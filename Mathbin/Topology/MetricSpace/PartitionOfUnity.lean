/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.metric_space.partition_of_unity
! leanprover-community/mathlib commit 50251fd6309cca5ca2e747882ffecd2729f38c5d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.EmetricParacompact
import Mathbin.Analysis.Convex.PartitionOfUnity

/-!
# Lemmas about (e)metric spaces that need partition of unity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The main lemma in this file (see `metric.exists_continuous_real_forall_closed_ball_subset`) says the
following. Let `X` be a metric space. Let `K : ι → set X` be a locally finite family of closed sets,
let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, → ℝ)` such that for any `i` and `x ∈ K i`, we have
`metric.closed_ball x (δ x) ⊆ U i`. We also formulate versions of this lemma for extended metric
spaces and for different codomains (`ℝ`, `ℝ≥0`, and `ℝ≥0∞`).

We also prove a few auxiliary lemmas to be used later in a proof of the smooth version of this
lemma.

## Tags

metric space, partition of unity, locally finite
-/


open Topology ENNReal BigOperators NNReal Filter

open Set Function Filter TopologicalSpace

variable {ι X : Type _}

namespace Emetric

variable [EMetricSpace X] {K : ι → Set X} {U : ι → Set X}

/- warning: emetric.eventually_nhds_zero_forall_closed_ball_subset -> EMetric.eventually_nhds_zero_forall_closedBall_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : EMetricSpace.{u2} X] {K : ι -> (Set.{u2} X)} {U : ι -> (Set.{u2} X)}, (forall (i : ι), IsClosed.{u2} X (UniformSpace.toTopologicalSpace.{u2} X (PseudoEMetricSpace.toUniformSpace.{u2} X (EMetricSpace.toPseudoEmetricSpace.{u2} X _inst_1))) (K i)) -> (forall (i : ι), IsOpen.{u2} X (UniformSpace.toTopologicalSpace.{u2} X (PseudoEMetricSpace.toUniformSpace.{u2} X (EMetricSpace.toPseudoEmetricSpace.{u2} X _inst_1))) (U i)) -> (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} X) (Set.hasSubset.{u2} X) (K i) (U i)) -> (LocallyFinite.{u1, u2} ι X (UniformSpace.toTopologicalSpace.{u2} X (PseudoEMetricSpace.toUniformSpace.{u2} X (EMetricSpace.toPseudoEmetricSpace.{u2} X _inst_1))) K) -> (forall (x : X), Filter.Eventually.{u2} (Prod.{0, u2} ENNReal X) (fun (p : Prod.{0, u2} ENNReal X) => forall (i : ι), (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) (Prod.snd.{0, u2} ENNReal X p) (K i)) -> (HasSubset.Subset.{u2} (Set.{u2} X) (Set.hasSubset.{u2} X) (EMetric.closedBall.{u2} X (EMetricSpace.toPseudoEmetricSpace.{u2} X _inst_1) (Prod.snd.{0, u2} ENNReal X p) (Prod.fst.{0, u2} ENNReal X p)) (U i))) (Filter.prod.{0, u2} ENNReal X (nhds.{0} ENNReal ENNReal.topologicalSpace (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (nhds.{u2} X (UniformSpace.toTopologicalSpace.{u2} X (PseudoEMetricSpace.toUniformSpace.{u2} X (EMetricSpace.toPseudoEmetricSpace.{u2} X _inst_1))) x)))
but is expected to have type
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : EMetricSpace.{u2} X] {K : ι -> (Set.{u2} X)} {U : ι -> (Set.{u2} X)}, (forall (i : ι), IsClosed.{u2} X (UniformSpace.toTopologicalSpace.{u2} X (PseudoEMetricSpace.toUniformSpace.{u2} X (EMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1))) (K i)) -> (forall (i : ι), IsOpen.{u2} X (UniformSpace.toTopologicalSpace.{u2} X (PseudoEMetricSpace.toUniformSpace.{u2} X (EMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1))) (U i)) -> (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) (K i) (U i)) -> (LocallyFinite.{u1, u2} ι X (UniformSpace.toTopologicalSpace.{u2} X (PseudoEMetricSpace.toUniformSpace.{u2} X (EMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1))) K) -> (forall (x : X), Filter.Eventually.{u2} (Prod.{0, u2} ENNReal X) (fun (p : Prod.{0, u2} ENNReal X) => forall (i : ι), (Membership.mem.{u2, u2} X (Set.{u2} X) (Set.instMembershipSet.{u2} X) (Prod.snd.{0, u2} ENNReal X p) (K i)) -> (HasSubset.Subset.{u2} (Set.{u2} X) (Set.instHasSubsetSet.{u2} X) (EMetric.closedBall.{u2} X (EMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1) (Prod.snd.{0, u2} ENNReal X p) (Prod.fst.{0, u2} ENNReal X p)) (U i))) (Filter.prod.{0, u2} ENNReal X (nhds.{0} ENNReal ENNReal.instTopologicalSpaceENNReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (nhds.{u2} X (UniformSpace.toTopologicalSpace.{u2} X (PseudoEMetricSpace.toUniformSpace.{u2} X (EMetricSpace.toPseudoEMetricSpace.{u2} X _inst_1))) x)))
Case conversion may be inaccurate. Consider using '#align emetric.eventually_nhds_zero_forall_closed_ball_subset EMetric.eventually_nhds_zero_forall_closedBall_subsetₓ'. -/
/-- Let `K : ι → set X` be a locally finitie family of closed sets in an emetric space. Let
`U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then for any point
`x : X`, for sufficiently small `r : ℝ≥0∞` and for `y` sufficiently close to `x`, for all `i`, if
`y ∈ K i`, then `emetric.closed_ball y r ⊆ U i`. -/
theorem eventually_nhds_zero_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) (x : X) :
    ∀ᶠ p : ℝ≥0∞ × X in 𝓝 0 ×ᶠ 𝓝 x, ∀ i, p.2 ∈ K i → closedBall p.2 p.1 ⊆ U i :=
  by
  suffices ∀ i, x ∈ K i → ∀ᶠ p : ℝ≥0∞ × X in 𝓝 0 ×ᶠ 𝓝 x, closed_ball p.2 p.1 ⊆ U i
    by
    filter_upwards [tendsto_snd (hfin.Inter_compl_mem_nhds hK x),
      (eventually_all_finite (hfin.point_finite x)).2 this]
    rintro ⟨r, y⟩ hxy hyU i hi
    simp only [mem_Inter₂, mem_compl_iff, not_imp_not, mem_preimage] at hxy
    exact hyU _ (hxy _ hi)
  intro i hi
  rcases nhds_basis_closed_eball.mem_iff.1 ((hU i).mem_nhds <| hKU i hi) with ⟨R, hR₀, hR⟩
  rcases ennreal.lt_iff_exists_nnreal_btwn.mp hR₀ with ⟨r, hr₀, hrR⟩
  filter_upwards [prod_mem_prod (eventually_lt_nhds hr₀)
      (closed_ball_mem_nhds x (tsub_pos_iff_lt.2 hrR))]with p hp z hz
  apply hR
  calc
    edist z x ≤ edist z p.2 + edist p.2 x := edist_triangle _ _ _
    _ ≤ p.1 + (R - p.1) := (add_le_add hz <| le_trans hp.2 <| tsub_le_tsub_left hp.1.out.le _)
    _ = R := add_tsub_cancel_of_le (lt_trans hp.1 hrR).le
    
#align emetric.eventually_nhds_zero_forall_closed_ball_subset EMetric.eventually_nhds_zero_forall_closedBall_subset

/- warning: emetric.exists_forall_closed_ball_subset_aux₁ -> EMetric.exists_forall_closedBall_subset_aux₁ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align emetric.exists_forall_closed_ball_subset_aux₁ EMetric.exists_forall_closedBall_subset_aux₁ₓ'. -/
theorem exists_forall_closedBall_subset_aux₁ (hK : ∀ i, IsClosed (K i)) (hU : ∀ i, IsOpen (U i))
    (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) (x : X) :
    ∃ r : ℝ,
      ∀ᶠ y in 𝓝 x,
        r ∈ Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' ⋂ (i) (hi : y ∈ K i), { r | closedBall y r ⊆ U i } :=
  by
  have :=
    (ennreal.continuous_of_real.tendsto' 0 0 ENNReal.ofReal_zero).Eventually
      (eventually_nhds_zero_forall_closed_ball_subset hK hU hKU hfin x).curry
  rcases this.exists_gt with ⟨r, hr0, hr⟩
  refine' ⟨r, hr.mono fun y hy => ⟨hr0, _⟩⟩
  rwa [mem_preimage, mem_Inter₂]
#align emetric.exists_forall_closed_ball_subset_aux₁ EMetric.exists_forall_closedBall_subset_aux₁

/- warning: emetric.exists_forall_closed_ball_subset_aux₂ -> EMetric.exists_forall_closedBall_subset_aux₂ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {X : Type.{u2}} [_inst_1 : EMetricSpace.{u2} X] {K : ι -> (Set.{u2} X)} {U : ι -> (Set.{u2} X)} (y : X), Convex.{0, 0} Real Real Real.orderedSemiring Real.addCommMonoid (Mul.toSMul.{0} Real Real.hasMul) (Inter.inter.{0} (Set.{0} Real) (Set.hasInter.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Set.preimage.{0, 0} Real ENNReal ENNReal.ofReal (Set.iInter.{0, succ u1} ENNReal ι (fun (i : ι) => Set.iInter.{0, 0} ENNReal (Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) y (K i)) (fun (hi : Membership.Mem.{u2, u2} X (Set.{u2} X) (Set.hasMem.{u2} X) y (K i)) => setOf.{0} ENNReal (fun (r : ENNReal) => HasSubset.Subset.{u2} (Set.{u2} X) (Set.hasSubset.{u2} X) (EMetric.closedBall.{u2} X (EMetricSpace.toPseudoEmetricSpace.{u2} X _inst_1) y r) (U i)))))))
but is expected to have type
  forall {ι : Type.{u2}} {X : Type.{u1}} [_inst_1 : EMetricSpace.{u1} X] {K : ι -> (Set.{u1} X)} {U : ι -> (Set.{u1} X)} (y : X), Convex.{0, 0} Real Real Real.orderedSemiring Real.instAddCommMonoidReal (Algebra.toSMul.{0, 0} Real Real Real.instCommSemiringReal Real.semiring (NormedAlgebra.toAlgebra.{0, 0} Real Real Real.normedField (SeminormedCommRing.toSeminormedRing.{0} Real (NormedCommRing.toSeminormedCommRing.{0} Real Real.normedCommRing)) (NormedAlgebra.id.{0} Real Real.normedField))) (Inter.inter.{0} (Set.{0} Real) (Set.instInterSet.{0} Real) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Set.preimage.{0, 0} Real ENNReal ENNReal.ofReal (Set.iInter.{0, succ u2} ENNReal ι (fun (i : ι) => Set.iInter.{0, 0} ENNReal (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) y (K i)) (fun (hi : Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) y (K i)) => setOf.{0} ENNReal (fun (r : ENNReal) => HasSubset.Subset.{u1} (Set.{u1} X) (Set.instHasSubsetSet.{u1} X) (EMetric.closedBall.{u1} X (EMetricSpace.toPseudoEMetricSpace.{u1} X _inst_1) y r) (U i)))))))
Case conversion may be inaccurate. Consider using '#align emetric.exists_forall_closed_ball_subset_aux₂ EMetric.exists_forall_closedBall_subset_aux₂ₓ'. -/
theorem exists_forall_closedBall_subset_aux₂ (y : X) :
    Convex ℝ
      (Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹' ⋂ (i) (hi : y ∈ K i), { r | closedBall y r ⊆ U i }) :=
  (convex_Ioi _).inter <|
    OrdConnected.convex <|
      OrdConnected.preimage_ennreal_ofReal <|
        ordConnected_iInter fun i =>
          ordConnected_iInter fun hi => ordConnected_setOf_closedBall_subset y (U i)
#align emetric.exists_forall_closed_ball_subset_aux₂ EMetric.exists_forall_closedBall_subset_aux₂

/- warning: emetric.exists_continuous_real_forall_closed_ball_subset -> EMetric.exists_continuous_real_forall_closedBall_subset is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align emetric.exists_continuous_real_forall_closed_ball_subset EMetric.exists_continuous_real_forall_closedBall_subsetₓ'. -/
/-- Let `X` be an extended metric space. Let `K : ι → set X` be a locally finite family of closed
sets, let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`,
we have `emetric.closed_ball x (ennreal.of_real (δ x)) ⊆ U i`. -/
theorem exists_continuous_real_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (ENNReal.ofReal <| δ x) ⊆ U i :=
  by
  simpa only [mem_inter_iff, forall_and, mem_preimage, mem_Inter, @forall_swap ι X] using
    exists_continuous_forall_mem_convex_of_local_const exists_forall_closed_ball_subset_aux₂
      (exists_forall_closed_ball_subset_aux₁ hK hU hKU hfin)
#align emetric.exists_continuous_real_forall_closed_ball_subset EMetric.exists_continuous_real_forall_closedBall_subset

/- warning: emetric.exists_continuous_nnreal_forall_closed_ball_subset -> EMetric.exists_continuous_nNReal_forall_closedBall_subset is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align emetric.exists_continuous_nnreal_forall_closed_ball_subset EMetric.exists_continuous_nNReal_forall_closedBall_subsetₓ'. -/
/-- Let `X` be an extended metric space. Let `K : ι → set X` be a locally finite family of closed
sets, let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ≥0)` such that for any `i` and `x ∈ K i`,
we have `emetric.closed_ball x (δ x) ⊆ U i`. -/
theorem exists_continuous_nNReal_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ≥0), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (δ x) ⊆ U i :=
  by
  rcases exists_continuous_real_forall_closed_ball_subset hK hU hKU hfin with ⟨δ, hδ₀, hδ⟩
  lift δ to C(X, ℝ≥0) using fun x => (hδ₀ x).le
  refine' ⟨δ, hδ₀, fun i x hi => _⟩
  simpa only [← ENNReal.ofReal_coe_nnreal] using hδ i x hi
#align emetric.exists_continuous_nnreal_forall_closed_ball_subset EMetric.exists_continuous_nNReal_forall_closedBall_subset

/- warning: emetric.exists_continuous_ennreal_forall_closed_ball_subset -> EMetric.exists_continuous_eNNReal_forall_closedBall_subset is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align emetric.exists_continuous_ennreal_forall_closed_ball_subset EMetric.exists_continuous_eNNReal_forall_closedBall_subsetₓ'. -/
/-- Let `X` be an extended metric space. Let `K : ι → set X` be a locally finite family of closed
sets, let `U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there
exists a positive continuous function `δ : C(X, ℝ≥0∞)` such that for any `i` and `x ∈ K i`,
we have `emetric.closed_ball x (δ x) ⊆ U i`. -/
theorem exists_continuous_eNNReal_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ≥0∞), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (δ x) ⊆ U i :=
  let ⟨δ, hδ₀, hδ⟩ := exists_continuous_nNReal_forall_closedBall_subset hK hU hKU hfin
  ⟨ContinuousMap.comp ⟨coe, ENNReal.continuous_coe⟩ δ, fun x => ENNReal.coe_pos.2 (hδ₀ x), hδ⟩
#align emetric.exists_continuous_ennreal_forall_closed_ball_subset EMetric.exists_continuous_eNNReal_forall_closedBall_subset

end Emetric

namespace Metric

variable [MetricSpace X] {K : ι → Set X} {U : ι → Set X}

/- warning: metric.exists_continuous_nnreal_forall_closed_ball_subset -> Metric.exists_continuous_nNReal_forall_closedBall_subset is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align metric.exists_continuous_nnreal_forall_closed_ball_subset Metric.exists_continuous_nNReal_forall_closedBall_subsetₓ'. -/
/-- Let `X` be a metric space. Let `K : ι → set X` be a locally finite family of closed sets, let
`U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, ℝ≥0)` such that for any `i` and `x ∈ K i`, we have
`metric.closed_ball x (δ x) ⊆ U i`. -/
theorem exists_continuous_nNReal_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ≥0), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (δ x) ⊆ U i :=
  by
  rcases EMetric.exists_continuous_nNReal_forall_closedBall_subset hK hU hKU hfin with ⟨δ, hδ0, hδ⟩
  refine' ⟨δ, hδ0, fun i x hx => _⟩
  rw [← emetric_closed_ball_nnreal]
  exact hδ i x hx
#align metric.exists_continuous_nnreal_forall_closed_ball_subset Metric.exists_continuous_nNReal_forall_closedBall_subset

/- warning: metric.exists_continuous_real_forall_closed_ball_subset -> Metric.exists_continuous_real_forall_closedBall_subset is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align metric.exists_continuous_real_forall_closed_ball_subset Metric.exists_continuous_real_forall_closedBall_subsetₓ'. -/
/-- Let `X` be a metric space. Let `K : ι → set X` be a locally finite family of closed sets, let
`U : ι → set X` be a family of open sets such that `K i ⊆ U i` for all `i`. Then there exists a
positive continuous function `δ : C(X, ℝ)` such that for any `i` and `x ∈ K i`, we have
`metric.closed_ball x (δ x) ⊆ U i`. -/
theorem exists_continuous_real_forall_closedBall_subset (hK : ∀ i, IsClosed (K i))
    (hU : ∀ i, IsOpen (U i)) (hKU : ∀ i, K i ⊆ U i) (hfin : LocallyFinite K) :
    ∃ δ : C(X, ℝ), (∀ x, 0 < δ x) ∧ ∀ (i), ∀ x ∈ K i, closedBall x (δ x) ⊆ U i :=
  let ⟨δ, hδ₀, hδ⟩ := exists_continuous_nNReal_forall_closedBall_subset hK hU hKU hfin
  ⟨ContinuousMap.comp ⟨coe, NNReal.continuous_coe⟩ δ, hδ₀, hδ⟩
#align metric.exists_continuous_real_forall_closed_ball_subset Metric.exists_continuous_real_forall_closedBall_subset

end Metric

