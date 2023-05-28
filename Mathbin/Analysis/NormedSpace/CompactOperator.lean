/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module analysis.normed_space.compact_operator
! leanprover-community/mathlib commit 781cb2eed038c4caf53bdbd8d20a95e5822d77df
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.LocallyConvex.Bounded
import Mathbin.Topology.Algebra.Module.StrongTopology

/-!
# Compact operators

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define compact linear operators between two topological vector spaces (TVS).

## Main definitions

* `is_compact_operator` : predicate for compact operators

## Main statements

* `is_compact_operator_iff_is_compact_closure_image_closed_ball` : the usual characterization of
  compact operators from a normed space to a T2 TVS.
* `is_compact_operator.comp_clm` : precomposing a compact operator by a continuous linear map gives
  a compact operator
* `is_compact_operator.clm_comp` : postcomposing a compact operator by a continuous linear map
  gives a compact operator
* `is_compact_operator.continuous` : compact operators are automatically continuous
* `is_closed_set_of_is_compact_operator` : the set of compact operators is closed for the operator
  norm

## Implementation details

We define `is_compact_operator` as a predicate, because the space of compact operators inherits all
of its structure from the space of continuous linear maps (e.g we want to have the usual operator
norm on compact operators).

The two natural options then would be to make it a predicate over linear maps or continuous linear
maps. Instead we define it as a predicate over bare functions, although it really only makes sense
for linear functions, because Lean is really good at finding coercions to bare functions (whereas
coercing from continuous linear maps to linear maps often needs type ascriptions).

## References

* Bourbaki, *Spectral Theory*, chapters 3 to 5, to be published (2022)

## Tags

Compact operator
-/


open Function Set Filter Bornology Metric

open Pointwise BigOperators Topology

#print IsCompactOperator /-
/-- A compact operator between two topological vector spaces. This definition is usually
given as "there exists a neighborhood of zero whose image is contained in a compact set",
but we choose a definition which involves fewer existential quantifiers and replaces images
with preimages.

We prove the equivalence in `is_compact_operator_iff_exists_mem_nhds_image_subset_compact`. -/
def IsCompactOperator {M₁ M₂ : Type _} [Zero M₁] [TopologicalSpace M₁] [TopologicalSpace M₂]
    (f : M₁ → M₂) : Prop :=
  ∃ K, IsCompact K ∧ f ⁻¹' K ∈ (𝓝 0 : Filter M₁)
#align is_compact_operator IsCompactOperator
-/

/- warning: is_compact_operator_zero -> isCompactOperator_zero is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Zero.{u1} M₁] [_inst_2 : TopologicalSpace.{u1} M₁] [_inst_3 : TopologicalSpace.{u2} M₂] [_inst_4 : Zero.{u2} M₂], IsCompactOperator.{u1, u2} M₁ M₂ _inst_1 _inst_2 _inst_3 (OfNat.ofNat.{max u1 u2} (M₁ -> M₂) 0 (OfNat.mk.{max u1 u2} (M₁ -> M₂) 0 (Zero.zero.{max u1 u2} (M₁ -> M₂) (Pi.instZero.{u1, u2} M₁ (fun (ᾰ : M₁) => M₂) (fun (i : M₁) => _inst_4)))))
but is expected to have type
  forall {M₁ : Type.{u2}} {M₂ : Type.{u1}} [_inst_1 : Zero.{u2} M₁] [_inst_2 : TopologicalSpace.{u2} M₁] [_inst_3 : TopologicalSpace.{u1} M₂] [_inst_4 : Zero.{u1} M₂], IsCompactOperator.{u2, u1} M₁ M₂ _inst_1 _inst_2 _inst_3 (OfNat.ofNat.{max u2 u1} (M₁ -> M₂) 0 (Zero.toOfNat0.{max u2 u1} (M₁ -> M₂) (Pi.instZero.{u2, u1} M₁ (fun (a._@.Mathlib.Analysis.NormedSpace.CompactOperator._hyg.67 : M₁) => M₂) (fun (i : M₁) => _inst_4))))
Case conversion may be inaccurate. Consider using '#align is_compact_operator_zero isCompactOperator_zeroₓ'. -/
theorem isCompactOperator_zero {M₁ M₂ : Type _} [Zero M₁] [TopologicalSpace M₁]
    [TopologicalSpace M₂] [Zero M₂] : IsCompactOperator (0 : M₁ → M₂) :=
  ⟨{0}, isCompact_singleton, mem_of_superset univ_mem fun x _ => rfl⟩
#align is_compact_operator_zero isCompactOperator_zero

section Characterizations

section

variable {R₁ R₂ : Type _} [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ M₂ : Type _}
  [TopologicalSpace M₁] [AddCommMonoid M₁] [TopologicalSpace M₂]

/- warning: is_compact_operator_iff_exists_mem_nhds_image_subset_compact -> isCompactOperator_iff_exists_mem_nhds_image_subset_compact is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_3 : TopologicalSpace.{u1} M₁] [_inst_4 : AddCommMonoid.{u1} M₁] [_inst_5 : TopologicalSpace.{u2} M₂] (f : M₁ -> M₂), Iff (IsCompactOperator.{u1, u2} M₁ M₂ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_4))) _inst_3 _inst_5 f) (Exists.{succ u1} (Set.{u1} M₁) (fun (V : Set.{u1} M₁) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} M₁) (Filter.{u1} M₁) (Filter.hasMem.{u1} M₁) V (nhds.{u1} M₁ _inst_3 (OfNat.ofNat.{u1} M₁ 0 (OfNat.mk.{u1} M₁ 0 (Zero.zero.{u1} M₁ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_4)))))))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} M₁) (Filter.{u1} M₁) (Filter.hasMem.{u1} M₁) V (nhds.{u1} M₁ _inst_3 (OfNat.ofNat.{u1} M₁ 0 (OfNat.mk.{u1} M₁ 0 (Zero.zero.{u1} M₁ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_4)))))))) => Exists.{succ u2} (Set.{u2} M₂) (fun (K : Set.{u2} M₂) => And (IsCompact.{u2} M₂ _inst_5 K) (HasSubset.Subset.{u2} (Set.{u2} M₂) (Set.hasSubset.{u2} M₂) (Set.image.{u1, u2} M₁ M₂ f V) K)))))
but is expected to have type
  forall {M₁ : Type.{u2}} {M₂ : Type.{u1}} [_inst_3 : TopologicalSpace.{u2} M₁] [_inst_4 : AddCommMonoid.{u2} M₁] [_inst_5 : TopologicalSpace.{u1} M₂] (f : M₁ -> M₂), Iff (IsCompactOperator.{u2, u1} M₁ M₂ (AddMonoid.toZero.{u2} M₁ (AddCommMonoid.toAddMonoid.{u2} M₁ _inst_4)) _inst_3 _inst_5 f) (Exists.{succ u2} (Set.{u2} M₁) (fun (V : Set.{u2} M₁) => And (Membership.mem.{u2, u2} (Set.{u2} M₁) (Filter.{u2} M₁) (instMembershipSetFilter.{u2} M₁) V (nhds.{u2} M₁ _inst_3 (OfNat.ofNat.{u2} M₁ 0 (Zero.toOfNat0.{u2} M₁ (AddMonoid.toZero.{u2} M₁ (AddCommMonoid.toAddMonoid.{u2} M₁ _inst_4)))))) (Exists.{succ u1} (Set.{u1} M₂) (fun (K : Set.{u1} M₂) => And (IsCompact.{u1} M₂ _inst_5 K) (HasSubset.Subset.{u1} (Set.{u1} M₂) (Set.instHasSubsetSet.{u1} M₂) (Set.image.{u2, u1} M₁ M₂ f V) K)))))
Case conversion may be inaccurate. Consider using '#align is_compact_operator_iff_exists_mem_nhds_image_subset_compact isCompactOperator_iff_exists_mem_nhds_image_subset_compactₓ'. -/
theorem isCompactOperator_iff_exists_mem_nhds_image_subset_compact (f : M₁ → M₂) :
    IsCompactOperator f ↔ ∃ V ∈ (𝓝 0 : Filter M₁), ∃ K : Set M₂, IsCompact K ∧ f '' V ⊆ K :=
  ⟨fun ⟨K, hK, hKf⟩ => ⟨f ⁻¹' K, hKf, K, hK, image_preimage_subset _ _⟩, fun ⟨V, hV, K, hK, hVK⟩ =>
    ⟨K, hK, mem_of_superset hV (image_subset_iff.mp hVK)⟩⟩
#align is_compact_operator_iff_exists_mem_nhds_image_subset_compact isCompactOperator_iff_exists_mem_nhds_image_subset_compact

/- warning: is_compact_operator_iff_exists_mem_nhds_is_compact_closure_image -> isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_3 : TopologicalSpace.{u1} M₁] [_inst_4 : AddCommMonoid.{u1} M₁] [_inst_5 : TopologicalSpace.{u2} M₂] [_inst_6 : T2Space.{u2} M₂ _inst_5] (f : M₁ -> M₂), Iff (IsCompactOperator.{u1, u2} M₁ M₂ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_4))) _inst_3 _inst_5 f) (Exists.{succ u1} (Set.{u1} M₁) (fun (V : Set.{u1} M₁) => Exists.{0} (Membership.Mem.{u1, u1} (Set.{u1} M₁) (Filter.{u1} M₁) (Filter.hasMem.{u1} M₁) V (nhds.{u1} M₁ _inst_3 (OfNat.ofNat.{u1} M₁ 0 (OfNat.mk.{u1} M₁ 0 (Zero.zero.{u1} M₁ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_4)))))))) (fun (H : Membership.Mem.{u1, u1} (Set.{u1} M₁) (Filter.{u1} M₁) (Filter.hasMem.{u1} M₁) V (nhds.{u1} M₁ _inst_3 (OfNat.ofNat.{u1} M₁ 0 (OfNat.mk.{u1} M₁ 0 (Zero.zero.{u1} M₁ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_4)))))))) => IsCompact.{u2} M₂ _inst_5 (closure.{u2} M₂ _inst_5 (Set.image.{u1, u2} M₁ M₂ f V)))))
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_3 : TopologicalSpace.{u1} M₁] [_inst_4 : AddCommMonoid.{u1} M₁] [_inst_5 : TopologicalSpace.{u2} M₂] [_inst_6 : T2Space.{u2} M₂ _inst_5] (f : M₁ -> M₂), Iff (IsCompactOperator.{u1, u2} M₁ M₂ (AddMonoid.toZero.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_4)) _inst_3 _inst_5 f) (Exists.{succ u1} (Set.{u1} M₁) (fun (V : Set.{u1} M₁) => And (Membership.mem.{u1, u1} (Set.{u1} M₁) (Filter.{u1} M₁) (instMembershipSetFilter.{u1} M₁) V (nhds.{u1} M₁ _inst_3 (OfNat.ofNat.{u1} M₁ 0 (Zero.toOfNat0.{u1} M₁ (AddMonoid.toZero.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_4)))))) (IsCompact.{u2} M₂ _inst_5 (closure.{u2} M₂ _inst_5 (Set.image.{u1, u2} M₁ M₂ f V)))))
Case conversion may be inaccurate. Consider using '#align is_compact_operator_iff_exists_mem_nhds_is_compact_closure_image isCompactOperator_iff_exists_mem_nhds_isCompact_closure_imageₓ'. -/
theorem isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image [T2Space M₂] (f : M₁ → M₂) :
    IsCompactOperator f ↔ ∃ V ∈ (𝓝 0 : Filter M₁), IsCompact (closure <| f '' V) :=
  by
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  exact
    ⟨fun ⟨V, hV, K, hK, hKV⟩ => ⟨V, hV, isCompact_closure_of_subset_compact hK hKV⟩,
      fun ⟨V, hV, hVc⟩ => ⟨V, hV, closure (f '' V), hVc, subset_closure⟩⟩
#align is_compact_operator_iff_exists_mem_nhds_is_compact_closure_image isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image

end

section Bounded

variable {𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁] [SeminormedRing 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
  {M₁ M₂ : Type _} [TopologicalSpace M₁] [AddCommMonoid M₁] [TopologicalSpace M₂] [AddCommMonoid M₂]
  [Module 𝕜₁ M₁] [Module 𝕜₂ M₂] [ContinuousConstSMul 𝕜₂ M₂]

/- warning: is_compact_operator.image_subset_compact_of_vonN_bounded -> IsCompactOperator.image_subset_compact_of_isVonNBounded is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.image_subset_compact_of_vonN_bounded IsCompactOperator.image_subset_compact_of_isVonNBoundedₓ'. -/
theorem IsCompactOperator.image_subset_compact_of_isVonNBounded {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁ S) :
    ∃ K : Set M₂, IsCompact K ∧ f '' S ⊆ K :=
  let ⟨K, hK, hKf⟩ := hf
  let ⟨r, hr, hrS⟩ := hS hKf
  let ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜₁ r
  let this := ne_zero_of_norm_ne_zero (hr.trans hc).Ne.symm
  ⟨σ₁₂ c • K, hK.image <| continuous_id.const_smul (σ₁₂ c), by
    rw [image_subset_iff, preimage_smul_setₛₗ _ _ _ f this.is_unit] <;> exact hrS c hc.le⟩
#align is_compact_operator.image_subset_compact_of_vonN_bounded IsCompactOperator.image_subset_compact_of_isVonNBounded

/- warning: is_compact_operator.is_compact_closure_image_of_vonN_bounded -> IsCompactOperator.isCompact_closure_image_of_isVonNBounded is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.is_compact_closure_image_of_vonN_bounded IsCompactOperator.isCompact_closure_image_of_isVonNBoundedₓ'. -/
theorem IsCompactOperator.isCompact_closure_image_of_isVonNBounded [T2Space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁ S) :
    IsCompact (closure <| f '' S) :=
  let ⟨K, hK, hKf⟩ := hf.image_subset_compact_of_isVonNBounded hS
  isCompact_closure_of_subset_compact hK hKf
#align is_compact_operator.is_compact_closure_image_of_vonN_bounded IsCompactOperator.isCompact_closure_image_of_isVonNBounded

end Bounded

section NormedSpace

variable {𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁] [SeminormedRing 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
  {M₁ M₂ M₃ : Type _} [SeminormedAddCommGroup M₁] [TopologicalSpace M₂] [AddCommMonoid M₂]
  [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂]

/- warning: is_compact_operator.image_subset_compact_of_bounded -> IsCompactOperator.image_subset_compact_of_bounded is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.image_subset_compact_of_bounded IsCompactOperator.image_subset_compact_of_boundedₓ'. -/
theorem IsCompactOperator.image_subset_compact_of_bounded [ContinuousConstSMul 𝕜₂ M₂]
    {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) {S : Set M₁} (hS : Metric.Bounded S) :
    ∃ K : Set M₂, IsCompact K ∧ f '' S ⊆ K :=
  hf.image_subset_compact_of_isVonNBounded
    (by rwa [NormedSpace.isVonNBounded_iff, ← Metric.bounded_iff_isBounded])
#align is_compact_operator.image_subset_compact_of_bounded IsCompactOperator.image_subset_compact_of_bounded

/- warning: is_compact_operator.is_compact_closure_image_of_bounded -> IsCompactOperator.isCompact_closure_image_of_bounded is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.is_compact_closure_image_of_bounded IsCompactOperator.isCompact_closure_image_of_boundedₓ'. -/
theorem IsCompactOperator.isCompact_closure_image_of_bounded [ContinuousConstSMul 𝕜₂ M₂]
    [T2Space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) {S : Set M₁}
    (hS : Metric.Bounded S) : IsCompact (closure <| f '' S) :=
  hf.isCompact_closure_image_of_isVonNBounded
    (by rwa [NormedSpace.isVonNBounded_iff, ← Metric.bounded_iff_isBounded])
#align is_compact_operator.is_compact_closure_image_of_bounded IsCompactOperator.isCompact_closure_image_of_bounded

/- warning: is_compact_operator.image_ball_subset_compact -> IsCompactOperator.image_ball_subset_compact is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.image_ball_subset_compact IsCompactOperator.image_ball_subset_compactₓ'. -/
theorem IsCompactOperator.image_ball_subset_compact [ContinuousConstSMul 𝕜₂ M₂] {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) (r : ℝ) : ∃ K : Set M₂, IsCompact K ∧ f '' Metric.ball 0 r ⊆ K :=
  hf.image_subset_compact_of_isVonNBounded (NormedSpace.isVonNBounded_ball 𝕜₁ M₁ r)
#align is_compact_operator.image_ball_subset_compact IsCompactOperator.image_ball_subset_compact

/- warning: is_compact_operator.image_closed_ball_subset_compact -> IsCompactOperator.image_closedBall_subset_compact is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.image_closed_ball_subset_compact IsCompactOperator.image_closedBall_subset_compactₓ'. -/
theorem IsCompactOperator.image_closedBall_subset_compact [ContinuousConstSMul 𝕜₂ M₂]
    {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : ℝ) :
    ∃ K : Set M₂, IsCompact K ∧ f '' Metric.closedBall 0 r ⊆ K :=
  hf.image_subset_compact_of_isVonNBounded (NormedSpace.isVonNBounded_closedBall 𝕜₁ M₁ r)
#align is_compact_operator.image_closed_ball_subset_compact IsCompactOperator.image_closedBall_subset_compact

/- warning: is_compact_operator.is_compact_closure_image_ball -> IsCompactOperator.isCompact_closure_image_ball is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.is_compact_closure_image_ball IsCompactOperator.isCompact_closure_image_ballₓ'. -/
theorem IsCompactOperator.isCompact_closure_image_ball [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂]
    {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : ℝ) :
    IsCompact (closure <| f '' Metric.ball 0 r) :=
  hf.isCompact_closure_image_of_isVonNBounded (NormedSpace.isVonNBounded_ball 𝕜₁ M₁ r)
#align is_compact_operator.is_compact_closure_image_ball IsCompactOperator.isCompact_closure_image_ball

/- warning: is_compact_operator.is_compact_closure_image_closed_ball -> IsCompactOperator.isCompact_closure_image_closedBall is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.is_compact_closure_image_closed_ball IsCompactOperator.isCompact_closure_image_closedBallₓ'. -/
theorem IsCompactOperator.isCompact_closure_image_closedBall [ContinuousConstSMul 𝕜₂ M₂]
    [T2Space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : ℝ) :
    IsCompact (closure <| f '' Metric.closedBall 0 r) :=
  hf.isCompact_closure_image_of_isVonNBounded (NormedSpace.isVonNBounded_closedBall 𝕜₁ M₁ r)
#align is_compact_operator.is_compact_closure_image_closed_ball IsCompactOperator.isCompact_closure_image_closedBall

/- warning: is_compact_operator_iff_image_ball_subset_compact -> isCompactOperator_iff_image_ball_subset_compact is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator_iff_image_ball_subset_compact isCompactOperator_iff_image_ball_subset_compactₓ'. -/
theorem isCompactOperator_iff_image_ball_subset_compact [ContinuousConstSMul 𝕜₂ M₂]
    (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ ∃ K : Set M₂, IsCompact K ∧ f '' Metric.ball 0 r ⊆ K :=
  ⟨fun hf => hf.image_ball_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.ball 0 r, ball_mem_nhds _ hr, K, hK, hKr⟩⟩
#align is_compact_operator_iff_image_ball_subset_compact isCompactOperator_iff_image_ball_subset_compact

/- warning: is_compact_operator_iff_image_closed_ball_subset_compact -> isCompactOperator_iff_image_closedBall_subset_compact is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator_iff_image_closed_ball_subset_compact isCompactOperator_iff_image_closedBall_subset_compactₓ'. -/
theorem isCompactOperator_iff_image_closedBall_subset_compact [ContinuousConstSMul 𝕜₂ M₂]
    (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ ∃ K : Set M₂, IsCompact K ∧ f '' Metric.closedBall 0 r ⊆ K :=
  ⟨fun hf => hf.image_closedBall_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.closedBall 0 r, closedBall_mem_nhds _ hr, K, hK, hKr⟩⟩
#align is_compact_operator_iff_image_closed_ball_subset_compact isCompactOperator_iff_image_closedBall_subset_compact

/- warning: is_compact_operator_iff_is_compact_closure_image_ball -> isCompactOperator_iff_isCompact_closure_image_ball is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator_iff_is_compact_closure_image_ball isCompactOperator_iff_isCompact_closure_image_ballₓ'. -/
theorem isCompactOperator_iff_isCompact_closure_image_ball [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂]
    (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ IsCompact (closure <| f '' Metric.ball 0 r) :=
  ⟨fun hf => hf.isCompact_closure_image_ball r, fun hf =>
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image f).mpr
      ⟨Metric.ball 0 r, ball_mem_nhds _ hr, hf⟩⟩
#align is_compact_operator_iff_is_compact_closure_image_ball isCompactOperator_iff_isCompact_closure_image_ball

/- warning: is_compact_operator_iff_is_compact_closure_image_closed_ball -> isCompactOperator_iff_isCompact_closure_image_closedBall is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator_iff_is_compact_closure_image_closed_ball isCompactOperator_iff_isCompact_closure_image_closedBallₓ'. -/
theorem isCompactOperator_iff_isCompact_closure_image_closedBall [ContinuousConstSMul 𝕜₂ M₂]
    [T2Space M₂] (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ IsCompact (closure <| f '' Metric.closedBall 0 r) :=
  ⟨fun hf => hf.isCompact_closure_image_closedBall r, fun hf =>
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image f).mpr
      ⟨Metric.closedBall 0 r, closedBall_mem_nhds _ hr, hf⟩⟩
#align is_compact_operator_iff_is_compact_closure_image_closed_ball isCompactOperator_iff_isCompact_closure_image_closedBall

end NormedSpace

end Characterizations

section Operations

variable {R₁ R₂ R₃ R₄ : Type _} [Semiring R₁] [Semiring R₂] [CommSemiring R₃] [CommSemiring R₄]
  {σ₁₂ : R₁ →+* R₂} {σ₁₄ : R₁ →+* R₄} {σ₃₄ : R₃ →+* R₄} {M₁ M₂ M₃ M₄ : Type _} [TopologicalSpace M₁]
  [AddCommMonoid M₁] [TopologicalSpace M₂] [AddCommMonoid M₂] [TopologicalSpace M₃]
  [AddCommGroup M₃] [TopologicalSpace M₄] [AddCommGroup M₄]

/- warning: is_compact_operator.smul -> IsCompactOperator.smul is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_5 : TopologicalSpace.{u1} M₁] [_inst_6 : AddCommMonoid.{u1} M₁] [_inst_7 : TopologicalSpace.{u2} M₂] [_inst_8 : AddCommMonoid.{u2} M₂] {S : Type.{u3}} [_inst_13 : Monoid.{u3} S] [_inst_14 : DistribMulAction.{u3, u2} S M₂ _inst_13 (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8)] [_inst_15 : ContinuousConstSMul.{u3, u2} S M₂ _inst_7 (SMulZeroClass.toHasSmul.{u3, u2} S M₂ (AddZeroClass.toHasZero.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8))) (DistribSMul.toSmulZeroClass.{u3, u2} S M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8)) (DistribMulAction.toDistribSMul.{u3, u2} S M₂ _inst_13 (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8) _inst_14)))] {f : M₁ -> M₂}, (IsCompactOperator.{u1, u2} M₁ M₂ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6))) _inst_5 _inst_7 f) -> (forall (c : S), IsCompactOperator.{u1, u2} M₁ M₂ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6))) _inst_5 _inst_7 (SMul.smul.{u3, max u1 u2} S (M₁ -> M₂) (Function.hasSMul.{u1, u3, u2} M₁ S M₂ (SMulZeroClass.toHasSmul.{u3, u2} S M₂ (AddZeroClass.toHasZero.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8))) (DistribSMul.toSmulZeroClass.{u3, u2} S M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8)) (DistribMulAction.toDistribSMul.{u3, u2} S M₂ _inst_13 (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8) _inst_14)))) c f))
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_5 : TopologicalSpace.{u1} M₁] [_inst_6 : AddCommMonoid.{u1} M₁] [_inst_7 : TopologicalSpace.{u2} M₂] [_inst_8 : AddCommMonoid.{u2} M₂] {S : Type.{u3}} [_inst_13 : Monoid.{u3} S] [_inst_14 : DistribMulAction.{u3, u2} S M₂ _inst_13 (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8)] [_inst_15 : ContinuousConstSMul.{u3, u2} S M₂ _inst_7 (SMulZeroClass.toSMul.{u3, u2} S M₂ (AddMonoid.toZero.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8)) (DistribSMul.toSMulZeroClass.{u3, u2} S M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8)) (DistribMulAction.toDistribSMul.{u3, u2} S M₂ _inst_13 (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8) _inst_14)))] {f : M₁ -> M₂}, (IsCompactOperator.{u1, u2} M₁ M₂ (AddMonoid.toZero.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6)) _inst_5 _inst_7 f) -> (forall (c : S), IsCompactOperator.{u1, u2} M₁ M₂ (AddMonoid.toZero.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6)) _inst_5 _inst_7 (HSMul.hSMul.{u3, max u1 u2, max u1 u2} S (M₁ -> M₂) (M₁ -> M₂) (instHSMul.{u3, max u1 u2} S (M₁ -> M₂) (Pi.instSMul.{u1, u2, u3} M₁ S (fun (a._@.Mathlib.Analysis.NormedSpace.CompactOperator._hyg.2184 : M₁) => M₂) (fun (i : M₁) => SMulZeroClass.toSMul.{u3, u2} S M₂ (AddMonoid.toZero.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8)) (DistribSMul.toSMulZeroClass.{u3, u2} S M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8)) (DistribMulAction.toDistribSMul.{u3, u2} S M₂ _inst_13 (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8) _inst_14))))) c f))
Case conversion may be inaccurate. Consider using '#align is_compact_operator.smul IsCompactOperator.smulₓ'. -/
theorem IsCompactOperator.smul {S : Type _} [Monoid S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ → M₂} (hf : IsCompactOperator f) (c : S) :
    IsCompactOperator (c • f) :=
  let ⟨K, hK, hKf⟩ := hf
  ⟨c • K, hK.image <| continuous_id.const_smul c,
    mem_of_superset hKf fun x hx => smul_mem_smul_set hx⟩
#align is_compact_operator.smul IsCompactOperator.smul

/- warning: is_compact_operator.add -> IsCompactOperator.add is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_5 : TopologicalSpace.{u1} M₁] [_inst_6 : AddCommMonoid.{u1} M₁] [_inst_7 : TopologicalSpace.{u2} M₂] [_inst_8 : AddCommMonoid.{u2} M₂] [_inst_13 : ContinuousAdd.{u2} M₂ _inst_7 (AddZeroClass.toHasAdd.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8)))] {f : M₁ -> M₂} {g : M₁ -> M₂}, (IsCompactOperator.{u1, u2} M₁ M₂ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6))) _inst_5 _inst_7 f) -> (IsCompactOperator.{u1, u2} M₁ M₂ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6))) _inst_5 _inst_7 g) -> (IsCompactOperator.{u1, u2} M₁ M₂ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6))) _inst_5 _inst_7 (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (M₁ -> M₂) (M₁ -> M₂) (M₁ -> M₂) (instHAdd.{max u1 u2} (M₁ -> M₂) (Pi.instAdd.{u1, u2} M₁ (fun (ᾰ : M₁) => M₂) (fun (i : M₁) => AddZeroClass.toHasAdd.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8))))) f g))
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_5 : TopologicalSpace.{u1} M₁] [_inst_6 : AddCommMonoid.{u1} M₁] [_inst_7 : TopologicalSpace.{u2} M₂] [_inst_8 : AddCommMonoid.{u2} M₂] [_inst_13 : ContinuousAdd.{u2} M₂ _inst_7 (AddZeroClass.toAdd.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8)))] {f : M₁ -> M₂} {g : M₁ -> M₂}, (IsCompactOperator.{u1, u2} M₁ M₂ (AddMonoid.toZero.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6)) _inst_5 _inst_7 f) -> (IsCompactOperator.{u1, u2} M₁ M₂ (AddMonoid.toZero.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6)) _inst_5 _inst_7 g) -> (IsCompactOperator.{u1, u2} M₁ M₂ (AddMonoid.toZero.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6)) _inst_5 _inst_7 (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (M₁ -> M₂) (M₁ -> M₂) (M₁ -> M₂) (instHAdd.{max u1 u2} (M₁ -> M₂) (Pi.instAdd.{u1, u2} M₁ (fun (ᾰ : M₁) => M₂) (fun (i : M₁) => AddZeroClass.toAdd.{u2} M₂ (AddMonoid.toAddZeroClass.{u2} M₂ (AddCommMonoid.toAddMonoid.{u2} M₂ _inst_8))))) f g))
Case conversion may be inaccurate. Consider using '#align is_compact_operator.add IsCompactOperator.addₓ'. -/
theorem IsCompactOperator.add [ContinuousAdd M₂] {f g : M₁ → M₂} (hf : IsCompactOperator f)
    (hg : IsCompactOperator g) : IsCompactOperator (f + g) :=
  let ⟨A, hA, hAf⟩ := hf
  let ⟨B, hB, hBg⟩ := hg
  ⟨A + B, hA.add hB,
    mem_of_superset (inter_mem hAf hBg) fun x ⟨hxA, hxB⟩ => Set.add_mem_add hxA hxB⟩
#align is_compact_operator.add IsCompactOperator.add

/- warning: is_compact_operator.neg -> IsCompactOperator.neg is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₄ : Type.{u2}} [_inst_5 : TopologicalSpace.{u1} M₁] [_inst_6 : AddCommMonoid.{u1} M₁] [_inst_11 : TopologicalSpace.{u2} M₄] [_inst_12 : AddCommGroup.{u2} M₄] [_inst_13 : ContinuousNeg.{u2} M₄ _inst_11 (SubNegMonoid.toHasNeg.{u2} M₄ (AddGroup.toSubNegMonoid.{u2} M₄ (AddCommGroup.toAddGroup.{u2} M₄ _inst_12)))] {f : M₁ -> M₄}, (IsCompactOperator.{u1, u2} M₁ M₄ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6))) _inst_5 _inst_11 f) -> (IsCompactOperator.{u1, u2} M₁ M₄ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6))) _inst_5 _inst_11 (Neg.neg.{max u1 u2} (M₁ -> M₄) (Pi.instNeg.{u1, u2} M₁ (fun (ᾰ : M₁) => M₄) (fun (i : M₁) => SubNegMonoid.toHasNeg.{u2} M₄ (AddGroup.toSubNegMonoid.{u2} M₄ (AddCommGroup.toAddGroup.{u2} M₄ _inst_12)))) f))
but is expected to have type
  forall {M₁ : Type.{u1}} {M₄ : Type.{u2}} [_inst_5 : TopologicalSpace.{u1} M₁] [_inst_6 : AddCommMonoid.{u1} M₁] [_inst_11 : TopologicalSpace.{u2} M₄] [_inst_12 : AddCommGroup.{u2} M₄] [_inst_13 : ContinuousNeg.{u2} M₄ _inst_11 (NegZeroClass.toNeg.{u2} M₄ (SubNegZeroMonoid.toNegZeroClass.{u2} M₄ (SubtractionMonoid.toSubNegZeroMonoid.{u2} M₄ (SubtractionCommMonoid.toSubtractionMonoid.{u2} M₄ (AddCommGroup.toDivisionAddCommMonoid.{u2} M₄ _inst_12)))))] {f : M₁ -> M₄}, (IsCompactOperator.{u1, u2} M₁ M₄ (AddMonoid.toZero.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6)) _inst_5 _inst_11 f) -> (IsCompactOperator.{u1, u2} M₁ M₄ (AddMonoid.toZero.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6)) _inst_5 _inst_11 (Neg.neg.{max u1 u2} (M₁ -> M₄) (Pi.instNeg.{u1, u2} M₁ (fun (ᾰ : M₁) => M₄) (fun (i : M₁) => NegZeroClass.toNeg.{u2} M₄ (SubNegZeroMonoid.toNegZeroClass.{u2} M₄ (SubtractionMonoid.toSubNegZeroMonoid.{u2} M₄ (SubtractionCommMonoid.toSubtractionMonoid.{u2} M₄ (AddCommGroup.toDivisionAddCommMonoid.{u2} M₄ _inst_12)))))) f))
Case conversion may be inaccurate. Consider using '#align is_compact_operator.neg IsCompactOperator.negₓ'. -/
theorem IsCompactOperator.neg [ContinuousNeg M₄] {f : M₁ → M₄} (hf : IsCompactOperator f) :
    IsCompactOperator (-f) :=
  let ⟨K, hK, hKf⟩ := hf
  ⟨-K, hK.neg, mem_of_superset hKf fun x (hx : f x ∈ K) => Set.neg_mem_neg.mpr hx⟩
#align is_compact_operator.neg IsCompactOperator.neg

/- warning: is_compact_operator.sub -> IsCompactOperator.sub is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₄ : Type.{u2}} [_inst_5 : TopologicalSpace.{u1} M₁] [_inst_6 : AddCommMonoid.{u1} M₁] [_inst_11 : TopologicalSpace.{u2} M₄] [_inst_12 : AddCommGroup.{u2} M₄] [_inst_13 : TopologicalAddGroup.{u2} M₄ _inst_11 (AddCommGroup.toAddGroup.{u2} M₄ _inst_12)] {f : M₁ -> M₄} {g : M₁ -> M₄}, (IsCompactOperator.{u1, u2} M₁ M₄ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6))) _inst_5 _inst_11 f) -> (IsCompactOperator.{u1, u2} M₁ M₄ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6))) _inst_5 _inst_11 g) -> (IsCompactOperator.{u1, u2} M₁ M₄ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6))) _inst_5 _inst_11 (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (M₁ -> M₄) (M₁ -> M₄) (M₁ -> M₄) (instHSub.{max u1 u2} (M₁ -> M₄) (Pi.instSub.{u1, u2} M₁ (fun (ᾰ : M₁) => M₄) (fun (i : M₁) => SubNegMonoid.toHasSub.{u2} M₄ (AddGroup.toSubNegMonoid.{u2} M₄ (AddCommGroup.toAddGroup.{u2} M₄ _inst_12))))) f g))
but is expected to have type
  forall {M₁ : Type.{u1}} {M₄ : Type.{u2}} [_inst_5 : TopologicalSpace.{u1} M₁] [_inst_6 : AddCommMonoid.{u1} M₁] [_inst_11 : TopologicalSpace.{u2} M₄] [_inst_12 : AddCommGroup.{u2} M₄] [_inst_13 : TopologicalAddGroup.{u2} M₄ _inst_11 (AddCommGroup.toAddGroup.{u2} M₄ _inst_12)] {f : M₁ -> M₄} {g : M₁ -> M₄}, (IsCompactOperator.{u1, u2} M₁ M₄ (AddMonoid.toZero.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6)) _inst_5 _inst_11 f) -> (IsCompactOperator.{u1, u2} M₁ M₄ (AddMonoid.toZero.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6)) _inst_5 _inst_11 g) -> (IsCompactOperator.{u1, u2} M₁ M₄ (AddMonoid.toZero.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_6)) _inst_5 _inst_11 (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (M₁ -> M₄) (M₁ -> M₄) (M₁ -> M₄) (instHSub.{max u1 u2} (M₁ -> M₄) (Pi.instSub.{u1, u2} M₁ (fun (ᾰ : M₁) => M₄) (fun (i : M₁) => SubNegMonoid.toSub.{u2} M₄ (AddGroup.toSubNegMonoid.{u2} M₄ (AddCommGroup.toAddGroup.{u2} M₄ _inst_12))))) f g))
Case conversion may be inaccurate. Consider using '#align is_compact_operator.sub IsCompactOperator.subₓ'. -/
theorem IsCompactOperator.sub [TopologicalAddGroup M₄] {f g : M₁ → M₄} (hf : IsCompactOperator f)
    (hg : IsCompactOperator g) : IsCompactOperator (f - g) := by
  rw [sub_eq_add_neg] <;> exact hf.add hg.neg
#align is_compact_operator.sub IsCompactOperator.sub

variable (σ₁₄ M₁ M₄)

#print compactOperator /-
/-- The submodule of compact continuous linear maps. -/
def compactOperator [Module R₁ M₁] [Module R₄ M₄] [ContinuousConstSMul R₄ M₄]
    [TopologicalAddGroup M₄] : Submodule R₄ (M₁ →SL[σ₁₄] M₄)
    where
  carrier := { f | IsCompactOperator f }
  add_mem' f g hf hg := hf.add hg
  zero_mem' := isCompactOperator_zero
  smul_mem' c f hf := hf.smul c
#align compact_operator compactOperator
-/

end Operations

section Comp

variable {R₁ R₂ R₃ : Type _} [Semiring R₁] [Semiring R₂] [Semiring R₃] {σ₁₂ : R₁ →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {M₁ M₂ M₃ : Type _} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₁] [Module R₁ M₁]

/- warning: is_compact_operator.comp_clm -> IsCompactOperator.comp_clm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.comp_clm IsCompactOperator.comp_clmₓ'. -/
theorem IsCompactOperator.comp_clm [AddCommMonoid M₂] [Module R₂ M₂] {f : M₂ → M₃}
    (hf : IsCompactOperator f) (g : M₁ →SL[σ₁₂] M₂) : IsCompactOperator (f ∘ g) :=
  by
  have := g.continuous.tendsto 0
  rw [map_zero] at this
  rcases hf with ⟨K, hK, hKf⟩
  exact ⟨K, hK, this hKf⟩
#align is_compact_operator.comp_clm IsCompactOperator.comp_clm

/- warning: is_compact_operator.continuous_comp -> IsCompactOperator.continuous_comp is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} {M₃ : Type.{u3}} [_inst_4 : TopologicalSpace.{u1} M₁] [_inst_5 : TopologicalSpace.{u2} M₂] [_inst_6 : TopologicalSpace.{u3} M₃] [_inst_7 : AddCommMonoid.{u1} M₁] {f : M₁ -> M₂}, (IsCompactOperator.{u1, u2} M₁ M₂ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_7))) _inst_4 _inst_5 f) -> (forall {g : M₂ -> M₃}, (Continuous.{u2, u3} M₂ M₃ _inst_5 _inst_6 g) -> (IsCompactOperator.{u1, u3} M₁ M₃ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddCommMonoid.toAddMonoid.{u1} M₁ _inst_7))) _inst_4 _inst_6 (Function.comp.{succ u1, succ u2, succ u3} M₁ M₂ M₃ g f)))
but is expected to have type
  forall {M₁ : Type.{u3}} {M₂ : Type.{u2}} {M₃ : Type.{u1}} [_inst_4 : TopologicalSpace.{u3} M₁] [_inst_5 : TopologicalSpace.{u2} M₂] [_inst_6 : TopologicalSpace.{u1} M₃] [_inst_7 : AddCommMonoid.{u3} M₁] {f : M₁ -> M₂}, (IsCompactOperator.{u3, u2} M₁ M₂ (AddMonoid.toZero.{u3} M₁ (AddCommMonoid.toAddMonoid.{u3} M₁ _inst_7)) _inst_4 _inst_5 f) -> (forall {g : M₂ -> M₃}, (Continuous.{u2, u1} M₂ M₃ _inst_5 _inst_6 g) -> (IsCompactOperator.{u3, u1} M₁ M₃ (AddMonoid.toZero.{u3} M₁ (AddCommMonoid.toAddMonoid.{u3} M₁ _inst_7)) _inst_4 _inst_6 (Function.comp.{succ u3, succ u2, succ u1} M₁ M₂ M₃ g f)))
Case conversion may be inaccurate. Consider using '#align is_compact_operator.continuous_comp IsCompactOperator.continuous_compₓ'. -/
theorem IsCompactOperator.continuous_comp {f : M₁ → M₂} (hf : IsCompactOperator f) {g : M₂ → M₃}
    (hg : Continuous g) : IsCompactOperator (g ∘ f) :=
  by
  rcases hf with ⟨K, hK, hKf⟩
  refine' ⟨g '' K, hK.image hg, mem_of_superset hKf _⟩
  nth_rw 2 [preimage_comp]
  exact preimage_mono (subset_preimage_image _ _)
#align is_compact_operator.continuous_comp IsCompactOperator.continuous_comp

/- warning: is_compact_operator.clm_comp -> IsCompactOperator.clm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.clm_comp IsCompactOperator.clm_compₓ'. -/
theorem IsCompactOperator.clm_comp [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid M₃]
    [Module R₃ M₃] {f : M₁ → M₂} (hf : IsCompactOperator f) (g : M₂ →SL[σ₂₃] M₃) :
    IsCompactOperator (g ∘ f) :=
  hf.continuous_comp g.Continuous
#align is_compact_operator.clm_comp IsCompactOperator.clm_comp

end Comp

section CodRestrict

variable {R₁ R₂ : Type _} [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ M₂ : Type _}
  [TopologicalSpace M₁] [TopologicalSpace M₂] [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R₁ M₁]
  [Module R₂ M₂]

/- warning: is_compact_operator.cod_restrict -> IsCompactOperator.codRestrict is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.cod_restrict IsCompactOperator.codRestrictₓ'. -/
theorem IsCompactOperator.codRestrict {f : M₁ → M₂} (hf : IsCompactOperator f) {V : Submodule R₂ M₂}
    (hV : ∀ x, f x ∈ V) (h_closed : IsClosed (V : Set M₂)) :
    IsCompactOperator (Set.codRestrict f V hV) :=
  let ⟨K, hK, hKf⟩ := hf
  ⟨coe ⁻¹' K, (closedEmbedding_subtype_val h_closed).isCompact_preimage hK, hKf⟩
#align is_compact_operator.cod_restrict IsCompactOperator.codRestrict

end CodRestrict

section Restrict

variable {R₁ R₂ R₃ : Type _} [Semiring R₁] [Semiring R₂] [Semiring R₃] {σ₁₂ : R₁ →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {M₁ M₂ M₃ : Type _} [TopologicalSpace M₁] [UniformSpace M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [Module R₁ M₁]
  [Module R₂ M₂] [Module R₃ M₃]

/- warning: is_compact_operator.restrict -> IsCompactOperator.restrict is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.restrict IsCompactOperator.restrictₓ'. -/
/-- If a compact operator preserves a closed submodule, its restriction to that submodule is
compact.

Note that, following mathlib's convention in linear algebra, `restrict` designates the restriction
of an endomorphism `f : E →ₗ E` to an endomorphism `f' : ↥V →ₗ ↥V`. To prove that the restriction
`f' : ↥U →ₛₗ ↥V` of a compact operator `f : E →ₛₗ F` is compact, apply
`is_compact_operator.cod_restrict` to `f ∘ U.subtypeL`, which is compact by
`is_compact_operator.comp_clm`. -/
theorem IsCompactOperator.restrict {f : M₁ →ₗ[R₁] M₁} (hf : IsCompactOperator f)
    {V : Submodule R₁ M₁} (hV : ∀ v ∈ V, f v ∈ V) (h_closed : IsClosed (V : Set M₁)) :
    IsCompactOperator (f.restrict hV) :=
  (hf.comp_clm V.subtypeL).codRestrict (SetLike.forall.2 hV) h_closed
#align is_compact_operator.restrict IsCompactOperator.restrict

/- warning: is_compact_operator.restrict' -> IsCompactOperator.restrict' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.restrict' IsCompactOperator.restrict'ₓ'. -/
/-- If a compact operator preserves a complete submodule, its restriction to that submodule is
compact.

Note that, following mathlib's convention in linear algebra, `restrict` designates the restriction
of an endomorphism `f : E →ₗ E` to an endomorphism `f' : ↥V →ₗ ↥V`. To prove that the restriction
`f' : ↥U →ₛₗ ↥V` of a compact operator `f : E →ₛₗ F` is compact, apply
`is_compact_operator.cod_restrict` to `f ∘ U.subtypeL`, which is compact by
`is_compact_operator.comp_clm`. -/
theorem IsCompactOperator.restrict' [SeparatedSpace M₂] {f : M₂ →ₗ[R₂] M₂}
    (hf : IsCompactOperator f) {V : Submodule R₂ M₂} (hV : ∀ v ∈ V, f v ∈ V)
    [hcomplete : CompleteSpace V] : IsCompactOperator (f.restrict hV) :=
  hf.restrict hV (completeSpace_coe_iff_isComplete.mp hcomplete).IsClosed
#align is_compact_operator.restrict' IsCompactOperator.restrict'

end Restrict

section Continuous

variable {𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂] {M₁ M₂ : Type _} [TopologicalSpace M₁] [AddCommGroup M₁]
  [TopologicalSpace M₂] [AddCommGroup M₂] [Module 𝕜₁ M₁] [Module 𝕜₂ M₂] [TopologicalAddGroup M₁]
  [ContinuousConstSMul 𝕜₁ M₁] [TopologicalAddGroup M₂] [ContinuousSMul 𝕜₂ M₂]

/- warning: is_compact_operator.continuous -> IsCompactOperator.continuous is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator.continuous IsCompactOperator.continuousₓ'. -/
@[continuity]
theorem IsCompactOperator.continuous {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) :
    Continuous f :=
  by
  letI : UniformSpace M₂ := TopologicalAddGroup.toUniformSpace _
  haveI : UniformAddGroup M₂ := comm_topologicalAddGroup_is_uniform
  -- Since `f` is linear, we only need to show that it is continuous at zero.
  -- Let `U` be a neighborhood of `0` in `M₂`.
  refine' continuous_of_continuousAt_zero f fun U hU => _
  rw [map_zero] at hU
  -- The compactness of `f` gives us a compact set `K : set M₂` such that `f ⁻¹' K` is a
  -- neighborhood of `0` in `M₁`.
  rcases hf with ⟨K, hK, hKf⟩
  -- But any compact set is totally bounded, hence Von-Neumann bounded. Thus, `K` absorbs `U`.
  -- This gives `r > 0` such that `∀ a : 𝕜₂, r ≤ ‖a‖ → K ⊆ a • U`.
  rcases hK.totally_bounded.is_vonN_bounded 𝕜₂ hU with ⟨r, hr, hrU⟩
  -- Choose `c : 𝕜₂` with `r < ‖c‖`.
  rcases NormedField.exists_lt_norm 𝕜₁ r with ⟨c, hc⟩
  have hcnz : c ≠ 0 := ne_zero_of_norm_ne_zero (hr.trans hc).Ne.symm
  -- We have `f ⁻¹' ((σ₁₂ c⁻¹) • K) = c⁻¹ • f ⁻¹' K ∈ 𝓝 0`. Thus, showing that
  -- `(σ₁₂ c⁻¹) • K ⊆ U` is enough to deduce that `f ⁻¹' U ∈ 𝓝 0`.
  suffices (σ₁₂ <| c⁻¹) • K ⊆ U by
    refine' mem_of_superset _ this
    have : IsUnit c⁻¹ := hcnz.is_unit.inv
    rwa [mem_map, preimage_smul_setₛₗ _ _ _ f this, set_smul_mem_nhds_zero_iff (inv_ne_zero hcnz)]
    infer_instance
  -- Since `σ₁₂ c⁻¹` = `(σ₁₂ c)⁻¹`, we have to prove that `K ⊆ σ₁₂ c • U`.
  rw [map_inv₀, ← subset_set_smul_iff₀ ((map_ne_zero σ₁₂).mpr hcnz)]
  -- But `σ₁₂` is isometric, so `‖σ₁₂ c‖ = ‖c‖ > r`, which concludes the argument since
  -- `∀ a : 𝕜₂, r ≤ ‖a‖ → K ⊆ a • U`.
  refine' hrU (σ₁₂ c) _
  rw [RingHomIsometric.is_iso]
  exact hc.le
#align is_compact_operator.continuous IsCompactOperator.continuous

/- warning: continuous_linear_map.mk_of_is_compact_operator -> ContinuousLinearMap.mkOfIsCompactOperator is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.mk_of_is_compact_operator ContinuousLinearMap.mkOfIsCompactOperatorₓ'. -/
/-- Upgrade a compact `linear_map` to a `continuous_linear_map`. -/
def ContinuousLinearMap.mkOfIsCompactOperator {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) :
    M₁ →SL[σ₁₂] M₂ :=
  ⟨f, hf.Continuous⟩
#align continuous_linear_map.mk_of_is_compact_operator ContinuousLinearMap.mkOfIsCompactOperator

/- warning: continuous_linear_map.mk_of_is_compact_operator_to_linear_map -> ContinuousLinearMap.mkOfIsCompactOperator_to_linearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.mk_of_is_compact_operator_to_linear_map ContinuousLinearMap.mkOfIsCompactOperator_to_linearMapₓ'. -/
@[simp]
theorem ContinuousLinearMap.mkOfIsCompactOperator_to_linearMap {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) :
    (ContinuousLinearMap.mkOfIsCompactOperator hf : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl
#align continuous_linear_map.mk_of_is_compact_operator_to_linear_map ContinuousLinearMap.mkOfIsCompactOperator_to_linearMap

/- warning: continuous_linear_map.coe_mk_of_is_compact_operator -> ContinuousLinearMap.coe_mkOfIsCompactOperator is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.coe_mk_of_is_compact_operator ContinuousLinearMap.coe_mkOfIsCompactOperatorₓ'. -/
@[simp]
theorem ContinuousLinearMap.coe_mkOfIsCompactOperator {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) : (ContinuousLinearMap.mkOfIsCompactOperator hf : M₁ → M₂) = f :=
  rfl
#align continuous_linear_map.coe_mk_of_is_compact_operator ContinuousLinearMap.coe_mkOfIsCompactOperator

/- warning: continuous_linear_map.mk_of_is_compact_operator_mem_compact_operator -> ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperator is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.mk_of_is_compact_operator_mem_compact_operator ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperatorₓ'. -/
theorem ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperator {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) :
    ContinuousLinearMap.mkOfIsCompactOperator hf ∈ compactOperator σ₁₂ M₁ M₂ :=
  hf
#align continuous_linear_map.mk_of_is_compact_operator_mem_compact_operator ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperator

end Continuous

/- warning: is_closed_set_of_is_compact_operator -> isClosed_setOf_isCompactOperator is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_closed_set_of_is_compact_operator isClosed_setOf_isCompactOperatorₓ'. -/
/-- The set of compact operators from a normed space to a complete topological vector space is
closed. -/
theorem isClosed_setOf_isCompactOperator {𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁]
    [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {M₁ M₂ : Type _} [SeminormedAddCommGroup M₁]
    [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [UniformAddGroup M₂]
    [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] :
    IsClosed { f : M₁ →SL[σ₁₂] M₂ | IsCompactOperator f } :=
  by
  refine' isClosed_of_closure_subset _
  rintro u hu
  rw [mem_closure_iff_nhds_zero] at hu
  suffices TotallyBounded (u '' Metric.closedBall 0 1)
    by
    change IsCompactOperator (u : M₁ →ₛₗ[σ₁₂] M₂)
    rw [isCompactOperator_iff_isCompact_closure_image_closedBall (u : M₁ →ₛₗ[σ₁₂] M₂) zero_lt_one]
    exact isCompact_of_totallyBounded_isClosed this.closure isClosed_closure
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  rcases exists_nhds_zero_half hU with ⟨V, hV, hVU⟩
  let SV : Set M₁ × Set M₂ := ⟨closed_ball 0 1, -V⟩
  rcases hu { f | ∀ x ∈ SV.1, f x ∈ SV.2 }
      (continuous_linear_map.has_basis_nhds_zero.mem_of_mem
        ⟨NormedSpace.isVonNBounded_closedBall _ _ _, neg_mem_nhds_zero M₂ hV⟩) with
    ⟨v, hv, huv⟩
  rcases totally_bounded_iff_subset_finite_Union_nhds_zero.mp
      (hv.is_compact_closure_image_closed_ball 1).TotallyBounded V hV with
    ⟨T, hT, hTv⟩
  have hTv : v '' closed_ball 0 1 ⊆ _ := subset_closure.trans hTv
  refine' ⟨T, hT, _⟩
  rw [image_subset_iff, preimage_Union₂] at hTv⊢
  intro x hx
  specialize hTv hx
  rw [mem_Union₂] at hTv⊢
  rcases hTv with ⟨t, ht, htx⟩
  refine' ⟨t, ht, _⟩
  rw [mem_preimage, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at htx⊢
  convert hVU _ htx _ (huv x hx) using 1
  rw [ContinuousLinearMap.sub_apply]
  abel
#align is_closed_set_of_is_compact_operator isClosed_setOf_isCompactOperator

/- warning: compact_operator_topological_closure -> compactOperator_topologicalClosure is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align compact_operator_topological_closure compactOperator_topologicalClosureₓ'. -/
theorem compactOperator_topologicalClosure {𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁]
    [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {M₁ M₂ : Type _} [SeminormedAddCommGroup M₁]
    [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [UniformAddGroup M₂]
    [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂]
    [ContinuousSMul 𝕜₂ (M₁ →SL[σ₁₂] M₂)] :
    (compactOperator σ₁₂ M₁ M₂).topologicalClosure = compactOperator σ₁₂ M₁ M₂ :=
  SetLike.ext' isClosed_setOf_isCompactOperator.closure_eq
#align compact_operator_topological_closure compactOperator_topologicalClosure

/- warning: is_compact_operator_of_tendsto -> isCompactOperator_of_tendsto is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_compact_operator_of_tendsto isCompactOperator_of_tendstoₓ'. -/
theorem isCompactOperator_of_tendsto {ι 𝕜₁ 𝕜₂ : Type _} [NontriviallyNormedField 𝕜₁]
    [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {M₁ M₂ : Type _} [SeminormedAddCommGroup M₁]
    [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [UniformAddGroup M₂]
    [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] {l : Filter ι} [l.ne_bot]
    {F : ι → M₁ →SL[σ₁₂] M₂} {f : M₁ →SL[σ₁₂] M₂} (hf : Tendsto F l (𝓝 f))
    (hF : ∀ᶠ i in l, IsCompactOperator (F i)) : IsCompactOperator f :=
  isClosed_setOf_isCompactOperator.mem_of_tendsto hf hF
#align is_compact_operator_of_tendsto isCompactOperator_of_tendsto

