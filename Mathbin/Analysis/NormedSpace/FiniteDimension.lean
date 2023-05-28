/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.normed_space.finite_dimension
! leanprover-community/mathlib commit 1b0a28e1c93409dbf6d69526863cd9984ef652ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Asymptotics.AsymptoticEquivalent
import Mathbin.Analysis.NormedSpace.AddTorsor
import Mathbin.Analysis.NormedSpace.AffineIsometry
import Mathbin.Analysis.NormedSpace.OperatorNorm
import Mathbin.Analysis.NormedSpace.RieszLemma
import Mathbin.Topology.Algebra.Module.FiniteDimension
import Mathbin.Topology.Algebra.InfiniteSum.Module
import Mathbin.Topology.Instances.Matrix

/-!
# Finite dimensional normed spaces over complete fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Over a complete nontrivially normed field, in finite dimension, all norms are equivalent and all
linear maps are continuous. Moreover, a finite-dimensional subspace is always complete and closed.

## Main results:

* `finite_dimensional.complete` : a finite-dimensional space over a complete field is complete. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution.
* `submodule.closed_of_finite_dimensional` : a finite-dimensional subspace over a complete field is
  closed
* `finite_dimensional.proper` : a finite-dimensional space over a proper field is proper. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution. It is however registered as an instance for `𝕜 = ℝ` and `𝕜 = ℂ`. As properness
  implies completeness, there is no need to also register `finite_dimensional.complete` on `ℝ` or
  `ℂ`.
* `finite_dimensional_of_is_compact_closed_ball`: Riesz' theorem: if the closed unit ball is
  compact, then the space is finite-dimensional.

## Implementation notes

The fact that all norms are equivalent is not written explicitly, as it would mean having two norms
on a single space, which is not the way type classes work. However, if one has a
finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another norm,
then the identities from `E` to `E'` and from `E'`to `E` are continuous thanks to
`linear_map.continuous_of_finite_dimensional`. This gives the desired norm equivalence.
-/


universe u v w x

noncomputable section

open Set FiniteDimensional TopologicalSpace Filter Asymptotics

open Classical BigOperators Filter Topology Asymptotics NNReal

namespace LinearIsometry

open LinearMap

variable {R : Type _} [Semiring R]

variable {F E₁ : Type _} [SeminormedAddCommGroup F] [NormedAddCommGroup E₁] [Module R E₁]

variable {R₁ : Type _} [Field R₁] [Module R₁ E₁] [Module R₁ F] [FiniteDimensional R₁ E₁]
  [FiniteDimensional R₁ F]

#print LinearIsometry.toLinearIsometryEquiv /-
/-- A linear isometry between finite dimensional spaces of equal dimension can be upgraded
    to a linear isometry equivalence. -/
def toLinearIsometryEquiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) : E₁ ≃ₗᵢ[R₁] F
    where
  toLinearEquiv := li.toLinearMap.linearEquivOfInjective li.Injective h
  norm_map' := li.norm_map'
#align linear_isometry.to_linear_isometry_equiv LinearIsometry.toLinearIsometryEquiv
-/

/- warning: linear_isometry.coe_to_linear_isometry_equiv -> LinearIsometry.coe_toLinearIsometryEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry.coe_to_linear_isometry_equiv LinearIsometry.coe_toLinearIsometryEquivₓ'. -/
@[simp]
theorem coe_toLinearIsometryEquiv (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F) :
    (li.toLinearIsometryEquiv h : E₁ → F) = li :=
  rfl
#align linear_isometry.coe_to_linear_isometry_equiv LinearIsometry.coe_toLinearIsometryEquiv

/- warning: linear_isometry.to_linear_isometry_equiv_apply -> LinearIsometry.toLinearIsometryEquiv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry.to_linear_isometry_equiv_apply LinearIsometry.toLinearIsometryEquiv_applyₓ'. -/
@[simp]
theorem toLinearIsometryEquiv_apply (li : E₁ →ₗᵢ[R₁] F) (h : finrank R₁ E₁ = finrank R₁ F)
    (x : E₁) : (li.toLinearIsometryEquiv h) x = li x :=
  rfl
#align linear_isometry.to_linear_isometry_equiv_apply LinearIsometry.toLinearIsometryEquiv_apply

end LinearIsometry

namespace AffineIsometry

open AffineMap

variable {𝕜 : Type _} {V₁ V₂ : Type _} {P₁ P₂ : Type _} [NormedField 𝕜] [NormedAddCommGroup V₁]
  [SeminormedAddCommGroup V₂] [NormedSpace 𝕜 V₁] [NormedSpace 𝕜 V₂] [MetricSpace P₁]
  [PseudoMetricSpace P₂] [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]

variable [FiniteDimensional 𝕜 V₁] [FiniteDimensional 𝕜 V₂]

#print AffineIsometry.toAffineIsometryEquiv /-
/-- An affine isometry between finite dimensional spaces of equal dimension can be upgraded
    to an affine isometry equivalence. -/
def toAffineIsometryEquiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂) (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) :
    P₁ ≃ᵃⁱ[𝕜] P₂ :=
  AffineIsometryEquiv.mk' li (li.LinearIsometry.toLinearIsometryEquiv h) (Inhabited.default P₁)
    fun p => by simp
#align affine_isometry.to_affine_isometry_equiv AffineIsometry.toAffineIsometryEquiv
-/

/- warning: affine_isometry.coe_to_affine_isometry_equiv -> AffineIsometry.coe_toAffineIsometryEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_isometry.coe_to_affine_isometry_equiv AffineIsometry.coe_toAffineIsometryEquivₓ'. -/
@[simp]
theorem coe_toAffineIsometryEquiv [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂)
    (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) : (li.toAffineIsometryEquiv h : P₁ → P₂) = li :=
  rfl
#align affine_isometry.coe_to_affine_isometry_equiv AffineIsometry.coe_toAffineIsometryEquiv

/- warning: affine_isometry.to_affine_isometry_equiv_apply -> AffineIsometry.toAffineIsometryEquiv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_isometry.to_affine_isometry_equiv_apply AffineIsometry.toAffineIsometryEquiv_applyₓ'. -/
@[simp]
theorem toAffineIsometryEquiv_apply [Inhabited P₁] (li : P₁ →ᵃⁱ[𝕜] P₂)
    (h : finrank 𝕜 V₁ = finrank 𝕜 V₂) (x : P₁) : (li.toAffineIsometryEquiv h) x = li x :=
  rfl
#align affine_isometry.to_affine_isometry_equiv_apply AffineIsometry.toAffineIsometryEquiv_apply

end AffineIsometry

section CompleteField

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type v} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {F' : Type x}
  [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F'] [TopologicalAddGroup F']
  [ContinuousSMul 𝕜 F'] [CompleteSpace 𝕜]

section Affine

variable {PE PF : Type _} [MetricSpace PE] [NormedAddTorsor E PE] [MetricSpace PF]
  [NormedAddTorsor F PF] [FiniteDimensional 𝕜 E]

include E F

/- warning: affine_map.continuous_of_finite_dimensional -> AffineMap.continuous_of_finiteDimensional is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_map.continuous_of_finite_dimensional AffineMap.continuous_of_finiteDimensionalₓ'. -/
theorem AffineMap.continuous_of_finiteDimensional (f : PE →ᵃ[𝕜] PF) : Continuous f :=
  AffineMap.continuous_linear_iff.1 f.linear.continuous_of_finiteDimensional
#align affine_map.continuous_of_finite_dimensional AffineMap.continuous_of_finiteDimensional

/- warning: affine_equiv.continuous_of_finite_dimensional -> AffineEquiv.continuous_of_finiteDimensional is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_equiv.continuous_of_finite_dimensional AffineEquiv.continuous_of_finiteDimensionalₓ'. -/
theorem AffineEquiv.continuous_of_finiteDimensional (f : PE ≃ᵃ[𝕜] PF) : Continuous f :=
  f.toAffineMap.continuous_of_finiteDimensional
#align affine_equiv.continuous_of_finite_dimensional AffineEquiv.continuous_of_finiteDimensional

#print AffineEquiv.toHomeomorphOfFiniteDimensional /-
/-- Reinterpret an affine equivalence as a homeomorphism. -/
def AffineEquiv.toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) : PE ≃ₜ PF
    where
  toEquiv := f.toEquiv
  continuous_toFun := f.continuous_of_finiteDimensional
  continuous_invFun :=
    haveI : FiniteDimensional 𝕜 F := f.linear.finite_dimensional
    f.symm.continuous_of_finite_dimensional
#align affine_equiv.to_homeomorph_of_finite_dimensional AffineEquiv.toHomeomorphOfFiniteDimensional
-/

/- warning: affine_equiv.coe_to_homeomorph_of_finite_dimensional -> AffineEquiv.coe_toHomeomorphOfFiniteDimensional is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_equiv.coe_to_homeomorph_of_finite_dimensional AffineEquiv.coe_toHomeomorphOfFiniteDimensionalₓ'. -/
@[simp]
theorem AffineEquiv.coe_toHomeomorphOfFiniteDimensional (f : PE ≃ᵃ[𝕜] PF) :
    ⇑f.toHomeomorphOfFiniteDimensional = f :=
  rfl
#align affine_equiv.coe_to_homeomorph_of_finite_dimensional AffineEquiv.coe_toHomeomorphOfFiniteDimensional

/- warning: affine_equiv.coe_to_homeomorph_of_finite_dimensional_symm -> AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_equiv.coe_to_homeomorph_of_finite_dimensional_symm AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symmₓ'. -/
@[simp]
theorem AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm (f : PE ≃ᵃ[𝕜] PF) :
    ⇑f.toHomeomorphOfFiniteDimensional.symm = f.symm :=
  rfl
#align affine_equiv.coe_to_homeomorph_of_finite_dimensional_symm AffineEquiv.coe_toHomeomorphOfFiniteDimensional_symm

end Affine

#print ContinuousLinearMap.continuous_det /-
theorem ContinuousLinearMap.continuous_det : Continuous fun f : E →L[𝕜] E => f.det :=
  by
  change Continuous fun f : E →L[𝕜] E => (f : E →ₗ[𝕜] E).det
  by_cases h : ∃ s : Finset E, Nonempty (Basis (↥s) 𝕜 E)
  · rcases h with ⟨s, ⟨b⟩⟩
    haveI : FiniteDimensional 𝕜 E := FiniteDimensional.of_fintype_basis b
    simp_rw [LinearMap.det_eq_det_toMatrix_of_finset b]
    refine' Continuous.matrix_det _
    exact
      ((LinearMap.toMatrix b b).toLinearMap.comp
          (ContinuousLinearMap.coeLM 𝕜)).continuous_of_finiteDimensional
  · unfold LinearMap.det
    simpa only [h, MonoidHom.one_apply, dif_neg, not_false_iff] using continuous_const
#align continuous_linear_map.continuous_det ContinuousLinearMap.continuous_det
-/

#print lipschitzExtensionConstant /-
/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `C * K` where `C` only depends on `E'`. We record a working value for this constant `C`
as `lipschitz_extension_constant E'`. -/
irreducible_def lipschitzExtensionConstant (E' : Type _) [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] : ℝ≥0 :=
  let A := (Basis.ofVectorSpace ℝ E').equivFun.toContinuousLinearEquiv
  max (‖A.symm.toContinuousLinearMap‖₊ * ‖A.toContinuousLinearMap‖₊) 1
#align lipschitz_extension_constant lipschitzExtensionConstant
-/

/- warning: lipschitz_extension_constant_pos -> lipschitzExtensionConstant_pos is a dubious translation:
lean 3 declaration is
  forall (E' : Type.{u1}) [_inst_12 : NormedAddCommGroup.{u1} E'] [_inst_13 : NormedSpace.{0, u1} Real E' Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E' _inst_12)] [_inst_14 : FiniteDimensional.{0, u1} Real E' Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} E' _inst_12) (NormedSpace.toModule.{0, u1} Real E' Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E' _inst_12) _inst_13)], LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (lipschitzExtensionConstant.{u1} E' _inst_12 _inst_13 _inst_14)
but is expected to have type
  forall (E' : Type.{u1}) [_inst_12 : NormedAddCommGroup.{u1} E'] [_inst_13 : NormedSpace.{0, u1} Real E' Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E' _inst_12)] [_inst_14 : FiniteDimensional.{0, u1} Real E' Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u1} E' _inst_12) (NormedSpace.toModule.{0, u1} Real E' Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E' _inst_12) _inst_13)], LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) (lipschitzExtensionConstant.{u1} E' _inst_12 _inst_13 _inst_14)
Case conversion may be inaccurate. Consider using '#align lipschitz_extension_constant_pos lipschitzExtensionConstant_posₓ'. -/
theorem lipschitzExtensionConstant_pos (E' : Type _) [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] : 0 < lipschitzExtensionConstant E' := by
  rw [lipschitzExtensionConstant]; exact zero_lt_one.trans_le (le_max_right _ _)
#align lipschitz_extension_constant_pos lipschitzExtensionConstant_pos

/- warning: lipschitz_on_with.extend_finite_dimension -> LipschitzOnWith.extend_finite_dimension is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_12 : PseudoMetricSpace.{u1} α] {E' : Type.{u2}} [_inst_13 : NormedAddCommGroup.{u2} E'] [_inst_14 : NormedSpace.{0, u2} Real E' Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E' _inst_13)] [_inst_15 : FiniteDimensional.{0, u2} Real E' Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u2} E' _inst_13) (NormedSpace.toModule.{0, u2} Real E' Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E' _inst_13) _inst_14)] {s : Set.{u1} α} {f : α -> E'} {K : NNReal}, (LipschitzOnWith.{u1, u2} α E' (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_12) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E' (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E' _inst_13))) K f s) -> (Exists.{max (succ u1) (succ u2)} (α -> E') (fun (g : α -> E') => And (LipschitzWith.{u1, u2} α E' (PseudoMetricSpace.toPseudoEMetricSpace.{u1} α _inst_12) (PseudoMetricSpace.toPseudoEMetricSpace.{u2} E' (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E' (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E' _inst_13))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (lipschitzExtensionConstant.{u2} E' _inst_13 _inst_14 _inst_15) K) g) (Set.EqOn.{u1, u2} α E' f g s)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_12 : PseudoMetricSpace.{u2} α] {E' : Type.{u1}} [_inst_13 : NormedAddCommGroup.{u1} E'] [_inst_14 : NormedSpace.{0, u1} Real E' Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E' _inst_13)] [_inst_15 : FiniteDimensional.{0, u1} Real E' Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u1} E' _inst_13) (NormedSpace.toModule.{0, u1} Real E' Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E' _inst_13) _inst_14)] {s : Set.{u2} α} {f : α -> E'} {K : NNReal}, (LipschitzOnWith.{u2, u1} α E' (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_12) (EMetricSpace.toPseudoEMetricSpace.{u1} E' (MetricSpace.toEMetricSpace.{u1} E' (NormedAddCommGroup.toMetricSpace.{u1} E' _inst_13))) K f s) -> (Exists.{max (succ u2) (succ u1)} (α -> E') (fun (g : α -> E') => And (LipschitzWith.{u2, u1} α E' (PseudoMetricSpace.toPseudoEMetricSpace.{u2} α _inst_12) (EMetricSpace.toPseudoEMetricSpace.{u1} E' (MetricSpace.toEMetricSpace.{u1} E' (NormedAddCommGroup.toMetricSpace.{u1} E' _inst_13))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (lipschitzExtensionConstant.{u1} E' _inst_13 _inst_14 _inst_15) K) g) (Set.EqOn.{u2, u1} α E' f g s)))
Case conversion may be inaccurate. Consider using '#align lipschitz_on_with.extend_finite_dimension LipschitzOnWith.extend_finite_dimensionₓ'. -/
/-- Any `K`-Lipschitz map from a subset `s` of a metric space `α` to a finite-dimensional real
vector space `E'` can be extended to a Lipschitz map on the whole space `α`, with a slightly worse
constant `lipschitz_extension_constant E' * K`. -/
theorem LipschitzOnWith.extend_finite_dimension {α : Type _} [PseudoMetricSpace α] {E' : Type _}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {s : Set α} {f : α → E'}
    {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ g : α → E', LipschitzWith (lipschitzExtensionConstant E' * K) g ∧ EqOn f g s :=
  by
  /- This result is already known for spaces `ι → ℝ`. We use a continuous linear equiv between
    `E'` and such a space to transfer the result to `E'`. -/
  let ι : Type _ := Basis.ofVectorSpaceIndex ℝ E'
  let A := (Basis.ofVectorSpace ℝ E').equivFun.toContinuousLinearEquiv
  have LA : LipschitzWith ‖A.to_continuous_linear_map‖₊ A := by apply A.lipschitz
  have L : LipschitzOnWith (‖A.to_continuous_linear_map‖₊ * K) (A ∘ f) s :=
    LA.comp_lipschitz_on_with hf
  obtain ⟨g, hg, gs⟩ :
    ∃ g : α → ι → ℝ, LipschitzWith (‖A.to_continuous_linear_map‖₊ * K) g ∧ eq_on (A ∘ f) g s :=
    L.extend_pi
  refine' ⟨A.symm ∘ g, _, _⟩
  · have LAsymm : LipschitzWith ‖A.symm.to_continuous_linear_map‖₊ A.symm := by
      apply A.symm.lipschitz
    apply (LAsymm.comp hg).weaken
    rw [lipschitzExtensionConstant, ← mul_assoc]
    refine' mul_le_mul' (le_max_left _ _) le_rfl
  · intro x hx
    have : A (f x) = g x := gs hx
    simp only [(· ∘ ·), ← this, A.symm_apply_apply]
#align lipschitz_on_with.extend_finite_dimension LipschitzOnWith.extend_finite_dimension

/- warning: linear_map.exists_antilipschitz_with -> LinearMap.exists_antilipschitzWith is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.exists_antilipschitz_with LinearMap.exists_antilipschitzWithₓ'. -/
theorem LinearMap.exists_antilipschitzWith [FiniteDimensional 𝕜 E] (f : E →ₗ[𝕜] F)
    (hf : f.ker = ⊥) : ∃ K > 0, AntilipschitzWith K f :=
  by
  cases subsingleton_or_nontrivial E
  · exact ⟨1, zero_lt_one, AntilipschitzWith.of_subsingleton⟩
  · rw [LinearMap.ker_eq_bot] at hf
    let e : E ≃L[𝕜] f.range := (LinearEquiv.ofInjective f hf).toContinuousLinearEquiv
    exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩
#align linear_map.exists_antilipschitz_with LinearMap.exists_antilipschitzWith

/- warning: linear_independent.eventually -> LinearIndependent.eventually is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {ι : Type.{u3}} [_inst_12 : Finite.{succ u3} ι] {f : ι -> E}, (LinearIndependent.{u3, u1, u2} ι 𝕜 E f (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3)) -> (Filter.Eventually.{max u3 u2} (ι -> E) (fun (g : ι -> E) => LinearIndependent.{u3, u1, u2} ι 𝕜 E g (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3)) (nhds.{max u3 u2} (ι -> E) (Pi.topologicalSpace.{u3, u2} ι (fun (ᾰ : ι) => E) (fun (a : ι) => UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))) f))
but is expected to have type
  forall {𝕜 : Type.{u2}} [_inst_1 : NontriviallyNormedField.{u2} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] [_inst_11 : CompleteSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSeminormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1))))))] {ι : Type.{u1}} [_inst_12 : Finite.{succ u1} ι] {f : ι -> E}, (LinearIndependent.{u1, u2, u3} ι 𝕜 E f (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_2)) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2) _inst_3)) -> (Filter.Eventually.{max u3 u1} (ι -> E) (fun (g : ι -> E) => LinearIndependent.{u1, u2, u3} ι 𝕜 E g (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_2)) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2) _inst_3)) (nhds.{max u3 u1} (ι -> E) (Pi.topologicalSpace.{u1, u3} ι (fun (ᾰ : ι) => E) (fun (a : ι) => UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2))))) f))
Case conversion may be inaccurate. Consider using '#align linear_independent.eventually LinearIndependent.eventuallyₓ'. -/
protected theorem LinearIndependent.eventually {ι} [Finite ι] {f : ι → E}
    (hf : LinearIndependent 𝕜 f) : ∀ᶠ g in 𝓝 f, LinearIndependent 𝕜 g :=
  by
  cases nonempty_fintype ι
  simp only [Fintype.linearIndependent_iff'] at hf⊢
  rcases LinearMap.exists_antilipschitzWith _ hf with ⟨K, K0, hK⟩
  have : tendsto (fun g : ι → E => ∑ i, ‖g i - f i‖) (𝓝 f) (𝓝 <| ∑ i, ‖f i - f i‖) :=
    tendsto_finset_sum _ fun i hi =>
      tendsto.norm <| ((continuous_apply i).Tendsto _).sub tendsto_const_nhds
  simp only [sub_self, norm_zero, Finset.sum_const_zero] at this
  refine' (this.eventually (gt_mem_nhds <| inv_pos.2 K0)).mono fun g hg => _
  replace hg : (∑ i, ‖g i - f i‖₊) < K⁻¹; · rw [← NNReal.coe_lt_coe]; push_cast ; exact hg
  rw [LinearMap.ker_eq_bot]
  refine' (hK.add_sub_lipschitz_with (LipschitzWith.of_dist_le_mul fun v u => _) hg).Injective
  simp only [dist_eq_norm, LinearMap.lsum_apply, Pi.sub_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smulRight_apply, LinearMap.id_apply, ←
    Finset.sum_sub_distrib, ← smul_sub, ← sub_smul, NNReal.coe_sum, coe_nnnorm, Finset.sum_mul]
  refine' norm_sum_le_of_le _ fun i _ => _
  rw [norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (v - u) i) (norm_nonneg _)
#align linear_independent.eventually LinearIndependent.eventually

/- warning: is_open_set_of_linear_independent -> isOpen_setOf_linearIndependent is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {ι : Type.{u3}} [_inst_12 : Finite.{succ u3} ι], IsOpen.{max u3 u2} (ι -> E) (Pi.topologicalSpace.{u3, u2} ι (fun (ᾰ : ι) => E) (fun (a : ι) => UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))) (setOf.{max u3 u2} (ι -> E) (fun (f : ι -> E) => LinearIndependent.{u3, u1, u2} ι 𝕜 E f (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3)))
but is expected to have type
  forall {𝕜 : Type.{u2}} [_inst_1 : NontriviallyNormedField.{u2} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] [_inst_11 : CompleteSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSeminormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1))))))] {ι : Type.{u1}} [_inst_12 : Finite.{succ u1} ι], IsOpen.{max u3 u1} (ι -> E) (Pi.topologicalSpace.{u1, u3} ι (fun (ᾰ : ι) => E) (fun (a : ι) => UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2))))) (setOf.{max u3 u1} (ι -> E) (fun (f : ι -> E) => LinearIndependent.{u1, u2, u3} ι 𝕜 E f (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_2)) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2) _inst_3)))
Case conversion may be inaccurate. Consider using '#align is_open_set_of_linear_independent isOpen_setOf_linearIndependentₓ'. -/
theorem isOpen_setOf_linearIndependent {ι : Type _} [Finite ι] :
    IsOpen { f : ι → E | LinearIndependent 𝕜 f } :=
  isOpen_iff_mem_nhds.2 fun f => LinearIndependent.eventually
#align is_open_set_of_linear_independent isOpen_setOf_linearIndependent

/- warning: is_open_set_of_nat_le_rank -> isOpen_setOf_nat_le_rank is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_open_set_of_nat_le_rank isOpen_setOf_nat_le_rankₓ'. -/
theorem isOpen_setOf_nat_le_rank (n : ℕ) : IsOpen { f : E →L[𝕜] F | ↑n ≤ (f : E →ₗ[𝕜] F).rank } :=
  by
  simp only [LinearMap.le_rank_iff_exists_linearIndependent_finset, set_of_exists, ← exists_prop]
  refine' isOpen_biUnion fun t ht => _
  have : Continuous fun f : E →L[𝕜] F => fun x : (t : Set E) => f x :=
    continuous_pi fun x => (ContinuousLinearMap.apply 𝕜 F (x : E)).Continuous
  exact is_open_set_of_linear_independent.preimage this
#align is_open_set_of_nat_le_rank isOpen_setOf_nat_le_rank

/- warning: basis.op_nnnorm_le -> Basis.op_nnnorm_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.op_nnnorm_le Basis.op_nnnorm_leₓ'. -/
theorem Basis.op_nnnorm_le {ι : Type _} [Fintype ι] (v : Basis ι 𝕜 E) {u : E →L[𝕜] F} (M : ℝ≥0)
    (hu : ∀ i, ‖u (v i)‖₊ ≤ M) : ‖u‖₊ ≤ Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖₊ * M :=
  u.op_nnnorm_le_bound _ fun e =>
    by
    set φ := v.equiv_funL.to_continuous_linear_map
    calc
      ‖u e‖₊ = ‖u (∑ i, v.equiv_fun e i • v i)‖₊ := by rw [v.sum_equiv_fun]
      _ = ‖∑ i, v.equiv_fun e i • (u <| v i)‖₊ := by simp [u.map_sum, LinearMap.map_smul]
      _ ≤ ∑ i, ‖v.equiv_fun e i • (u <| v i)‖₊ := (nnnorm_sum_le _ _)
      _ = ∑ i, ‖v.equiv_fun e i‖₊ * ‖u (v i)‖₊ := by simp only [nnnorm_smul]
      _ ≤ ∑ i, ‖v.equiv_fun e i‖₊ * M :=
        (Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hu i) (zero_le _))
      _ = (∑ i, ‖v.equiv_fun e i‖₊) * M := finset.sum_mul.symm
      _ ≤ Fintype.card ι • (‖φ‖₊ * ‖e‖₊) * M :=
        (suffices _ from mul_le_mul_of_nonneg_right this (zero_le M)
        calc
          (∑ i, ‖v.equiv_fun e i‖₊) ≤ Fintype.card ι • ‖φ e‖₊ := Pi.sum_nnnorm_apply_le_nnnorm _
          _ ≤ Fintype.card ι • (‖φ‖₊ * ‖e‖₊) := nsmul_le_nsmul_of_le_right (φ.le_op_nnnorm e) _
          )
      _ = Fintype.card ι • ‖φ‖₊ * M * ‖e‖₊ := by simp only [smul_mul_assoc, mul_right_comm]
      
#align basis.op_nnnorm_le Basis.op_nnnorm_le

/- warning: basis.op_norm_le -> Basis.op_norm_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.op_norm_le Basis.op_norm_leₓ'. -/
theorem Basis.op_norm_le {ι : Type _} [Fintype ι] (v : Basis ι 𝕜 E) {u : E →L[𝕜] F} {M : ℝ}
    (hM : 0 ≤ M) (hu : ∀ i, ‖u (v i)‖ ≤ M) :
    ‖u‖ ≤ Fintype.card ι • ‖v.equivFunL.toContinuousLinearMap‖ * M := by
  simpa using nnreal.coe_le_coe.mpr (v.op_nnnorm_le ⟨M, hM⟩ hu)
#align basis.op_norm_le Basis.op_norm_le

/- warning: basis.exists_op_nnnorm_le -> Basis.exists_op_nnnorm_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.exists_op_nnnorm_le Basis.exists_op_nnnorm_leₓ'. -/
/-- A weaker version of `basis.op_nnnorm_le` that abstracts away the value of `C`. -/
theorem Basis.exists_op_nnnorm_le {ι : Type _} [Finite ι] (v : Basis ι 𝕜 E) :
    ∃ C > (0 : ℝ≥0), ∀ {u : E →L[𝕜] F} (M : ℝ≥0), (∀ i, ‖u (v i)‖₊ ≤ M) → ‖u‖₊ ≤ C * M := by
  cases nonempty_fintype ι <;>
    exact
      ⟨max (Fintype.card ι • ‖v.equiv_funL.to_continuous_linear_map‖₊) 1,
        zero_lt_one.trans_le (le_max_right _ _), fun u M hu =>
        (v.op_nnnorm_le M hu).trans <| mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le M)⟩
#align basis.exists_op_nnnorm_le Basis.exists_op_nnnorm_le

/- warning: basis.exists_op_norm_le -> Basis.exists_op_norm_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align basis.exists_op_norm_le Basis.exists_op_norm_leₓ'. -/
/-- A weaker version of `basis.op_norm_le` that abstracts away the value of `C`. -/
theorem Basis.exists_op_norm_le {ι : Type _} [Finite ι] (v : Basis ι 𝕜 E) :
    ∃ C > (0 : ℝ), ∀ {u : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ‖u (v i)‖ ≤ M) → ‖u‖ ≤ C * M :=
  let ⟨C, hC, h⟩ := v.exists_op_nnnorm_le
  ⟨C, hC, fun u => Subtype.forall'.mpr h⟩
#align basis.exists_op_norm_le Basis.exists_op_norm_le

instance [FiniteDimensional 𝕜 E] [SecondCountableTopology F] :
    SecondCountableTopology (E →L[𝕜] F) :=
  by
  set d := FiniteDimensional.finrank 𝕜 E
  suffices :
    ∀ ε > (0 : ℝ), ∃ n : (E →L[𝕜] F) → Fin d → ℕ, ∀ f g : E →L[𝕜] F, n f = n g → dist f g ≤ ε
  exact
    Metric.secondCountable_of_countable_discretization fun ε ε_pos =>
      ⟨Fin d → ℕ, by infer_instance, this ε ε_pos⟩
  intro ε ε_pos
  obtain ⟨u : ℕ → F, hu : DenseRange u⟩ := exists_dense_seq F
  let v := FiniteDimensional.finBasis 𝕜 E
  obtain
    ⟨C : ℝ, C_pos : 0 < C, hC :
      ∀ {φ : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ‖φ (v i)‖ ≤ M) → ‖φ‖ ≤ C * M⟩ :=
    v.exists_op_norm_le
  have h_2C : 0 < 2 * C := mul_pos zero_lt_two C_pos
  have hε2C : 0 < ε / (2 * C) := div_pos ε_pos h_2C
  have : ∀ φ : E →L[𝕜] F, ∃ n : Fin d → ℕ, ‖φ - (v.constrL <| u ∘ n)‖ ≤ ε / 2 :=
    by
    intro φ
    have : ∀ i, ∃ n, ‖φ (v i) - u n‖ ≤ ε / (2 * C) :=
      by
      simp only [norm_sub_rev]
      intro i
      have : φ (v i) ∈ closure (range u) := hu _
      obtain ⟨n, hn⟩ : ∃ n, ‖u n - φ (v i)‖ < ε / (2 * C) :=
        by
        rw [mem_closure_iff_nhds_basis Metric.nhds_basis_ball] at this
        specialize this (ε / (2 * C)) hε2C
        simpa [dist_eq_norm]
      exact ⟨n, le_of_lt hn⟩
    choose n hn using this
    use n
    replace hn : ∀ i : Fin d, ‖(φ - (v.constrL <| u ∘ n)) (v i)‖ ≤ ε / (2 * C); · simp [hn]
    have : C * (ε / (2 * C)) = ε / 2 := by
      rw [eq_div_iff (two_ne_zero : (2 : ℝ) ≠ 0), mul_comm, ← mul_assoc,
        mul_div_cancel' _ (ne_of_gt h_2C)]
    specialize hC (le_of_lt hε2C) hn
    rwa [this] at hC
  choose n hn using this
  set Φ := fun φ : E →L[𝕜] F => v.constrL <| u ∘ n φ
  change ∀ z, dist z (Φ z) ≤ ε / 2 at hn
  use n
  intro x y hxy
  calc
    dist x y ≤ dist x (Φ x) + dist (Φ x) y := dist_triangle _ _ _
    _ = dist x (Φ x) + dist y (Φ y) := by simp [Φ, hxy, dist_comm]
    _ ≤ ε := by linarith [hn x, hn y]
    

variable (𝕜 E)

#print FiniteDimensional.complete /-
theorem FiniteDimensional.complete [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  have : UniformEmbedding e.to_linear_equiv.to_equiv.symm := e.symm.uniform_embedding
  exact (completeSpace_congr this).1 (by infer_instance)
#align finite_dimensional.complete FiniteDimensional.complete
-/

variable {𝕜 E}

#print Submodule.complete_of_finiteDimensional /-
/-- A finite-dimensional subspace is complete. -/
theorem Submodule.complete_of_finiteDimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsComplete (s : Set E) :=
  completeSpace_coe_iff_isComplete.1 (FiniteDimensional.complete 𝕜 s)
#align submodule.complete_of_finite_dimensional Submodule.complete_of_finiteDimensional
-/

#print Submodule.closed_of_finiteDimensional /-
/-- A finite-dimensional subspace is closed. -/
theorem Submodule.closed_of_finiteDimensional (s : Submodule 𝕜 E) [FiniteDimensional 𝕜 s] :
    IsClosed (s : Set E) :=
  s.complete_of_finiteDimensional.IsClosed
#align submodule.closed_of_finite_dimensional Submodule.closed_of_finiteDimensional
-/

/- warning: affine_subspace.closed_of_finite_dimensional -> AffineSubspace.closed_of_finiteDimensional is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align affine_subspace.closed_of_finite_dimensional AffineSubspace.closed_of_finiteDimensionalₓ'. -/
theorem AffineSubspace.closed_of_finiteDimensional {P : Type _} [MetricSpace P]
    [NormedAddTorsor E P] (s : AffineSubspace 𝕜 P) [FiniteDimensional 𝕜 s.direction] :
    IsClosed (s : Set P) :=
  s.isClosed_direction_iff.mp s.direction.closed_of_finiteDimensional
#align affine_subspace.closed_of_finite_dimensional AffineSubspace.closed_of_finiteDimensional

section Riesz

/- warning: exists_norm_le_le_norm_sub_of_finset -> exists_norm_le_le_norm_sub_of_finset is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {c : 𝕜}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) c)) -> (forall {R : Real}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) c) R) -> (Not (FiniteDimensional.{u1, u2} 𝕜 E (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3))) -> (forall (s : Finset.{u2} E), Exists.{succ u2} E (fun (x : E) => And (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x) R) (forall (y : E), (Membership.Mem.{u2, u2} E (Finset.{u2} E) (Finset.hasMem.{u2} E) y s) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) y x)))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {c : 𝕜}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) c)) -> (forall {R : Real}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) c) R) -> (Not (FiniteDimensional.{u1, u2} 𝕜 E (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3))) -> (forall (s : Finset.{u2} E), Exists.{succ u2} E (fun (x : E) => And (LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) x) R) (forall (y : E), (Membership.mem.{u2, u2} E (Finset.{u2} E) (Finset.instMembershipFinset.{u2} E) y s) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) y x)))))))
Case conversion may be inaccurate. Consider using '#align exists_norm_le_le_norm_sub_of_finset exists_norm_le_le_norm_sub_of_finsetₓ'. -/
/-- In an infinite dimensional space, given a finite number of points, one may find a point
with norm at most `R` which is at distance at least `1` of all these points. -/
theorem exists_norm_le_le_norm_sub_of_finset {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R)
    (h : ¬FiniteDimensional 𝕜 E) (s : Finset E) : ∃ x : E, ‖x‖ ≤ R ∧ ∀ y ∈ s, 1 ≤ ‖y - x‖ :=
  by
  let F := Submodule.span 𝕜 (s : Set E)
  haveI : FiniteDimensional 𝕜 F :=
    Module.finite_def.2
      ((Submodule.fg_top _).2 (Submodule.fg_def.2 ⟨s, Finset.finite_toSet _, rfl⟩))
  have Fclosed : IsClosed (F : Set E) := Submodule.closed_of_finiteDimensional _
  have : ∃ x, x ∉ F := by
    contrapose! h
    have : (⊤ : Submodule 𝕜 E) = F := by ext x; simp [h]
    have : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 E) := by rwa [this]
    refine' Module.finite_def.2 ((Submodule.fg_top _).1 (Module.finite_def.1 this))
  obtain ⟨x, xR, hx⟩ : ∃ x : E, ‖x‖ ≤ R ∧ ∀ y : E, y ∈ F → 1 ≤ ‖x - y‖ :=
    riesz_lemma_of_norm_lt hc hR Fclosed this
  have hx' : ∀ y : E, y ∈ F → 1 ≤ ‖y - x‖ := by intro y hy; rw [← norm_neg]; simpa using hx y hy
  exact ⟨x, xR, fun y hy => hx' _ (Submodule.subset_span hy)⟩
#align exists_norm_le_le_norm_sub_of_finset exists_norm_le_le_norm_sub_of_finset

/- warning: exists_seq_norm_le_one_le_norm_sub' -> exists_seq_norm_le_one_le_norm_sub' is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {c : 𝕜}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) c)) -> (forall {R : Real}, (LT.lt.{0} Real Real.hasLt (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) c) R) -> (Not (FiniteDimensional.{u1, u2} 𝕜 E (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3))) -> (Exists.{succ u2} (Nat -> E) (fun (f : Nat -> E) => And (forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (f n)) R) (forall (m : Nat) (n : Nat), (Ne.{1} Nat m n) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) (f m) (f n))))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {c : 𝕜}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) c)) -> (forall {R : Real}, (LT.lt.{0} Real Real.instLTReal (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) c) R) -> (Not (FiniteDimensional.{u1, u2} 𝕜 E (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3))) -> (Exists.{succ u2} (Nat -> E) (fun (f : Nat -> E) => And (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) (f n)) R) (forall (m : Nat) (n : Nat), (Ne.{1} Nat m n) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) (f m) (f n))))))))
Case conversion may be inaccurate. Consider using '#align exists_seq_norm_le_one_le_norm_sub' exists_seq_norm_le_one_le_norm_sub'ₓ'. -/
/-- In an infinite-dimensional normed space, there exists a sequence of points which are all
bounded by `R` and at distance at least `1`. For a version not assuming `c` and `R`, see
`exists_seq_norm_le_one_le_norm_sub`. -/
theorem exists_seq_norm_le_one_le_norm_sub' {c : 𝕜} (hc : 1 < ‖c‖) {R : ℝ} (hR : ‖c‖ < R)
    (h : ¬FiniteDimensional 𝕜 E) : ∃ f : ℕ → E, (∀ n, ‖f n‖ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ‖f m - f n‖ :=
  by
  have : IsSymm E fun x y : E => 1 ≤ ‖x - y‖ :=
    by
    constructor
    intro x y hxy
    rw [← norm_neg]
    simpa
  apply
    exists_seq_of_forall_finset_exists' (fun x : E => ‖x‖ ≤ R) fun (x : E) (y : E) => 1 ≤ ‖x - y‖
  intro s hs
  exact exists_norm_le_le_norm_sub_of_finset hc hR h s
#align exists_seq_norm_le_one_le_norm_sub' exists_seq_norm_le_one_le_norm_sub'

/- warning: exists_seq_norm_le_one_le_norm_sub -> exists_seq_norm_le_one_le_norm_sub is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))], (Not (FiniteDimensional.{u1, u2} 𝕜 E (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3))) -> (Exists.{1} Real (fun (R : Real) => Exists.{succ u2} (Nat -> E) (fun (f : Nat -> E) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) R) (And (forall (n : Nat), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (f n)) R) (forall (m : Nat) (n : Nat), (Ne.{1} Nat m n) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) (f m) (f n)))))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))], (Not (FiniteDimensional.{u1, u2} 𝕜 E (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3))) -> (Exists.{1} Real (fun (R : Real) => Exists.{succ u2} (Nat -> E) (fun (f : Nat -> E) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) R) (And (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) (f n)) R) (forall (m : Nat) (n : Nat), (Ne.{1} Nat m n) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) (f m) (f n)))))))))
Case conversion may be inaccurate. Consider using '#align exists_seq_norm_le_one_le_norm_sub exists_seq_norm_le_one_le_norm_subₓ'. -/
theorem exists_seq_norm_le_one_le_norm_sub (h : ¬FiniteDimensional 𝕜 E) :
    ∃ (R : ℝ)(f : ℕ → E), 1 < R ∧ (∀ n, ‖f n‖ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ‖f m - f n‖ :=
  by
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, 1 < ‖c‖ := NormedField.exists_one_lt_norm 𝕜
  have A : ‖c‖ < ‖c‖ + 1 := by linarith
  rcases exists_seq_norm_le_one_le_norm_sub' hc A h with ⟨f, hf⟩
  exact ⟨‖c‖ + 1, f, hc.trans A, hf.1, hf.2⟩
#align exists_seq_norm_le_one_le_norm_sub exists_seq_norm_le_one_le_norm_sub

variable (𝕜)

/- warning: finite_dimensional_of_is_compact_closed_ball₀ -> finiteDimensional_of_isCompact_closed_ball₀ is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (IsCompact.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (Metric.closedBall.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))))) r)) -> (FiniteDimensional.{u1, u2} 𝕜 E (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3))
but is expected to have type
  forall (𝕜 : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (IsCompact.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (Metric.closedBall.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)) (OfNat.ofNat.{u2} E 0 (Zero.toOfNat0.{u2} E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))))) r)) -> (FiniteDimensional.{u1, u2} 𝕜 E (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3))
Case conversion may be inaccurate. Consider using '#align finite_dimensional_of_is_compact_closed_ball₀ finiteDimensional_of_isCompact_closed_ball₀ₓ'. -/
/-- **Riesz's theorem**: if a closed ball with center zero of positive radius is compact in a vector
space, then the space is finite-dimensional. -/
theorem finiteDimensional_of_isCompact_closed_ball₀ {r : ℝ} (rpos : 0 < r)
    (h : IsCompact (Metric.closedBall (0 : E) r)) : FiniteDimensional 𝕜 E :=
  by
  by_contra hfin
  obtain ⟨R, f, Rgt, fle, lef⟩ :
    ∃ (R : ℝ)(f : ℕ → E), 1 < R ∧ (∀ n, ‖f n‖ ≤ R) ∧ ∀ m n, m ≠ n → 1 ≤ ‖f m - f n‖ :=
    exists_seq_norm_le_one_le_norm_sub hfin
  have rRpos : 0 < r / R := div_pos rpos (zero_lt_one.trans Rgt)
  obtain ⟨c, hc⟩ : ∃ c : 𝕜, 0 < ‖c‖ ∧ ‖c‖ < r / R := NormedField.exists_norm_lt _ rRpos
  let g := fun n : ℕ => c • f n
  have A : ∀ n, g n ∈ Metric.closedBall (0 : E) r :=
    by
    intro n
    simp only [norm_smul, dist_zero_right, Metric.mem_closedBall]
    calc
      ‖c‖ * ‖f n‖ ≤ r / R * R := mul_le_mul hc.2.le (fle n) (norm_nonneg _) rRpos.le
      _ = r := by field_simp [(zero_lt_one.trans Rgt).ne']
      
  obtain ⟨x, hx, φ, φmono, φlim⟩ :
    ∃ (x : E)(H : x ∈ Metric.closedBall (0 : E) r)(φ : ℕ → ℕ),
      StrictMono φ ∧ tendsto (g ∘ φ) at_top (𝓝 x) :=
    h.tendsto_subseq A
  have B : CauchySeq (g ∘ φ) := φlim.cauchy_seq
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → dist ((g ∘ φ) n) ((g ∘ φ) N) < ‖c‖ :=
    Metric.cauchySeq_iff'.1 B ‖c‖ hc.1
  apply lt_irrefl ‖c‖
  calc
    ‖c‖ ≤ dist (g (φ (N + 1))) (g (φ N)) :=
      by
      conv_lhs => rw [← mul_one ‖c‖]
      simp only [g, dist_eq_norm, ← smul_sub, norm_smul, -mul_one]
      apply mul_le_mul_of_nonneg_left (lef _ _ (ne_of_gt _)) (norm_nonneg _)
      exact φmono (Nat.lt_succ_self N)
    _ < ‖c‖ := hN (N + 1) (Nat.le_succ N)
    
#align finite_dimensional_of_is_compact_closed_ball₀ finiteDimensional_of_isCompact_closed_ball₀

/- warning: finite_dimensional_of_is_compact_closed_ball -> finiteDimensional_of_isCompact_closedBall is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (forall {c : E}, (IsCompact.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (Metric.closedBall.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)) c r)) -> (FiniteDimensional.{u1, u2} 𝕜 E (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3)))
but is expected to have type
  forall (𝕜 : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (forall {c : E}, (IsCompact.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (Metric.closedBall.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)) c r)) -> (FiniteDimensional.{u1, u2} 𝕜 E (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3)))
Case conversion may be inaccurate. Consider using '#align finite_dimensional_of_is_compact_closed_ball finiteDimensional_of_isCompact_closedBallₓ'. -/
/-- **Riesz's theorem**: if a closed ball of positive radius is compact in a vector space, then the
space is finite-dimensional. -/
theorem finiteDimensional_of_isCompact_closedBall {r : ℝ} (rpos : 0 < r) {c : E}
    (h : IsCompact (Metric.closedBall c r)) : FiniteDimensional 𝕜 E :=
  by
  apply finiteDimensional_of_isCompact_closed_ball₀ 𝕜 rpos
  have : Continuous fun x => -c + x := continuous_const.add continuous_id
  simpa using h.image this
#align finite_dimensional_of_is_compact_closed_ball finiteDimensional_of_isCompact_closedBall

/- warning: has_compact_mul_support.eq_one_or_finite_dimensional -> HasCompactMulSupport.eq_one_or_finiteDimensional is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {X : Type.{u3}} [_inst_12 : TopologicalSpace.{u3} X] [_inst_13 : One.{u3} X] [_inst_14 : T2Space.{u3} X _inst_12] {f : E -> X}, (HasCompactMulSupport.{u2, u3} E X (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) _inst_13 f) -> (Continuous.{u2, u3} E X (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) _inst_12 f) -> (Or (Eq.{max (succ u2) (succ u3)} (E -> X) f (OfNat.ofNat.{max u2 u3} (E -> X) 1 (OfNat.mk.{max u2 u3} (E -> X) 1 (One.one.{max u2 u3} (E -> X) (Pi.instOne.{u2, u3} E (fun (ᾰ : E) => X) (fun (i : E) => _inst_13)))))) (FiniteDimensional.{u1, u2} 𝕜 E (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3)))
but is expected to have type
  forall (𝕜 : Type.{u2}) [_inst_1 : NontriviallyNormedField.{u2} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] [_inst_11 : CompleteSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSeminormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1))))))] {X : Type.{u1}} [_inst_12 : TopologicalSpace.{u1} X] [_inst_13 : One.{u1} X] [_inst_14 : T2Space.{u1} X _inst_12] {f : E -> X}, (HasCompactMulSupport.{u3, u1} E X (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) _inst_13 f) -> (Continuous.{u3, u1} E X (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) _inst_12 f) -> (Or (Eq.{max (succ u3) (succ u1)} (E -> X) f (OfNat.ofNat.{max u3 u1} (E -> X) 1 (One.toOfNat1.{max u3 u1} (E -> X) (Pi.instOne.{u3, u1} E (fun (a._@.Mathlib.Analysis.NormedSpace.FiniteDimension._hyg.8925 : E) => X) (fun (i : E) => _inst_13))))) (FiniteDimensional.{u2, u3} 𝕜 E (NormedDivisionRing.toDivisionRing.{u2} 𝕜 (NormedField.toNormedDivisionRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1))) (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_2) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2) _inst_3)))
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support.eq_one_or_finite_dimensional HasCompactMulSupport.eq_one_or_finiteDimensionalₓ'. -/
/-- If a function has compact multiplicative support, then either the function is trivial or the
space if finite-dimensional. -/
@[to_additive
      "If a function has compact support, then either the function is trivial or the\nspace if finite-dimensional."]
theorem HasCompactMulSupport.eq_one_or_finiteDimensional {X : Type _} [TopologicalSpace X] [One X]
    [T2Space X] {f : E → X} (hf : HasCompactMulSupport f) (h'f : Continuous f) :
    f = 1 ∨ FiniteDimensional 𝕜 E :=
  by
  by_cases h : ∀ x, f x = 1; · apply Or.inl; ext x; exact h x
  apply Or.inr
  push_neg  at h
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 1; exact h
  have : Function.mulSupport f ∈ 𝓝 x := h'f.is_open_mul_support.mem_nhds hx
  obtain ⟨r, rpos, hr⟩ : ∃ (r : ℝ)(hi : 0 < r), Metric.closedBall x r ⊆ Function.mulSupport f
  exact metric.nhds_basis_closed_ball.mem_iff.1 this
  have : IsCompact (Metric.closedBall x r) :=
    isCompact_of_isClosed_subset hf Metric.isClosed_ball (hr.trans (subset_mulTSupport _))
  exact finiteDimensional_of_isCompact_closedBall 𝕜 rpos this
#align has_compact_mul_support.eq_one_or_finite_dimensional HasCompactMulSupport.eq_one_or_finiteDimensional
#align has_compact_support.eq_zero_or_finite_dimensional HasCompactSupport.eq_zero_or_finiteDimensional

end Riesz

/- warning: linear_equiv.closed_embedding_of_injective -> LinearEquiv.closedEmbedding_of_injective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.closed_embedding_of_injective LinearEquiv.closedEmbedding_of_injectiveₓ'. -/
/-- An injective linear map with finite-dimensional domain is a closed embedding. -/
theorem LinearEquiv.closedEmbedding_of_injective {f : E →ₗ[𝕜] F} (hf : f.ker = ⊥)
    [FiniteDimensional 𝕜 E] : ClosedEmbedding ⇑f :=
  let g := LinearEquiv.ofInjective f (LinearMap.ker_eq_bot.mp hf)
  { embedding_subtype_val.comp g.toContinuousLinearEquiv.toHomeomorph.Embedding with
    closed_range := by
      haveI := f.finite_dimensional_range
      simpa [f.range_coe] using f.range.closed_of_finite_dimensional }
#align linear_equiv.closed_embedding_of_injective LinearEquiv.closedEmbedding_of_injective

/- warning: continuous_linear_map.exists_right_inverse_of_surjective -> ContinuousLinearMap.exists_right_inverse_of_surjective is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.exists_right_inverse_of_surjective ContinuousLinearMap.exists_right_inverse_of_surjectiveₓ'. -/
theorem ContinuousLinearMap.exists_right_inverse_of_surjective [FiniteDimensional 𝕜 F]
    (f : E →L[𝕜] F) (hf : LinearMap.range f = ⊤) :
    ∃ g : F →L[𝕜] E, f.comp g = ContinuousLinearMap.id 𝕜 F :=
  let ⟨g, hg⟩ := (f : E →ₗ[𝕜] F).exists_rightInverse_of_surjective hf
  ⟨g.toContinuousLinearMap, ContinuousLinearMap.ext <| LinearMap.ext_iff.1 hg⟩
#align continuous_linear_map.exists_right_inverse_of_surjective ContinuousLinearMap.exists_right_inverse_of_surjective

/- warning: closed_embedding_smul_left -> closedEmbedding_smul_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {c : E}, (Ne.{succ u2} E c (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2)))))))))) -> (ClosedEmbedding.{u1, u2} 𝕜 E (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (fun (x : 𝕜) => SMul.smul.{u1, u2} 𝕜 E (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3))))) x c))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] [_inst_11 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))] {c : E}, (Ne.{succ u2} E c (OfNat.ofNat.{u2} E 0 (Zero.toOfNat0.{u2} E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))))))) -> (ClosedEmbedding.{u1, u2} 𝕜 E (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (fun (x : 𝕜) => HSMul.hSMul.{u1, u2, u2} 𝕜 E E (instHSMul.{u1, u2} 𝕜 E (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))))) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))))) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3)))))) x c))
Case conversion may be inaccurate. Consider using '#align closed_embedding_smul_left closedEmbedding_smul_leftₓ'. -/
theorem closedEmbedding_smul_left {c : E} (hc : c ≠ 0) : ClosedEmbedding fun x : 𝕜 => x • c :=
  LinearEquiv.closedEmbedding_of_injective (LinearMap.ker_toSpanSingleton 𝕜 E hc)
#align closed_embedding_smul_left closedEmbedding_smul_left

#print isClosedMap_smul_left /-
-- `smul` is a closed map in the first argument.
theorem isClosedMap_smul_left (c : E) : IsClosedMap fun x : 𝕜 => x • c :=
  by
  by_cases hc : c = 0
  · simp_rw [hc, smul_zero]; exact isClosedMap_const
  · exact (closedEmbedding_smul_left hc).IsClosedMap
#align is_closed_map_smul_left isClosedMap_smul_left
-/

open ContinuousLinearMap

#print ContinuousLinearEquiv.piRing /-
/-- Continuous linear equivalence between continuous linear functions `𝕜ⁿ → E` and `Eⁿ`.
The spaces `𝕜ⁿ` and `Eⁿ` are represented as `ι → 𝕜` and `ι → E`, respectively,
where `ι` is a finite type. -/
def ContinuousLinearEquiv.piRing (ι : Type _) [Fintype ι] [DecidableEq ι] :
    ((ι → 𝕜) →L[𝕜] E) ≃L[𝕜] ι → E :=
  {
    LinearMap.toContinuousLinearMap.symm.trans
      (LinearEquiv.piRing 𝕜 E ι
        𝕜) with
    continuous_toFun := by
      refine' continuous_pi fun i => _
      exact (ContinuousLinearMap.apply 𝕜 E (Pi.single i 1)).Continuous
    continuous_invFun :=
      by
      simp_rw [LinearEquiv.invFun_eq_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm]
      change
        Continuous
          (linear_map.to_continuous_linear_map.to_linear_map.comp
            (LinearEquiv.piRing 𝕜 E ι 𝕜).symm.toLinearMap)
      apply AddMonoidHomClass.continuous_of_bound _ (Fintype.card ι : ℝ) fun g => _
      rw [← nsmul_eq_mul]
      apply op_norm_le_bound _ (nsmul_nonneg (norm_nonneg g) (Fintype.card ι)) fun t => _
      simp_rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply,
        LinearMap.coe_to_continuous_linear_map', LinearEquiv.piRing_symm_apply]
      apply le_trans (norm_sum_le _ _)
      rw [smul_mul_assoc]
      refine' Finset.sum_le_card_nsmul _ _ _ fun i hi => _
      rw [norm_smul, mul_comm]
      exact mul_le_mul (norm_le_pi_norm g i) (norm_le_pi_norm t i) (norm_nonneg _) (norm_nonneg g) }
#align continuous_linear_equiv.pi_ring ContinuousLinearEquiv.piRing
-/

/- warning: continuous_on_clm_apply -> continuousOn_clm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_on_clm_apply continuousOn_clm_applyₓ'. -/
/-- A family of continuous linear maps is continuous on `s` if all its applications are. -/
theorem continuousOn_clm_apply {X : Type _} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X → E →L[𝕜] F} {s : Set X} : ContinuousOn f s ↔ ∀ y, ContinuousOn (fun x => f x y) s :=
  by
  refine' ⟨fun h y => (ContinuousLinearMap.apply 𝕜 F y).Continuous.comp_continuousOn h, fun h => _⟩
  let d := finrank 𝕜 E
  have hd : d = finrank 𝕜 (Fin d → 𝕜) := (finrank_fin_fun 𝕜).symm
  let e₁ : E ≃L[𝕜] Fin d → 𝕜 := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ : (E →L[𝕜] F) ≃L[𝕜] Fin d → F :=
    (e₁.arrow_congr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.comp.left_id f, ← e₂.symm_comp_self]
  exact e₂.symm.continuous.comp_continuous_on (continuous_on_pi.mpr fun i => h _)
#align continuous_on_clm_apply continuousOn_clm_apply

/- warning: continuous_clm_apply -> continuous_clm_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_clm_apply continuous_clm_applyₓ'. -/
theorem continuous_clm_apply {X : Type _} [TopologicalSpace X] [FiniteDimensional 𝕜 E]
    {f : X → E →L[𝕜] F} : Continuous f ↔ ∀ y, Continuous fun x => f x y := by
  simp_rw [continuous_iff_continuousOn_univ, continuousOn_clm_apply]
#align continuous_clm_apply continuous_clm_apply

end CompleteField

section ProperField

variable (𝕜 : Type u) [NontriviallyNormedField 𝕜] (E : Type v) [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [ProperSpace 𝕜]

#print FiniteDimensional.proper /-
/-- Any finite-dimensional vector space over a proper field is proper.
We do not register this as an instance to avoid an instance loop when trying to prove the
properness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare the instance
explicitly when needed. -/
theorem FiniteDimensional.proper [FiniteDimensional 𝕜 E] : ProperSpace E :=
  by
  set e := ContinuousLinearEquiv.ofFinrankEq (@finrank_fin_fun 𝕜 _ _ (finrank 𝕜 E)).symm
  exact e.symm.antilipschitz.proper_space e.symm.continuous e.symm.surjective
#align finite_dimensional.proper FiniteDimensional.proper
-/

end ProperField

#print FiniteDimensional.proper_real /-
/- Over the real numbers, we can register the previous statement as an instance as it will not
cause problems in instance resolution since the properness of `ℝ` is already known. -/
instance (priority := 900) FiniteDimensional.proper_real (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] : ProperSpace E :=
  FiniteDimensional.proper ℝ E
#align finite_dimensional.proper_real FiniteDimensional.proper_real
-/

/- warning: exists_mem_frontier_inf_dist_compl_eq_dist -> exists_mem_frontier_infDist_compl_eq_dist is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] [_inst_3 : FiniteDimensional.{0, u1} Real E Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2)] {x : E} {s : Set.{u1} E}, (Membership.Mem.{u1, u1} E (Set.{u1} E) (Set.hasMem.{u1} E) x s) -> (Ne.{succ u1} (Set.{u1} E) s (Set.univ.{u1} E)) -> (Exists.{succ u1} E (fun (y : E) => Exists.{0} (Membership.Mem.{u1, u1} E (Set.{u1} E) (Set.hasMem.{u1} E) y (frontier.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) s)) (fun (H : Membership.Mem.{u1, u1} E (Set.{u1} E) (Set.hasMem.{u1} E) y (frontier.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) s)) => Eq.{1} Real (Metric.infDist.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)) x (HasCompl.compl.{u1} (Set.{u1} E) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} E) (Set.booleanAlgebra.{u1} E)) s)) (Dist.dist.{u1} E (PseudoMetricSpace.toHasDist.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) x y))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] [_inst_3 : FiniteDimensional.{0, u1} Real E Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2)] {x : E} {s : Set.{u1} E}, (Membership.mem.{u1, u1} E (Set.{u1} E) (Set.instMembershipSet.{u1} E) x s) -> (Ne.{succ u1} (Set.{u1} E) s (Set.univ.{u1} E)) -> (Exists.{succ u1} E (fun (y : E) => And (Membership.mem.{u1, u1} E (Set.{u1} E) (Set.instMembershipSet.{u1} E) y (frontier.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) s)) (Eq.{1} Real (Metric.infDist.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)) x (HasCompl.compl.{u1} (Set.{u1} E) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} E) (Set.instBooleanAlgebraSet.{u1} E)) s)) (Dist.dist.{u1} E (PseudoMetricSpace.toDist.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) x y))))
Case conversion may be inaccurate. Consider using '#align exists_mem_frontier_inf_dist_compl_eq_dist exists_mem_frontier_infDist_compl_eq_distₓ'. -/
/-- If `E` is a finite dimensional normed real vector space, `x : E`, and `s` is a neighborhood of
`x` that is not equal to the whole space, then there exists a point `y ∈ frontier s` at distance
`metric.inf_dist x sᶜ` from `x`. See also
`is_compact.exists_mem_frontier_inf_dist_compl_eq_dist`. -/
theorem exists_mem_frontier_infDist_compl_eq_dist {E : Type _} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {x : E} {s : Set E} (hx : x ∈ s) (hs : s ≠ univ) :
    ∃ y ∈ frontier s, Metric.infDist x (sᶜ) = dist x y :=
  by
  rcases Metric.exists_mem_closure_infDist_eq_dist (nonempty_compl.2 hs) x with ⟨y, hys, hyd⟩
  rw [closure_compl] at hys
  refine'
    ⟨y,
      ⟨Metric.closedBall_infDist_compl_subset_closure hx <| Metric.mem_closedBall.2 <| ge_of_eq _,
        hys⟩,
      hyd⟩
  rwa [dist_comm]
#align exists_mem_frontier_inf_dist_compl_eq_dist exists_mem_frontier_infDist_compl_eq_dist

/- warning: is_compact.exists_mem_frontier_inf_dist_compl_eq_dist -> IsCompact.exists_mem_frontier_infDist_compl_eq_dist is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] [_inst_3 : Nontrivial.{u1} E] {x : E} {K : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) K) -> (Membership.Mem.{u1, u1} E (Set.{u1} E) (Set.hasMem.{u1} E) x K) -> (Exists.{succ u1} E (fun (y : E) => Exists.{0} (Membership.Mem.{u1, u1} E (Set.{u1} E) (Set.hasMem.{u1} E) y (frontier.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) K)) (fun (H : Membership.Mem.{u1, u1} E (Set.{u1} E) (Set.hasMem.{u1} E) y (frontier.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) K)) => Eq.{1} Real (Metric.infDist.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)) x (HasCompl.compl.{u1} (Set.{u1} E) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} E) (Set.booleanAlgebra.{u1} E)) K)) (Dist.dist.{u1} E (PseudoMetricSpace.toHasDist.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) x y))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] [_inst_3 : Nontrivial.{u1} E] {x : E} {K : Set.{u1} E}, (IsCompact.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) K) -> (Membership.mem.{u1, u1} E (Set.{u1} E) (Set.instMembershipSet.{u1} E) x K) -> (Exists.{succ u1} E (fun (y : E) => And (Membership.mem.{u1, u1} E (Set.{u1} E) (Set.instMembershipSet.{u1} E) y (frontier.{u1} E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) K)) (Eq.{1} Real (Metric.infDist.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)) x (HasCompl.compl.{u1} (Set.{u1} E) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} E) (Set.instBooleanAlgebraSet.{u1} E)) K)) (Dist.dist.{u1} E (PseudoMetricSpace.toDist.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1))) x y))))
Case conversion may be inaccurate. Consider using '#align is_compact.exists_mem_frontier_inf_dist_compl_eq_dist IsCompact.exists_mem_frontier_infDist_compl_eq_distₓ'. -/
/-- If `K` is a compact set in a nontrivial real normed space and `x ∈ K`, then there exists a point
`y` of the boundary of `K` at distance `metric.inf_dist x Kᶜ` from `x`. See also
`exists_mem_frontier_inf_dist_compl_eq_dist`. -/
theorem IsCompact.exists_mem_frontier_infDist_compl_eq_dist {E : Type _} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] {x : E} {K : Set E} (hK : IsCompact K) (hx : x ∈ K) :
    ∃ y ∈ frontier K, Metric.infDist x (Kᶜ) = dist x y :=
  by
  obtain hx' | hx' : x ∈ interior K ∪ frontier K := by rw [← closure_eq_interior_union_frontier];
    exact subset_closure hx
  · rw [mem_interior_iff_mem_nhds, metric.nhds_basis_closed_ball.mem_iff] at hx'
    rcases hx' with ⟨r, hr₀, hrK⟩
    have : FiniteDimensional ℝ E :=
      finiteDimensional_of_isCompact_closedBall ℝ hr₀
        (isCompact_of_isClosed_subset hK Metric.isClosed_ball hrK)
    exact exists_mem_frontier_infDist_compl_eq_dist hx hK.ne_univ
  · refine' ⟨x, hx', _⟩
    rw [frontier_eq_closure_inter_closure] at hx'
    rw [Metric.infDist_zero_of_mem_closure hx'.2, dist_self]
#align is_compact.exists_mem_frontier_inf_dist_compl_eq_dist IsCompact.exists_mem_frontier_infDist_compl_eq_dist

/- warning: summable_norm_iff -> summable_norm_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} E] [_inst_2 : NormedSpace.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)] [_inst_3 : FiniteDimensional.{0, u2} Real E Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_1) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1) _inst_2)] {f : α -> E}, Iff (Summable.{0, u1} Real α Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f x))) (Summable.{u2, u1} E α (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))) f)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] [_inst_3 : FiniteDimensional.{0, u1} Real E Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2)] {f : α -> E}, Iff (Summable.{0, u2} Real α Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_1) (f x))) (Summable.{u1, u2} E α (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) f)
Case conversion may be inaccurate. Consider using '#align summable_norm_iff summable_norm_iffₓ'. -/
/-- In a finite dimensional vector space over `ℝ`, the series `∑ x, ‖f x‖` is unconditionally
summable if and only if the series `∑ x, f x` is unconditionally summable. One implication holds in
any complete normed space, while the other holds only in finite dimensional spaces. -/
theorem summable_norm_iff {α E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : α → E} : (Summable fun x => ‖f x‖) ↔ Summable f :=
  by
  refine' ⟨summable_of_summable_norm, fun hf => _⟩
  -- First we use a finite basis to reduce the problem to the case `E = fin N → ℝ`
  suffices ∀ {N : ℕ} {g : α → Fin N → ℝ}, Summable g → Summable fun x => ‖g x‖
    by
    obtain v := fin_basis ℝ E
    set e := v.equiv_funL
    have : Summable fun x => ‖e (f x)‖ := this (e.summable.2 hf)
    refine'
      summable_of_norm_bounded _ (this.mul_left ↑‖(e.symm : (Fin (finrank ℝ E) → ℝ) →L[ℝ] E)‖₊)
        fun i => _
    simpa using (e.symm : (Fin (finrank ℝ E) → ℝ) →L[ℝ] E).le_op_norm (e <| f i)
  clear! E
  -- Now we deal with `g : α → fin N → ℝ`
  intro N g hg
  have : ∀ i, Summable fun x => ‖g x i‖ := fun i => (Pi.summable.1 hg i).abs
  refine'
    summable_of_norm_bounded _ (summable_sum fun i (hi : i ∈ Finset.univ) => this i) fun x => _
  rw [norm_norm, pi_norm_le_iff_of_nonneg]
  · refine' fun i => Finset.single_le_sum (fun i hi => _) (Finset.mem_univ i)
    exact norm_nonneg (g x i)
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
#align summable_norm_iff summable_norm_iff

/- warning: summable_of_is_O' -> summable_of_isBigO' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} {F : Type.{u3}} [_inst_1 : NormedAddCommGroup.{u2} E] [_inst_2 : CompleteSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))] [_inst_3 : NormedAddCommGroup.{u3} F] [_inst_4 : NormedSpace.{0, u3} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_3)] [_inst_5 : FiniteDimensional.{0, u3} Real F Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_3) (NormedSpace.toModule.{0, u3} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_3) _inst_4)] {f : ι -> E} {g : ι -> F}, (Summable.{u3, u1} F ι (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_3)) (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_3)))) g) -> (Asymptotics.IsBigO.{u1, u2, u3} ι E F (NormedAddCommGroup.toHasNorm.{u2} E _inst_1) (NormedAddCommGroup.toHasNorm.{u3} F _inst_3) (Filter.cofinite.{u1} ι) f g) -> (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))) f)
but is expected to have type
  forall {ι : Type.{u3}} {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} E] [_inst_2 : CompleteSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))] [_inst_3 : NormedAddCommGroup.{u1} F] [_inst_4 : NormedSpace.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_3)] [_inst_5 : FiniteDimensional.{0, u1} Real F Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_3) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_3) _inst_4)] {f : ι -> E} {g : ι -> F}, (Summable.{u1, u3} F ι (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_3)) (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_3)))) g) -> (Asymptotics.IsBigO.{u3, u2, u1} ι E F (NormedAddCommGroup.toNorm.{u2} E _inst_1) (NormedAddCommGroup.toNorm.{u1} F _inst_3) (Filter.cofinite.{u3} ι) f g) -> (Summable.{u2, u3} E ι (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))) f)
Case conversion may be inaccurate. Consider using '#align summable_of_is_O' summable_of_isBigO'ₓ'. -/
theorem summable_of_isBigO' {ι E F : Type _} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : ι → E} {g : ι → F}
    (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  summable_of_isBigO (summable_norm_iff.mpr hg) h.norm_right
#align summable_of_is_O' summable_of_isBigO'

/- warning: summable_of_is_O_nat' -> summable_of_isBigO_nat' is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : CompleteSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))] [_inst_3 : NormedAddCommGroup.{u2} F] [_inst_4 : NormedSpace.{0, u2} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_3)] [_inst_5 : FiniteDimensional.{0, u2} Real F Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_3) (NormedSpace.toModule.{0, u2} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_3) _inst_4)] {f : Nat -> E} {g : Nat -> F}, (Summable.{u2, 0} F Nat (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_3)) (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_3)))) g) -> (Asymptotics.IsBigO.{0, u1, u2} Nat E F (NormedAddCommGroup.toHasNorm.{u1} E _inst_1) (NormedAddCommGroup.toHasNorm.{u2} F _inst_3) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) f g) -> (Summable.{u1, 0} E Nat (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) f)
but is expected to have type
  forall {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u2} E] [_inst_2 : CompleteSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))] [_inst_3 : NormedAddCommGroup.{u1} F] [_inst_4 : NormedSpace.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_3)] [_inst_5 : FiniteDimensional.{0, u1} Real F Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_3) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_3) _inst_4)] {f : Nat -> E} {g : Nat -> F}, (Summable.{u1, 0} F Nat (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_3)) (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_3)))) g) -> (Asymptotics.IsBigO.{0, u2, u1} Nat E F (NormedAddCommGroup.toNorm.{u2} E _inst_1) (NormedAddCommGroup.toNorm.{u1} F _inst_3) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) f g) -> (Summable.{u2, 0} E Nat (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))) f)
Case conversion may be inaccurate. Consider using '#align summable_of_is_O_nat' summable_of_isBigO_nat'ₓ'. -/
theorem summable_of_isBigO_nat' {E F : Type _} [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : ℕ → E} {g : ℕ → F}
    (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
  summable_of_isBigO_nat (summable_norm_iff.mpr hg) h.norm_right
#align summable_of_is_O_nat' summable_of_isBigO_nat'

/- warning: summable_of_is_equivalent -> summable_of_isEquivalent is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} E] [_inst_2 : NormedSpace.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)] [_inst_3 : FiniteDimensional.{0, u2} Real E Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_1) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1) _inst_2)] {f : ι -> E} {g : ι -> E}, (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))) g) -> (Asymptotics.IsEquivalent.{u1, u2} ι E _inst_1 (Filter.cofinite.{u1} ι) f g) -> (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))) f)
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] [_inst_3 : FiniteDimensional.{0, u1} Real E Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2)] {f : ι -> E} {g : ι -> E}, (Summable.{u1, u2} E ι (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) g) -> (Asymptotics.IsEquivalent.{u2, u1} ι E _inst_1 (Filter.cofinite.{u2} ι) f g) -> (Summable.{u1, u2} E ι (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) f)
Case conversion may be inaccurate. Consider using '#align summable_of_is_equivalent summable_of_isEquivalentₓ'. -/
theorem summable_of_isEquivalent {ι E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ι → E} {g : ι → E} (hg : Summable g) (h : f ~[cofinite] g) :
    Summable f :=
  hg.trans_sub (summable_of_isBigO' hg h.IsLittleO.IsBigO)
#align summable_of_is_equivalent summable_of_isEquivalent

#print summable_of_isEquivalent_nat /-
theorem summable_of_isEquivalent_nat {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℕ → E} {g : ℕ → E} (hg : Summable g) (h : f ~[atTop] g) :
    Summable f :=
  hg.trans_sub (summable_of_isBigO_nat' hg h.IsLittleO.IsBigO)
#align summable_of_is_equivalent_nat summable_of_isEquivalent_nat
-/

/- warning: is_equivalent.summable_iff -> IsEquivalent.summable_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {E : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} E] [_inst_2 : NormedSpace.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)] [_inst_3 : FiniteDimensional.{0, u2} Real E Real.divisionRing (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_1) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1) _inst_2)] {f : ι -> E} {g : ι -> E}, (Asymptotics.IsEquivalent.{u1, u2} ι E _inst_1 (Filter.cofinite.{u1} ι) f g) -> (Iff (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))) f) (Summable.{u2, u1} E ι (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_1)))) g))
but is expected to have type
  forall {ι : Type.{u2}} {E : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} E] [_inst_2 : NormedSpace.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)] [_inst_3 : FiniteDimensional.{0, u1} Real E Real.instDivisionRingReal (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1) (NormedSpace.toModule.{0, u1} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1) _inst_2)] {f : ι -> E} {g : ι -> E}, (Asymptotics.IsEquivalent.{u2, u1} ι E _inst_1 (Filter.cofinite.{u2} ι) f g) -> (Iff (Summable.{u1, u2} E ι (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) f) (Summable.{u1, u2} E ι (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_1)))) g))
Case conversion may be inaccurate. Consider using '#align is_equivalent.summable_iff IsEquivalent.summable_iffₓ'. -/
theorem IsEquivalent.summable_iff {ι E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ι → E} {g : ι → E} (h : f ~[cofinite] g) :
    Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_isEquivalent hf h.symm, fun hg => summable_of_isEquivalent hg h⟩
#align is_equivalent.summable_iff IsEquivalent.summable_iff

#print IsEquivalent.summable_iff_nat /-
theorem IsEquivalent.summable_iff_nat {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℕ → E} {g : ℕ → E} (h : f ~[atTop] g) : Summable f ↔ Summable g :=
  ⟨fun hf => summable_of_isEquivalent_nat hf h.symm, fun hg => summable_of_isEquivalent_nat hg h⟩
#align is_equivalent.summable_iff_nat IsEquivalent.summable_iff_nat
-/

