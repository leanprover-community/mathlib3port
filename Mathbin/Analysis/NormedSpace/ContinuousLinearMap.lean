/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo

! This file was ported from Lean 3 source module analysis.normed_space.continuous_linear_map
! leanprover-community/mathlib commit 9a48a083b390d9b84a71efbdc4e8dfa26a687104
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Basic

/-! # Constructions of continuous linear maps between (semi-)normed spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A fundamental fact about (semi-)linear maps between normed spaces over sensible fields is that
continuity and boundedness are equivalent conditions.  That is, for normed spaces `E`, `F`, a
`linear_map` `f : E →ₛₗ[σ] F` is the coercion of some `continuous_linear_map` `f' : E →SL[σ] F`, if
and only if there exists a bound `C` such that for all `x`, `‖f x‖ ≤ C * ‖x‖`.

We prove one direction in this file: `linear_map.mk_continuous`, boundedness implies continuity. The
other direction, `continuous_linear_map.bound`, is deferred to a later file, where the
strong operator topology on `E →SL[σ] F` is available, because it is natural to use
`continuous_linear_map.bound` to define a norm `⨆ x, ‖f x‖ / ‖x‖` on `E →SL[σ] F` and to show that
this is compatible with the strong operator topology.

This file also contains several corollaries of `linear_map.mk_continuous`: other "easy"
constructions of continuous linear maps between normed spaces.

This file is meant to be lightweight (it is imported by much of the analysis library); think twice
before adding imports!
-/


open Metric ContinuousLinearMap

open Set Real

open NNReal

variable {𝕜 𝕜₂ E F G : Type _}

variable [NormedField 𝕜] [NormedField 𝕜₂]

/-! # General constructions -/


section Seminormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜 G]

variable {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

/- warning: linear_map.mk_continuous -> LinearMap.mkContinuous is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.mk_continuous LinearMap.mkContinuousₓ'. -/
/-- Construct a continuous linear map from a linear map and a bound on this linear map.
The fact that the norm of the continuous linear map is then controlled is given in
`linear_map.mk_continuous_norm_le`. -/
def LinearMap.mkContinuous (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
  ⟨f, AddMonoidHomClass.continuous_of_bound f C h⟩
#align linear_map.mk_continuous LinearMap.mkContinuous

#print LinearMap.toContinuousLinearMap₁ /-
/-- Reinterpret a linear map `𝕜 →ₗ[𝕜] E` as a continuous linear map. This construction
is generalized to the case of any finite dimensional domain
in `linear_map.to_continuous_linear_map`. -/
def LinearMap.toContinuousLinearMap₁ (f : 𝕜 →ₗ[𝕜] E) : 𝕜 →L[𝕜] E :=
  f.mkContinuous ‖f 1‖ fun x =>
    le_of_eq <| by conv_lhs => rw [← mul_one x]; rw [← smul_eq_mul, f.map_smul, norm_smul, mul_comm]
#align linear_map.to_continuous_linear_map₁ LinearMap.toContinuousLinearMap₁
-/

/- warning: linear_map.mk_continuous_of_exists_bound -> LinearMap.mkContinuousOfExistsBound is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.mk_continuous_of_exists_bound LinearMap.mkContinuousOfExistsBoundₓ'. -/
/-- Construct a continuous linear map from a linear map and the existence of a bound on this linear
map. If you have an explicit bound, use `linear_map.mk_continuous` instead, as a norm estimate will
follow automatically in `linear_map.mk_continuous_norm_le`. -/
def LinearMap.mkContinuousOfExistsBound (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
  ⟨f,
    let ⟨C, hC⟩ := h
    AddMonoidHomClass.continuous_of_bound f C hC⟩
#align linear_map.mk_continuous_of_exists_bound LinearMap.mkContinuousOfExistsBound

/- warning: continuous_of_linear_of_boundₛₗ -> continuous_of_linear_of_boundₛₗ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_of_linear_of_boundₛₗ continuous_of_linear_of_boundₛₗₓ'. -/
theorem continuous_of_linear_of_boundₛₗ {f : E → F} (h_add : ∀ x y, f (x + y) = f x + f y)
    (h_smul : ∀ (c : 𝕜) (x), f (c • x) = σ c • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    Continuous f :=
  let φ : E →ₛₗ[σ] F :=
    { toFun := f
      map_add' := h_add
      map_smul' := h_smul }
  AddMonoidHomClass.continuous_of_bound φ C h_bound
#align continuous_of_linear_of_boundₛₗ continuous_of_linear_of_boundₛₗ

/- warning: continuous_of_linear_of_bound -> continuous_of_linear_of_bound is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_of_linear_of_bound continuous_of_linear_of_boundₓ'. -/
theorem continuous_of_linear_of_bound {f : E → G} (h_add : ∀ x y, f (x + y) = f x + f y)
    (h_smul : ∀ (c : 𝕜) (x), f (c • x) = c • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    Continuous f :=
  let φ : E →ₗ[𝕜] G :=
    { toFun := f
      map_add' := h_add
      map_smul' := h_smul }
  AddMonoidHomClass.continuous_of_bound φ C h_bound
#align continuous_of_linear_of_bound continuous_of_linear_of_bound

/- warning: linear_map.mk_continuous_coe -> LinearMap.mkContinuous_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.mk_continuous_coe LinearMap.mkContinuous_coeₓ'. -/
@[simp, norm_cast]
theorem LinearMap.mkContinuous_coe (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    (f.mkContinuous C h : E →ₛₗ[σ] F) = f :=
  rfl
#align linear_map.mk_continuous_coe LinearMap.mkContinuous_coe

/- warning: linear_map.mk_continuous_apply -> LinearMap.mkContinuous_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.mk_continuous_apply LinearMap.mkContinuous_applyₓ'. -/
@[simp]
theorem LinearMap.mkContinuous_apply (C : ℝ) (h : ∀ x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
    f.mkContinuous C h x = f x :=
  rfl
#align linear_map.mk_continuous_apply LinearMap.mkContinuous_apply

/- warning: linear_map.mk_continuous_of_exists_bound_coe -> LinearMap.mkContinuousOfExistsBound_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.mk_continuous_of_exists_bound_coe LinearMap.mkContinuousOfExistsBound_coeₓ'. -/
@[simp, norm_cast]
theorem LinearMap.mkContinuousOfExistsBound_coe (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    (f.mkContinuousOfExistsBound h : E →ₛₗ[σ] F) = f :=
  rfl
#align linear_map.mk_continuous_of_exists_bound_coe LinearMap.mkContinuousOfExistsBound_coe

/- warning: linear_map.mk_continuous_of_exists_bound_apply -> LinearMap.mkContinuousOfExistsBound_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.mk_continuous_of_exists_bound_apply LinearMap.mkContinuousOfExistsBound_applyₓ'. -/
@[simp]
theorem LinearMap.mkContinuousOfExistsBound_apply (h : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
    f.mkContinuousOfExistsBound h x = f x :=
  rfl
#align linear_map.mk_continuous_of_exists_bound_apply LinearMap.mkContinuousOfExistsBound_apply

/- warning: linear_map.to_continuous_linear_map₁_coe -> LinearMap.toContinuousLinearMap₁_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_continuous_linear_map₁_coe LinearMap.toContinuousLinearMap₁_coeₓ'. -/
@[simp]
theorem LinearMap.toContinuousLinearMap₁_coe (f : 𝕜 →ₗ[𝕜] E) :
    (f.toContinuousLinearMap₁ : 𝕜 →ₗ[𝕜] E) = f :=
  rfl
#align linear_map.to_continuous_linear_map₁_coe LinearMap.toContinuousLinearMap₁_coe

/- warning: linear_map.to_continuous_linear_map₁_apply -> LinearMap.toContinuousLinearMap₁_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.to_continuous_linear_map₁_apply LinearMap.toContinuousLinearMap₁_applyₓ'. -/
@[simp]
theorem LinearMap.toContinuousLinearMap₁_apply (f : 𝕜 →ₗ[𝕜] E) (x) :
    f.toContinuousLinearMap₁ x = f x :=
  rfl
#align linear_map.to_continuous_linear_map₁_apply LinearMap.toContinuousLinearMap₁_apply

namespace ContinuousLinearMap

/- warning: continuous_linear_map.antilipschitz_of_bound -> ContinuousLinearMap.antilipschitz_of_bound is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.antilipschitz_of_bound ContinuousLinearMap.antilipschitz_of_boundₓ'. -/
theorem antilipschitz_of_bound (f : E →SL[σ] F) {K : ℝ≥0} (h : ∀ x, ‖x‖ ≤ K * ‖f x‖) :
    AntilipschitzWith K f :=
  AddMonoidHomClass.antilipschitz_of_bound _ h
#align continuous_linear_map.antilipschitz_of_bound ContinuousLinearMap.antilipschitz_of_bound

/- warning: continuous_linear_map.bound_of_antilipschitz -> ContinuousLinearMap.bound_of_antilipschitz is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.bound_of_antilipschitz ContinuousLinearMap.bound_of_antilipschitzₓ'. -/
theorem bound_of_antilipschitz (f : E →SL[σ] F) {K : ℝ≥0} (h : AntilipschitzWith K f) (x) :
    ‖x‖ ≤ K * ‖f x‖ :=
  AddMonoidHomClass.bound_of_antilipschitz _ h x
#align continuous_linear_map.bound_of_antilipschitz ContinuousLinearMap.bound_of_antilipschitz

end ContinuousLinearMap

section

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ σ₂₁] [RingHomInvPair σ₂₁ σ]

include σ₂₁

/- warning: linear_equiv.to_continuous_linear_equiv_of_bounds -> LinearEquiv.toContinuousLinearEquivOfBounds is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.to_continuous_linear_equiv_of_bounds LinearEquiv.toContinuousLinearEquivOfBoundsₓ'. -/
/-- Construct a continuous linear equivalence from a linear equivalence together with
bounds in both directions. -/
def LinearEquiv.toContinuousLinearEquivOfBounds (e : E ≃ₛₗ[σ] F) (C_to C_inv : ℝ)
    (h_to : ∀ x, ‖e x‖ ≤ C_to * ‖x‖) (h_inv : ∀ x : F, ‖e.symm x‖ ≤ C_inv * ‖x‖) : E ≃SL[σ] F
    where
  toLinearEquiv := e
  continuous_toFun := AddMonoidHomClass.continuous_of_bound e C_to h_to
  continuous_invFun := AddMonoidHomClass.continuous_of_bound e.symm C_inv h_inv
#align linear_equiv.to_continuous_linear_equiv_of_bounds LinearEquiv.toContinuousLinearEquivOfBounds

end

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]

variable {σ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ] F) (x y z : E)

/- warning: continuous_linear_map.uniform_embedding_of_bound -> ContinuousLinearMap.uniformEmbedding_of_bound is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.uniform_embedding_of_bound ContinuousLinearMap.uniformEmbedding_of_boundₓ'. -/
theorem ContinuousLinearMap.uniformEmbedding_of_bound {K : ℝ≥0} (hf : ∀ x, ‖x‖ ≤ K * ‖f x‖) :
    UniformEmbedding f :=
  (AddMonoidHomClass.antilipschitz_of_bound f hf).UniformEmbedding f.UniformContinuous
#align continuous_linear_map.uniform_embedding_of_bound ContinuousLinearMap.uniformEmbedding_of_bound

end Normed

/-! ## Homotheties -/


section Seminormed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]

variable {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

/- warning: continuous_linear_map.of_homothety -> ContinuousLinearMap.ofHomothety is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.of_homothety ContinuousLinearMap.ofHomothetyₓ'. -/
/-- A (semi-)linear map which is a homothety is a continuous linear map.
    Since the field `𝕜` need not have `ℝ` as a subfield, this theorem is not directly deducible from
    the corresponding theorem about isometries plus a theorem about scalar multiplication.  Likewise
    for the other theorems about homotheties in this file.
 -/
def ContinuousLinearMap.ofHomothety (f : E →ₛₗ[σ] F) (a : ℝ) (hf : ∀ x, ‖f x‖ = a * ‖x‖) :
    E →SL[σ] F :=
  f.mkContinuous a fun x => le_of_eq (hf x)
#align continuous_linear_map.of_homothety ContinuousLinearMap.ofHomothety

variable {σ₂₁ : 𝕜₂ →+* 𝕜} [RingHomInvPair σ σ₂₁] [RingHomInvPair σ₂₁ σ]

include σ₂₁

/- warning: continuous_linear_equiv.homothety_inverse -> ContinuousLinearEquiv.homothety_inverse is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.homothety_inverse ContinuousLinearEquiv.homothety_inverseₓ'. -/
theorem ContinuousLinearEquiv.homothety_inverse (a : ℝ) (ha : 0 < a) (f : E ≃ₛₗ[σ] F) :
    (∀ x : E, ‖f x‖ = a * ‖x‖) → ∀ y : F, ‖f.symm y‖ = a⁻¹ * ‖y‖ :=
  by
  intro hf y
  calc
    ‖f.symm y‖ = a⁻¹ * (a * ‖f.symm y‖) := _
    _ = a⁻¹ * ‖f (f.symm y)‖ := by rw [hf]
    _ = a⁻¹ * ‖y‖ := by simp
    
  rw [← mul_assoc, inv_mul_cancel (ne_of_lt ha).symm, one_mul]
#align continuous_linear_equiv.homothety_inverse ContinuousLinearEquiv.homothety_inverse

/- warning: continuous_linear_equiv.of_homothety -> ContinuousLinearEquiv.ofHomothety is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.of_homothety ContinuousLinearEquiv.ofHomothetyₓ'. -/
/-- A linear equivalence which is a homothety is a continuous linear equivalence. -/
noncomputable def ContinuousLinearEquiv.ofHomothety (f : E ≃ₛₗ[σ] F) (a : ℝ) (ha : 0 < a)
    (hf : ∀ x, ‖f x‖ = a * ‖x‖) : E ≃SL[σ] F :=
  LinearEquiv.toContinuousLinearEquivOfBounds f a a⁻¹ (fun x => (hf x).le) fun x =>
    (ContinuousLinearEquiv.homothety_inverse a ha f hf x).le
#align continuous_linear_equiv.of_homothety ContinuousLinearEquiv.ofHomothety

end Seminormed

/-! ## The span of a single vector -/


section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace ContinuousLinearMap

variable (𝕜)

/- warning: continuous_linear_map.to_span_singleton_homothety -> ContinuousLinearMap.toSpanSingleton_homothety is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : NormedField.{u1} 𝕜] [_inst_3 : SeminormedAddCommGroup.{u2} E] [_inst_4 : NormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_3] (x : E) (c : 𝕜), Eq.{1} Real (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_3) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LinearMap.{u1, u1, u1, u2} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) 𝕜 E (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (Semiring.toModule.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 _inst_3 _inst_4)) (fun (_x : LinearMap.{u1, u1, u1, u2} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))))) 𝕜 E (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (Semiring.toModule.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 _inst_3 _inst_4)) => 𝕜 -> E) (LinearMap.hasCoeToFun.{u1, u1, u1, u2} 𝕜 𝕜 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (Semiring.toModule.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 _inst_3 _inst_4) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1))))))) (LinearMap.toSpanSingleton.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 _inst_3 _inst_4) x) c)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_3) x) (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 _inst_1) c))
but is expected to have type
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : NormedField.{u1} 𝕜] [_inst_3 : SeminormedAddCommGroup.{u2} E] [_inst_4 : NormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_3] (x : E) (c : 𝕜), Eq.{1} Real (Norm.norm.{u2} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : 𝕜) => E) c) (SeminormedAddCommGroup.toNorm.{u2} ((fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : 𝕜) => E) c) _inst_3) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (LinearMap.{u1, u1, u1, u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))) (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))))) 𝕜 E (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (Semiring.toModule.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 _inst_3 _inst_4)) 𝕜 (fun (_x : 𝕜) => (fun (x._@.Mathlib.Algebra.Module.LinearMap._hyg.6193 : 𝕜) => E) _x) (LinearMap.instFunLikeLinearMap.{u1, u1, u1, u2} 𝕜 𝕜 𝕜 E (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))) (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (Semiring.toModule.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))))) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 _inst_3 _inst_4) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1))))))) (LinearMap.toSpanSingleton.{u1, u2} 𝕜 E (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_3)) (NormedSpace.toModule.{u1, u2} 𝕜 E _inst_1 _inst_3 _inst_4) x) c)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u2} E (SeminormedAddCommGroup.toNorm.{u2} E _inst_3) x) (Norm.norm.{u1} 𝕜 (NormedField.toNorm.{u1} 𝕜 _inst_1) c))
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.to_span_singleton_homothety ContinuousLinearMap.toSpanSingleton_homothetyₓ'. -/
theorem toSpanSingleton_homothety (x : E) (c : 𝕜) :
    ‖LinearMap.toSpanSingleton 𝕜 E x c‖ = ‖x‖ * ‖c‖ := by rw [mul_comm]; exact norm_smul _ _
#align continuous_linear_map.to_span_singleton_homothety ContinuousLinearMap.toSpanSingleton_homothety

#print ContinuousLinearMap.toSpanSingleton /-
/-- Given an element `x` of a normed space `E` over a field `𝕜`, the natural continuous
    linear map from `𝕜` to `E` by taking multiples of `x`.-/
def toSpanSingleton (x : E) : 𝕜 →L[𝕜] E :=
  ofHomothety (LinearMap.toSpanSingleton 𝕜 E x) ‖x‖ (toSpanSingleton_homothety 𝕜 x)
#align continuous_linear_map.to_span_singleton ContinuousLinearMap.toSpanSingleton
-/

/- warning: continuous_linear_map.to_span_singleton_apply -> ContinuousLinearMap.toSpanSingleton_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.to_span_singleton_apply ContinuousLinearMap.toSpanSingleton_applyₓ'. -/
theorem toSpanSingleton_apply (x : E) (r : 𝕜) : toSpanSingleton 𝕜 x r = r • x := by
  simp [to_span_singleton, of_homothety, LinearMap.toSpanSingleton]
#align continuous_linear_map.to_span_singleton_apply ContinuousLinearMap.toSpanSingleton_apply

/- warning: continuous_linear_map.to_span_singleton_add -> ContinuousLinearMap.toSpanSingleton_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.to_span_singleton_add ContinuousLinearMap.toSpanSingleton_addₓ'. -/
theorem toSpanSingleton_add (x y : E) :
    toSpanSingleton 𝕜 (x + y) = toSpanSingleton 𝕜 x + toSpanSingleton 𝕜 y := by ext1;
  simp [to_span_singleton_apply]
#align continuous_linear_map.to_span_singleton_add ContinuousLinearMap.toSpanSingleton_add

#print ContinuousLinearMap.toSpanSingleton_smul' /-
theorem toSpanSingleton_smul' (𝕜') [NormedField 𝕜'] [NormedSpace 𝕜' E] [SMulCommClass 𝕜 𝕜' E]
    (c : 𝕜') (x : E) : toSpanSingleton 𝕜 (c • x) = c • toSpanSingleton 𝕜 x := by ext1;
  rw [to_span_singleton_apply, smul_apply, to_span_singleton_apply, smul_comm]
#align continuous_linear_map.to_span_singleton_smul' ContinuousLinearMap.toSpanSingleton_smul'
-/

/- warning: continuous_linear_map.to_span_singleton_smul -> ContinuousLinearMap.toSpanSingleton_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.to_span_singleton_smul ContinuousLinearMap.toSpanSingleton_smulₓ'. -/
theorem toSpanSingleton_smul (c : 𝕜) (x : E) :
    toSpanSingleton 𝕜 (c • x) = c • toSpanSingleton 𝕜 x :=
  toSpanSingleton_smul' 𝕜 𝕜 c x
#align continuous_linear_map.to_span_singleton_smul ContinuousLinearMap.toSpanSingleton_smul

end ContinuousLinearMap

section

namespace ContinuousLinearEquiv

variable (𝕜)

/- warning: continuous_linear_equiv.to_span_nonzero_singleton_homothety -> ContinuousLinearEquiv.toSpanNonzeroSingleton_homothety is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.to_span_nonzero_singleton_homothety ContinuousLinearEquiv.toSpanNonzeroSingleton_homothetyₓ'. -/
theorem toSpanNonzeroSingleton_homothety (x : E) (h : x ≠ 0) (c : 𝕜) :
    ‖LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h c‖ = ‖x‖ * ‖c‖ :=
  ContinuousLinearMap.toSpanSingleton_homothety _ _ _
#align continuous_linear_equiv.to_span_nonzero_singleton_homothety ContinuousLinearEquiv.toSpanNonzeroSingleton_homothety

end ContinuousLinearEquiv

end

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace ContinuousLinearEquiv

variable (𝕜)

/- warning: continuous_linear_equiv.to_span_nonzero_singleton -> ContinuousLinearEquiv.toSpanNonzeroSingleton is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.to_span_nonzero_singleton ContinuousLinearEquiv.toSpanNonzeroSingletonₓ'. -/
/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural
    continuous linear equivalence from `E₁` to the span of `x`.-/
noncomputable def toSpanNonzeroSingleton (x : E) (h : x ≠ 0) : 𝕜 ≃L[𝕜] 𝕜 ∙ x :=
  ofHomothety (LinearEquiv.toSpanNonzeroSingleton 𝕜 E x h) ‖x‖ (norm_pos_iff.mpr h)
    (toSpanNonzeroSingleton_homothety 𝕜 x h)
#align continuous_linear_equiv.to_span_nonzero_singleton ContinuousLinearEquiv.toSpanNonzeroSingleton

/- warning: continuous_linear_equiv.coord -> ContinuousLinearEquiv.coord is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.coord ContinuousLinearEquiv.coordₓ'. -/
/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural continuous
    linear map from the span of `x` to `𝕜`.-/
noncomputable def coord (x : E) (h : x ≠ 0) : (𝕜 ∙ x) →L[𝕜] 𝕜 :=
  (toSpanNonzeroSingleton 𝕜 x h).symm
#align continuous_linear_equiv.coord ContinuousLinearEquiv.coord

/- warning: continuous_linear_equiv.coe_to_span_nonzero_singleton_symm -> ContinuousLinearEquiv.coe_toSpanNonzeroSingleton_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.coe_to_span_nonzero_singleton_symm ContinuousLinearEquiv.coe_toSpanNonzeroSingleton_symmₓ'. -/
@[simp]
theorem coe_toSpanNonzeroSingleton_symm {x : E} (h : x ≠ 0) :
    ⇑(toSpanNonzeroSingleton 𝕜 x h).symm = coord 𝕜 x h :=
  rfl
#align continuous_linear_equiv.coe_to_span_nonzero_singleton_symm ContinuousLinearEquiv.coe_toSpanNonzeroSingleton_symm

/- warning: continuous_linear_equiv.coord_to_span_nonzero_singleton -> ContinuousLinearEquiv.coord_toSpanNonzeroSingleton is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.coord_to_span_nonzero_singleton ContinuousLinearEquiv.coord_toSpanNonzeroSingletonₓ'. -/
@[simp]
theorem coord_toSpanNonzeroSingleton {x : E} (h : x ≠ 0) (c : 𝕜) :
    coord 𝕜 x h (toSpanNonzeroSingleton 𝕜 x h c) = c :=
  (toSpanNonzeroSingleton 𝕜 x h).symm_apply_apply c
#align continuous_linear_equiv.coord_to_span_nonzero_singleton ContinuousLinearEquiv.coord_toSpanNonzeroSingleton

/- warning: continuous_linear_equiv.to_span_nonzero_singleton_coord -> ContinuousLinearEquiv.toSpanNonzeroSingleton_coord is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.to_span_nonzero_singleton_coord ContinuousLinearEquiv.toSpanNonzeroSingleton_coordₓ'. -/
@[simp]
theorem toSpanNonzeroSingleton_coord {x : E} (h : x ≠ 0) (y : 𝕜 ∙ x) :
    toSpanNonzeroSingleton 𝕜 x h (coord 𝕜 x h y) = y :=
  (toSpanNonzeroSingleton 𝕜 x h).apply_symm_apply y
#align continuous_linear_equiv.to_span_nonzero_singleton_coord ContinuousLinearEquiv.toSpanNonzeroSingleton_coord

/- warning: continuous_linear_equiv.coord_self -> ContinuousLinearEquiv.coord_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.coord_self ContinuousLinearEquiv.coord_selfₓ'. -/
@[simp]
theorem coord_self (x : E) (h : x ≠ 0) :
    (coord 𝕜 x h) (⟨x, Submodule.mem_span_singleton_self x⟩ : 𝕜 ∙ x) = 1 :=
  LinearEquiv.coord_self 𝕜 E x h
#align continuous_linear_equiv.coord_self ContinuousLinearEquiv.coord_self

end ContinuousLinearEquiv

end Normed

