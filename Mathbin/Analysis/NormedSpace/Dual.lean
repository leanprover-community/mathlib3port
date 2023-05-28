/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module analysis.normed_space.dual
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.HahnBanach.Extension
import Mathbin.Analysis.NormedSpace.IsROrC
import Mathbin.Analysis.LocallyConvex.Polar

/-!
# The topological dual of a normed space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the topological dual `normed_space.dual` of a normed space, and the
continuous linear map `normed_space.inclusion_in_double_dual` from a normed space into its double
dual.

For base field `𝕜 = ℝ` or `𝕜 = ℂ`, this map is actually an isometric embedding; we provide a
version `normed_space.inclusion_in_double_dual_li` of the map which is of type a bundled linear
isometric embedding, `E →ₗᵢ[𝕜] (dual 𝕜 (dual 𝕜 E))`.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `seminormed_add_comm_group` and we specialize to `normed_add_comm_group` when needed.

## Main definitions

* `inclusion_in_double_dual` and `inclusion_in_double_dual_li` are the inclusion of a normed space
  in its double dual, considered as a bounded linear map and as a linear isometry, respectively.
* `polar 𝕜 s` is the subset of `dual 𝕜 E` consisting of those functionals `x'` for which
  `‖x' z‖ ≤ 1` for every `z ∈ s`.

## Tags

dual
-/


noncomputable section

open Classical Topology

universe u v

namespace NormedSpace

section General

variable (𝕜 : Type _) [NontriviallyNormedField 𝕜]

variable (E : Type _) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (F : Type _) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler normed_space[normed_space] 𝕜 -/
#print NormedSpace.Dual /-
/-- The topological dual of a seminormed space `E`. -/
def Dual :=
  E →L[𝕜] 𝕜 deriving Inhabited, SeminormedAddCommGroup,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler normed_space[normed_space] 𝕜»
#align normed_space.dual NormedSpace.Dual
-/

instance : ContinuousLinearMapClass (Dual 𝕜 E) 𝕜 E 𝕜 :=
  ContinuousLinearMap.continuousSemilinearMapClass

instance : CoeFun (Dual 𝕜 E) fun _ => E → 𝕜 :=
  ContinuousLinearMap.toFun

instance : NormedAddCommGroup (Dual 𝕜 F) :=
  ContinuousLinearMap.toNormedAddCommGroup

instance [FiniteDimensional 𝕜 E] : FiniteDimensional 𝕜 (Dual 𝕜 E) :=
  ContinuousLinearMap.finiteDimensional

#print NormedSpace.inclusionInDoubleDual /-
/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusionInDoubleDual : E →L[𝕜] Dual 𝕜 (Dual 𝕜 E) :=
  ContinuousLinearMap.apply 𝕜 𝕜
#align normed_space.inclusion_in_double_dual NormedSpace.inclusionInDoubleDual
-/

/- warning: normed_space.dual_def -> NormedSpace.dual_def is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.dual_def NormedSpace.dual_defₓ'. -/
@[simp]
theorem dual_def (x : E) (f : Dual 𝕜 E) : inclusionInDoubleDual 𝕜 E x f = f x :=
  rfl
#align normed_space.dual_def NormedSpace.dual_def

/- warning: normed_space.inclusion_in_double_dual_norm_eq -> NormedSpace.inclusionInDoubleDual_norm_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.inclusion_in_double_dual_norm_eq NormedSpace.inclusionInDoubleDual_norm_eqₓ'. -/
theorem inclusionInDoubleDual_norm_eq :
    ‖inclusionInDoubleDual 𝕜 E‖ = ‖ContinuousLinearMap.id 𝕜 (Dual 𝕜 E)‖ :=
  ContinuousLinearMap.op_norm_flip _
#align normed_space.inclusion_in_double_dual_norm_eq NormedSpace.inclusionInDoubleDual_norm_eq

/- warning: normed_space.inclusion_in_double_dual_norm_le -> NormedSpace.inclusionInDoubleDual_norm_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.inclusion_in_double_dual_norm_le NormedSpace.inclusionInDoubleDual_norm_leₓ'. -/
theorem inclusionInDoubleDual_norm_le : ‖inclusionInDoubleDual 𝕜 E‖ ≤ 1 := by
  rw [inclusion_in_double_dual_norm_eq]; exact ContinuousLinearMap.norm_id_le
#align normed_space.inclusion_in_double_dual_norm_le NormedSpace.inclusionInDoubleDual_norm_le

/- warning: normed_space.double_dual_bound -> NormedSpace.double_dual_bound is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.double_dual_bound NormedSpace.double_dual_boundₓ'. -/
theorem double_dual_bound (x : E) : ‖(inclusionInDoubleDual 𝕜 E) x‖ ≤ ‖x‖ := by
  simpa using ContinuousLinearMap.le_of_op_norm_le _ (inclusion_in_double_dual_norm_le 𝕜 E) x
#align normed_space.double_dual_bound NormedSpace.double_dual_bound

#print NormedSpace.dualPairing /-
/-- The dual pairing as a bilinear form. -/
def dualPairing : Dual 𝕜 E →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLM 𝕜
#align normed_space.dual_pairing NormedSpace.dualPairing
-/

/- warning: normed_space.dual_pairing_apply -> NormedSpace.dualPairing_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.dual_pairing_apply NormedSpace.dualPairing_applyₓ'. -/
@[simp]
theorem dualPairing_apply {v : Dual 𝕜 E} {x : E} : dualPairing 𝕜 E v x = v x :=
  rfl
#align normed_space.dual_pairing_apply NormedSpace.dualPairing_apply

/- warning: normed_space.dual_pairing_separating_left -> NormedSpace.dualPairing_separatingLeft is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} 𝕜] (E : Type.{u2}) [_inst_2 : SeminormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) _inst_2], LinearMap.SeparatingLeft.{u1, u1, u1, max u2 u1, u2} 𝕜 𝕜 𝕜 (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) E (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))) (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))) (AddCommGroup.toAddCommMonoid.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toAddCommGroup.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.Dual.seminormedAddCommGroup.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3))) (NormedSpace.toModule.{u1, max u2 u1} 𝕜 (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedSpace.Dual.seminormedAddCommGroup.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.Dual.normedSpace.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)) (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) _inst_2 _inst_3) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (NormedSpace.dualPairing.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)
but is expected to have type
  forall (𝕜 : Type.{u2}) [_inst_1 : NontriviallyNormedField.{u2} 𝕜] (E : Type.{u1}) [_inst_2 : SeminormedAddCommGroup.{u1} E] [_inst_3 : NormedSpace.{u2, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) _inst_2], LinearMap.SeparatingLeft.{u2, u2, u2, max u2 u1, u1} 𝕜 𝕜 𝕜 (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) E (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1)))) (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1)))) (AddCommGroup.toAddCommMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toAddCommGroup.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.instSeminormedAddCommGroupDual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3))) (NormedSpace.toModule.{u2, max u2 u1} 𝕜 (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) (NormedSpace.instSeminormedAddCommGroupDual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.instNormedSpaceDualToNormedFieldInstSeminormedAddCommGroupDual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3)) (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1)))) (AddCommGroup.toAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) (NormedSpace.toModule.{u2, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) _inst_2 _inst_3) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1))))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1))))))) (NormedSpace.dualPairing.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3)
Case conversion may be inaccurate. Consider using '#align normed_space.dual_pairing_separating_left NormedSpace.dualPairing_separatingLeftₓ'. -/
theorem dualPairing_separatingLeft : (dualPairing 𝕜 E).SeparatingLeft :=
  by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ContinuousLinearMap.coe_injective
#align normed_space.dual_pairing_separating_left NormedSpace.dualPairing_separatingLeft

end General

section BidualIsometry

variable (𝕜 : Type v) [IsROrC 𝕜] {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/- warning: normed_space.norm_le_dual_bound -> NormedSpace.norm_le_dual_bound is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.norm_le_dual_bound NormedSpace.norm_le_dual_boundₓ'. -/
/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
    Compare `continuous_linear_map.op_norm_le_bound`. -/
theorem norm_le_dual_bound (x : E) {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ f : Dual 𝕜 E, ‖f x‖ ≤ M * ‖f‖) :
    ‖x‖ ≤ M := by
  classical
    by_cases h : x = 0
    · simp only [h, hMp, norm_zero]
    · obtain ⟨f, hf₁, hfx⟩ : ∃ f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f x = ‖x‖ := exists_dual_vector 𝕜 x h
      calc
        ‖x‖ = ‖(‖x‖ : 𝕜)‖ := is_R_or_C.norm_coe_norm.symm
        _ = ‖f x‖ := by rw [hfx]
        _ ≤ M * ‖f‖ := (hM f)
        _ = M := by rw [hf₁, mul_one]
        
#align normed_space.norm_le_dual_bound NormedSpace.norm_le_dual_bound

/- warning: normed_space.eq_zero_of_forall_dual_eq_zero -> NormedSpace.eq_zero_of_forall_dual_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.eq_zero_of_forall_dual_eq_zero NormedSpace.eq_zero_of_forall_dual_eq_zeroₓ'. -/
theorem eq_zero_of_forall_dual_eq_zero {x : E} (h : ∀ f : Dual 𝕜 E, f x = (0 : 𝕜)) : x = 0 :=
  norm_le_zero_iff.mp (norm_le_dual_bound 𝕜 x le_rfl fun f => by simp [h f])
#align normed_space.eq_zero_of_forall_dual_eq_zero NormedSpace.eq_zero_of_forall_dual_eq_zero

/- warning: normed_space.eq_zero_iff_forall_dual_eq_zero -> NormedSpace.eq_zero_iff_forall_dual_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.eq_zero_iff_forall_dual_eq_zero NormedSpace.eq_zero_iff_forall_dual_eq_zeroₓ'. -/
theorem eq_zero_iff_forall_dual_eq_zero (x : E) : x = 0 ↔ ∀ g : Dual 𝕜 E, g x = 0 :=
  ⟨fun hx => by simp [hx], fun h => eq_zero_of_forall_dual_eq_zero 𝕜 h⟩
#align normed_space.eq_zero_iff_forall_dual_eq_zero NormedSpace.eq_zero_iff_forall_dual_eq_zero

/- warning: normed_space.eq_iff_forall_dual_eq -> NormedSpace.eq_iff_forall_dual_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.eq_iff_forall_dual_eq NormedSpace.eq_iff_forall_dual_eqₓ'. -/
/-- See also `geometric_hahn_banach_point_point`. -/
theorem eq_iff_forall_dual_eq {x y : E} : x = y ↔ ∀ g : Dual 𝕜 E, g x = g y :=
  by
  rw [← sub_eq_zero, eq_zero_iff_forall_dual_eq_zero 𝕜 (x - y)]
  simp [sub_eq_zero]
#align normed_space.eq_iff_forall_dual_eq NormedSpace.eq_iff_forall_dual_eq

#print NormedSpace.inclusionInDoubleDualLi /-
/-- The inclusion of a normed space in its double dual is an isometry onto its image.-/
def inclusionInDoubleDualLi : E →ₗᵢ[𝕜] Dual 𝕜 (Dual 𝕜 E) :=
  { inclusionInDoubleDual 𝕜 E with
    norm_map' := by
      intro x
      apply le_antisymm
      · exact double_dual_bound 𝕜 E x
      rw [ContinuousLinearMap.norm_def]
      refine' le_csInf ContinuousLinearMap.bounds_nonempty _
      rintro c ⟨hc1, hc2⟩
      exact norm_le_dual_bound 𝕜 x hc1 hc2 }
#align normed_space.inclusion_in_double_dual_li NormedSpace.inclusionInDoubleDualLi
-/

end BidualIsometry

section PolarSets

open Metric Set NormedSpace

#print NormedSpace.polar /-
/-- Given a subset `s` in a normed space `E` (over a field `𝕜`), the polar
`polar 𝕜 s` is the subset of `dual 𝕜 E` consisting of those functionals which
evaluate to something of norm at most one at all points `z ∈ s`. -/
def polar (𝕜 : Type _) [NontriviallyNormedField 𝕜] {E : Type _} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] : Set E → Set (Dual 𝕜 E) :=
  (dualPairing 𝕜 E).flip.polar
#align normed_space.polar NormedSpace.polar
-/

variable (𝕜 : Type _) [NontriviallyNormedField 𝕜]

variable {E : Type _} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/- warning: normed_space.mem_polar_iff -> NormedSpace.mem_polar_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.mem_polar_iff NormedSpace.mem_polar_iffₓ'. -/
theorem mem_polar_iff {x' : Dual 𝕜 E} (s : Set E) : x' ∈ polar 𝕜 s ↔ ∀ z ∈ s, ‖x' z‖ ≤ 1 :=
  Iff.rfl
#align normed_space.mem_polar_iff NormedSpace.mem_polar_iff

/- warning: normed_space.polar_univ -> NormedSpace.polar_univ is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) _inst_2], Eq.{succ (max u2 u1)} (Set.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)) (NormedSpace.polar.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3 (Set.univ.{u2} E)) (Singleton.singleton.{max u2 u1, max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (Set.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)) (Set.hasSingleton.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)) (OfNat.ofNat.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) 0 (OfNat.mk.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) 0 (Zero.zero.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (AddZeroClass.toHasZero.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (AddMonoid.toAddZeroClass.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SubNegMonoid.toAddMonoid.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (AddGroup.toSubNegMonoid.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddGroup.toAddGroup.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toSeminormedAddGroup.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.Dual.seminormedAddCommGroup.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)))))))))))
but is expected to have type
  forall (𝕜 : Type.{u2}) [_inst_1 : NontriviallyNormedField.{u2} 𝕜] {E : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} E] [_inst_3 : NormedSpace.{u2, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) _inst_2], Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3)) (NormedSpace.polar.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 (Set.univ.{u1} E)) (Singleton.singleton.{max u2 u1, max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (Set.{max u1 u2} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3)) (Set.instSingletonSet.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3)) (OfNat.ofNat.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) 0 (Zero.toOfNat0.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (NegZeroClass.toZero.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SubNegZeroMonoid.toNegZeroClass.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SubtractionMonoid.toSubNegZeroMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SubtractionCommMonoid.toSubtractionMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (AddCommGroup.toDivisionAddCommMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toAddCommGroup.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.instSeminormedAddCommGroupDual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3))))))))))
Case conversion may be inaccurate. Consider using '#align normed_space.polar_univ NormedSpace.polar_univₓ'. -/
@[simp]
theorem polar_univ : polar 𝕜 (univ : Set E) = {(0 : dual 𝕜 E)} :=
  (dualPairing 𝕜 E).flip.polar_univ
    (LinearMap.flip_separatingRight.mpr (dualPairing_separatingLeft 𝕜 E))
#align normed_space.polar_univ NormedSpace.polar_univ

#print NormedSpace.isClosed_polar /-
theorem isClosed_polar (s : Set E) : IsClosed (polar 𝕜 s) :=
  by
  dsimp only [NormedSpace.polar]
  simp only [LinearMap.polar_eq_iInter, LinearMap.flip_apply]
  refine' isClosed_biInter fun z hz => _
  exact is_closed_Iic.preimage (ContinuousLinearMap.apply 𝕜 𝕜 z).Continuous.norm
#align normed_space.is_closed_polar NormedSpace.isClosed_polar
-/

#print NormedSpace.polar_closure /-
@[simp]
theorem polar_closure (s : Set E) : polar 𝕜 (closure s) = polar 𝕜 s :=
  ((dualPairing 𝕜 E).flip.polar_antitone subset_closure).antisymm <|
    (dualPairing 𝕜 E).flip.polar_gc.l_le <|
      closure_minimal ((dualPairing 𝕜 E).flip.polar_gc.le_u_l s) <| by
        simpa [LinearMap.flip_flip] using
          (is_closed_polar _ _).Preimage (inclusion_in_double_dual 𝕜 E).Continuous
#align normed_space.polar_closure NormedSpace.polar_closure
-/

variable {𝕜}

/- warning: normed_space.smul_mem_polar -> NormedSpace.smul_mem_polar is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_space.smul_mem_polar NormedSpace.smul_mem_polarₓ'. -/
/-- If `x'` is a dual element such that the norms `‖x' z‖` are bounded for `z ∈ s`, then a
small scalar multiple of `x'` is in `polar 𝕜 s`. -/
theorem smul_mem_polar {s : Set E} {x' : Dual 𝕜 E} {c : 𝕜} (hc : ∀ z, z ∈ s → ‖x' z‖ ≤ ‖c‖) :
    c⁻¹ • x' ∈ polar 𝕜 s := by
  by_cases c_zero : c = 0;
  · simp only [c_zero, inv_zero, zero_smul]
    exact (dual_pairing 𝕜 E).flip.zero_mem_polar _
  have eq : ∀ z, ‖c⁻¹ • x' z‖ = ‖c⁻¹‖ * ‖x' z‖ := fun z => norm_smul c⁻¹ _
  have le : ∀ z, z ∈ s → ‖c⁻¹ • x' z‖ ≤ ‖c⁻¹‖ * ‖c‖ :=
    by
    intro z hzs
    rw [Eq z]
    apply mul_le_mul (le_of_eq rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _)
  have cancel : ‖c⁻¹‖ * ‖c‖ = 1 := by
    simp only [c_zero, norm_eq_zero, Ne.def, not_false_iff, inv_mul_cancel, norm_inv]
  rwa [cancel] at le
#align normed_space.smul_mem_polar NormedSpace.smul_mem_polar

/- warning: normed_space.polar_ball_subset_closed_ball_div -> NormedSpace.polar_ball_subset_closedBall_div is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) _inst_2] {c : 𝕜}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) c)) -> (forall {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)) (Set.hasSubset.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)) (NormedSpace.polar.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3 (Metric.ball.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_2) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_2))))))))) r)) (Metric.closedBall.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toPseudoMetricSpace.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.Dual.seminormedAddCommGroup.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)) (OfNat.ofNat.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) 0 (OfNat.mk.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) 0 (Zero.zero.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (AddZeroClass.toHasZero.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (AddMonoid.toAddZeroClass.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SubNegMonoid.toAddMonoid.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (AddGroup.toSubNegMonoid.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddGroup.toAddGroup.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toSeminormedAddGroup.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.Dual.seminormedAddCommGroup.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)))))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) c) r))))
but is expected to have type
  forall {𝕜 : Type.{u2}} [_inst_1 : NontriviallyNormedField.{u2} 𝕜] {E : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} E] [_inst_3 : NormedSpace.{u2, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) _inst_2] {c : 𝕜}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1)) c)) -> (forall {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (HasSubset.Subset.{max u2 u1} (Set.{max u1 u2} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3)) (Set.instHasSubsetSet.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3)) (NormedSpace.polar.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 (Metric.ball.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_2) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))))) r)) (Metric.closedBall.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toPseudoMetricSpace.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.instSeminormedAddCommGroupDual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3)) (OfNat.ofNat.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) 0 (Zero.toOfNat0.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (NegZeroClass.toZero.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SubNegZeroMonoid.toNegZeroClass.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SubtractionMonoid.toSubNegZeroMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SubtractionCommMonoid.toSubtractionMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (AddCommGroup.toDivisionAddCommMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toAddCommGroup.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.instSeminormedAddCommGroupDual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3))))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1)) c) r))))
Case conversion may be inaccurate. Consider using '#align normed_space.polar_ball_subset_closed_ball_div NormedSpace.polar_ball_subset_closedBall_divₓ'. -/
theorem polar_ball_subset_closedBall_div {c : 𝕜} (hc : 1 < ‖c‖) {r : ℝ} (hr : 0 < r) :
    polar 𝕜 (ball (0 : E) r) ⊆ closedBall (0 : Dual 𝕜 E) (‖c‖ / r) :=
  by
  intro x' hx'
  rw [mem_polar_iff] at hx'
  simp only [polar, mem_set_of_eq, mem_closedBall_zero_iff, mem_ball_zero_iff] at *
  have hcr : 0 < ‖c‖ / r := div_pos (zero_lt_one.trans hc) hr
  refine' ContinuousLinearMap.op_norm_le_of_shell hr hcr.le hc fun x h₁ h₂ => _
  calc
    ‖x' x‖ ≤ 1 := hx' _ h₂
    _ ≤ ‖c‖ / r * ‖x‖ := (inv_pos_le_iff_one_le_mul' hcr).1 (by rwa [inv_div])
    
#align normed_space.polar_ball_subset_closed_ball_div NormedSpace.polar_ball_subset_closedBall_div

variable (𝕜)

/- warning: normed_space.closed_ball_inv_subset_polar_closed_ball -> NormedSpace.closedBall_inv_subset_polar_closedBall is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) _inst_2] {r : Real}, HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)) (Set.hasSubset.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)) (Metric.closedBall.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toPseudoMetricSpace.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.Dual.seminormedAddCommGroup.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)) (OfNat.ofNat.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) 0 (OfNat.mk.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) 0 (Zero.zero.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (AddZeroClass.toHasZero.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (AddMonoid.toAddZeroClass.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SubNegMonoid.toAddMonoid.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (AddGroup.toSubNegMonoid.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddGroup.toAddGroup.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toSeminormedAddGroup.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.Dual.seminormedAddCommGroup.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)))))))))) (Inv.inv.{0} Real Real.hasInv r)) (NormedSpace.polar.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3 (Metric.closedBall.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_2) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_2))))))))) r))
but is expected to have type
  forall (𝕜 : Type.{u2}) [_inst_1 : NontriviallyNormedField.{u2} 𝕜] {E : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} E] [_inst_3 : NormedSpace.{u2, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) _inst_2] {r : Real}, HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3)) (Set.instHasSubsetSet.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3)) (Metric.closedBall.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toPseudoMetricSpace.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.instSeminormedAddCommGroupDual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3)) (OfNat.ofNat.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) 0 (Zero.toOfNat0.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (NegZeroClass.toZero.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SubNegZeroMonoid.toNegZeroClass.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SubtractionMonoid.toSubNegZeroMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SubtractionCommMonoid.toSubtractionMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (AddCommGroup.toDivisionAddCommMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toAddCommGroup.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.instSeminormedAddCommGroupDual.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3))))))))) (Inv.inv.{0} Real Real.instInvReal r)) (NormedSpace.polar.{u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 (Metric.closedBall.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E _inst_2) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))))) r))
Case conversion may be inaccurate. Consider using '#align normed_space.closed_ball_inv_subset_polar_closed_ball NormedSpace.closedBall_inv_subset_polar_closedBallₓ'. -/
theorem closedBall_inv_subset_polar_closedBall {r : ℝ} :
    closedBall (0 : Dual 𝕜 E) r⁻¹ ⊆ polar 𝕜 (closedBall (0 : E) r) := fun x' hx' x hx =>
  calc
    ‖x' x‖ ≤ ‖x'‖ * ‖x‖ := x'.le_opNorm x
    _ ≤ r⁻¹ * r :=
      (mul_le_mul (mem_closedBall_zero_iff.1 hx') (mem_closedBall_zero_iff.1 hx) (norm_nonneg _)
        (dist_nonneg.trans hx'))
    _ = r / r := (inv_mul_eq_div _ _)
    _ ≤ 1 := div_self_le_one r
    
#align normed_space.closed_ball_inv_subset_polar_closed_ball NormedSpace.closedBall_inv_subset_polar_closedBall

/- warning: normed_space.polar_closed_ball -> NormedSpace.polar_closedBall is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_4 : IsROrC.{u1} 𝕜] [_inst_5 : NormedAddCommGroup.{u2} E] [_inst_6 : NormedSpace.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)] {r : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Eq.{succ (max u2 u1)} (Set.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6)) (NormedSpace.polar.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6 (Metric.closedBall.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_5))))))))) r)) (Metric.closedBall.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) (SeminormedAddCommGroup.toPseudoMetricSpace.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) (NormedSpace.Dual.seminormedAddCommGroup.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6)) (OfNat.ofNat.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) 0 (OfNat.mk.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) 0 (Zero.zero.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) (AddZeroClass.toHasZero.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) (AddMonoid.toAddZeroClass.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) (SubNegMonoid.toAddMonoid.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) (AddGroup.toSubNegMonoid.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) (NormedAddGroup.toAddGroup.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) (NormedAddCommGroup.toNormedAddGroup.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) (NormedSpace.Dual.normedAddCommGroup.{u1, u2} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_4)) E _inst_5 _inst_6)))))))))) (Inv.inv.{0} Real Real.hasInv r)))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_4 : IsROrC.{u2} 𝕜] [_inst_5 : NormedAddCommGroup.{u1} E] [_inst_6 : NormedSpace.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)] {r : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (NormedSpace.Dual.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6)) (NormedSpace.polar.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6 (Metric.closedBall.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_5)))))))) r)) (Metric.closedBall.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6) (SeminormedAddCommGroup.toPseudoMetricSpace.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6) (NormedSpace.instSeminormedAddCommGroupDual.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6)) (OfNat.ofNat.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6) 0 (Zero.toOfNat0.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6) (NegZeroClass.toZero.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6) (SubNegZeroMonoid.toNegZeroClass.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6) (SubtractionMonoid.toSubNegZeroMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6) (SubtractionCommMonoid.toSubtractionMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6) (AddCommGroup.toDivisionAddCommMonoid.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6) (NormedAddCommGroup.toAddCommGroup.{max u2 u1} (NormedSpace.Dual.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6) (NormedSpace.instNormedAddCommGroupDualToSeminormedAddCommGroup.{u2, u1} 𝕜 (DenselyNormedField.toNontriviallyNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_4)) E _inst_5 _inst_6))))))))) (Inv.inv.{0} Real Real.instInvReal r)))
Case conversion may be inaccurate. Consider using '#align normed_space.polar_closed_ball NormedSpace.polar_closedBallₓ'. -/
/-- The `polar` of closed ball in a normed space `E` is the closed ball of the dual with
inverse radius. -/
theorem polar_closedBall {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℝ}
    (hr : 0 < r) : polar 𝕜 (closedBall (0 : E) r) = closedBall (0 : Dual 𝕜 E) r⁻¹ :=
  by
  refine' subset.antisymm _ (closed_ball_inv_subset_polar_closed_ball _)
  intro x' h
  simp only [mem_closedBall_zero_iff]
  refine' ContinuousLinearMap.op_norm_le_of_ball hr (inv_nonneg.mpr hr.le) fun z hz => _
  simpa only [one_div] using LinearMap.bound_of_ball_bound' hr 1 x'.to_linear_map h z
#align normed_space.polar_closed_ball NormedSpace.polar_closedBall

/- warning: normed_space.bounded_polar_of_mem_nhds_zero -> NormedSpace.bounded_polar_of_mem_nhds_zero is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) _inst_2] {s : Set.{u2} E}, (Membership.Mem.{u2, u2} (Set.{u2} E) (Filter.{u2} E) (Filter.hasMem.{u2} E) s (nhds.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_2))) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_2))))))))))) -> (Metric.Bounded.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toPseudoMetricSpace.{max u2 u1} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.Dual.seminormedAddCommGroup.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)) (NormedSpace.polar.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3 s))
but is expected to have type
  forall (𝕜 : Type.{u1}) [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) _inst_2] {s : Set.{u2} E}, (Membership.mem.{u2, u2} (Set.{u2} E) (Filter.{u2} E) (instMembershipSetFilter.{u2} E) s (nhds.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E _inst_2))) (OfNat.ofNat.{u2} E 0 (Zero.toOfNat0.{u2} E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))))))) -> (Metric.Bounded.{max u1 u2} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (SeminormedAddCommGroup.toPseudoMetricSpace.{max u1 u2} (NormedSpace.Dual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3) (NormedSpace.instSeminormedAddCommGroupDual.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3)) (NormedSpace.polar.{u1, u2} 𝕜 _inst_1 E _inst_2 _inst_3 s))
Case conversion may be inaccurate. Consider using '#align normed_space.bounded_polar_of_mem_nhds_zero NormedSpace.bounded_polar_of_mem_nhds_zeroₓ'. -/
/-- Given a neighborhood `s` of the origin in a normed space `E`, the dual norms
of all elements of the polar `polar 𝕜 s` are bounded by a constant. -/
theorem bounded_polar_of_mem_nhds_zero {s : Set E} (s_nhd : s ∈ 𝓝 (0 : E)) : Bounded (polar 𝕜 s) :=
  by
  obtain ⟨a, ha⟩ : ∃ a : 𝕜, 1 < ‖a‖ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, r_pos, r_ball⟩ : ∃ (r : ℝ)(hr : 0 < r), ball 0 r ⊆ s := Metric.mem_nhds_iff.1 s_nhd
  exact
    bounded_closed_ball.mono
      (((dual_pairing 𝕜 E).flip.polar_antitone r_ball).trans <|
        polar_ball_subset_closed_ball_div ha r_pos)
#align normed_space.bounded_polar_of_mem_nhds_zero NormedSpace.bounded_polar_of_mem_nhds_zero

end PolarSets

end NormedSpace

