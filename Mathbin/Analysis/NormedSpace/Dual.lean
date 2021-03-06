/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathbin.Analysis.NormedSpace.HahnBanach.Extension
import Mathbin.Analysis.NormedSpace.IsROrC
import Mathbin.Analysis.LocallyConvex.Polar

/-!
# The topological dual of a normed space

In this file we define the topological dual `normed_space.dual` of a normed space, and the
continuous linear map `normed_space.inclusion_in_double_dual` from a normed space into its double
dual.

For base field `๐ = โ` or `๐ = โ`, this map is actually an isometric embedding; we provide a
version `normed_space.inclusion_in_double_dual_li` of the map which is of type a bundled linear
isometric embedding, `E โโแตข[๐] (dual ๐ (dual ๐ E))`.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `semi_normed_group` and we specialize to `normed_group` when needed.

## Main definitions

* `inclusion_in_double_dual` and `inclusion_in_double_dual_li` are the inclusion of a normed space
  in its double dual, considered as a bounded linear map and as a linear isometry, respectively.
* `polar ๐ s` is the subset of `dual ๐ E` consisting of those functionals `x'` for which
  `โฅx' zโฅ โค 1` for every `z โ s`.

## Tags

dual
-/


noncomputable section

open Classical TopologicalSpace

universe u v

namespace NormedSpace

section General

variable (๐ : Type _) [NondiscreteNormedField ๐]

variable (E : Type _) [SemiNormedGroup E] [NormedSpace ๐ E]

variable (F : Type _) [NormedGroup F] [NormedSpace ๐ F]

-- ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler normed_space ๐
/-- The topological dual of a seminormed space `E`. -/
def Dual :=
  E โL[๐] ๐ deriving Inhabited, SemiNormedGroup,
  ยซ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler normed_space ๐ยป

instance : ContinuousLinearMapClass (Dual ๐ E) ๐ E ๐ :=
  ContinuousLinearMap.continuousSemilinearMapClass

instance : CoeFun (Dual ๐ E) fun _ => E โ ๐ :=
  ContinuousLinearMap.toFun

instance : NormedGroup (Dual ๐ F) :=
  ContinuousLinearMap.toNormedGroup

instance [FiniteDimensional ๐ E] : FiniteDimensional ๐ (Dual ๐ E) :=
  ContinuousLinearMap.finite_dimensional

/-- The inclusion of a normed space in its double (topological) dual, considered
   as a bounded linear map. -/
def inclusionInDoubleDual : E โL[๐] Dual ๐ (Dual ๐ E) :=
  ContinuousLinearMap.apply ๐ ๐

@[simp]
theorem dual_def (x : E) (f : Dual ๐ E) : inclusionInDoubleDual ๐ E x f = f x :=
  rfl

theorem inclusion_in_double_dual_norm_eq : โฅinclusionInDoubleDual ๐ Eโฅ = โฅContinuousLinearMap.id ๐ (Dual ๐ E)โฅ :=
  ContinuousLinearMap.op_norm_flip _

theorem inclusion_in_double_dual_norm_le : โฅinclusionInDoubleDual ๐ Eโฅ โค 1 := by
  rw [inclusion_in_double_dual_norm_eq]
  exact ContinuousLinearMap.norm_id_le

theorem double_dual_bound (x : E) : โฅ(inclusionInDoubleDual ๐ E) xโฅ โค โฅxโฅ := by
  simpa using ContinuousLinearMap.le_of_op_norm_le _ (inclusion_in_double_dual_norm_le ๐ E) x

/-- The dual pairing as a bilinear form. -/
def dualPairing : Dual ๐ E โโ[๐] E โโ[๐] ๐ :=
  ContinuousLinearMap.coeLm ๐

@[simp]
theorem dual_pairing_apply {v : Dual ๐ E} {x : E} : dualPairing ๐ E v x = v x :=
  rfl

theorem dual_pairing_separating_left : (dualPairing ๐ E).SeparatingLeft := by
  rw [LinearMap.separating_left_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ContinuousLinearMap.coe_injective

end General

section BidualIsometry

variable (๐ : Type v) [IsROrC ๐] {E : Type u} [NormedGroup E] [NormedSpace ๐ E]

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
    Compare `continuous_linear_map.op_norm_le_bound`. -/
theorem norm_le_dual_bound (x : E) {M : โ} (hMp : 0 โค M) (hM : โ f : Dual ๐ E, โฅf xโฅ โค M * โฅfโฅ) : โฅxโฅ โค M := by
  classical
  by_cases' h : x = 0
  ยท simp only [โ h, โ hMp, โ norm_zero]
    
  ยท obtain โจf, hfโ, hfxโฉ : โ f : E โL[๐] ๐, โฅfโฅ = 1 โง f x = โฅxโฅ := exists_dual_vector ๐ x h
    calc โฅxโฅ = โฅ(โฅxโฅ : ๐)โฅ := is_R_or_C.norm_coe_norm.symm _ = โฅf xโฅ := by
        rw [hfx]_ โค M * โฅfโฅ := hM f _ = M := by
        rw [hfโ, mul_oneโ]
    

theorem eq_zero_of_forall_dual_eq_zero {x : E} (h : โ f : Dual ๐ E, f x = (0 : ๐)) : x = 0 :=
  norm_le_zero_iff.mp
    (norm_le_dual_bound ๐ x le_rfl fun f => by
      simp [โ h f])

theorem eq_zero_iff_forall_dual_eq_zero (x : E) : x = 0 โ โ g : Dual ๐ E, g x = 0 :=
  โจfun hx => by
    simp [โ hx], fun h => eq_zero_of_forall_dual_eq_zero ๐ hโฉ

/-- See also `geometric_hahn_banach_point_point`. -/
theorem eq_iff_forall_dual_eq {x y : E} : x = y โ โ g : Dual ๐ E, g x = g y := by
  rw [โ sub_eq_zero, eq_zero_iff_forall_dual_eq_zero ๐ (x - y)]
  simp [โ sub_eq_zero]

/-- The inclusion of a normed space in its double dual is an isometry onto its image.-/
def inclusionInDoubleDualLi : E โโแตข[๐] Dual ๐ (Dual ๐ E) :=
  { inclusionInDoubleDual ๐ E with
    norm_map' := by
      intro x
      apply le_antisymmโ
      ยท exact double_dual_bound ๐ E x
        
      rw [ContinuousLinearMap.norm_def]
      refine' le_cInf ContinuousLinearMap.bounds_nonempty _
      rintro c โจhc1, hc2โฉ
      exact norm_le_dual_bound ๐ x hc1 hc2 }

end BidualIsometry

section PolarSets

open Metric Set NormedSpace

/-- Given a subset `s` in a normed space `E` (over a field `๐`), the polar
`polar ๐ s` is the subset of `dual ๐ E` consisting of those functionals which
evaluate to something of norm at most one at all points `z โ s`. -/
def Polar (๐ : Type _) [NondiscreteNormedField ๐] {E : Type _} [SemiNormedGroup E] [NormedSpace ๐ E] :
    Set E โ Set (Dual ๐ E) :=
  (dualPairing ๐ E).flip.Polar

variable (๐ : Type _) [NondiscreteNormedField ๐]

variable {E : Type _} [SemiNormedGroup E] [NormedSpace ๐ E]

theorem mem_polar_iff {x' : Dual ๐ E} (s : Set E) : x' โ Polar ๐ s โ โ, โ z โ s, โ, โฅx' zโฅ โค 1 :=
  Iff.rfl

@[simp]
theorem polar_univ : Polar ๐ (Univ : Set E) = {(0 : dual ๐ E)} :=
  (dualPairing ๐ E).flip.polar_univ (LinearMap.flip_separating_right.mpr (dual_pairing_separating_left ๐ E))

theorem is_closed_polar (s : Set E) : IsClosed (Polar ๐ s) := by
  dunfold NormedSpace.Polar
  simp only [โ LinearMap.polar_eq_Inter, โ LinearMap.flip_apply]
  refine' is_closed_bInter fun z hz => _
  exact is_closed_Iic.preimage (ContinuousLinearMap.apply ๐ ๐ z).Continuous.norm

@[simp]
theorem polar_closure (s : Set E) : Polar ๐ (Closure s) = Polar ๐ s :=
  ((dualPairing ๐ E).flip.polar_antitone subset_closure).antisymm <|
    (dualPairing ๐ E).flip.polar_gc.l_le <|
      closure_minimal ((dualPairing ๐ E).flip.polar_gc.le_u_l s) <| by
        simpa [โ LinearMap.flip_flip] using (is_closed_polar _ _).Preimage (inclusion_in_double_dual ๐ E).Continuous

variable {๐}

/-- If `x'` is a dual element such that the norms `โฅx' zโฅ` are bounded for `z โ s`, then a
small scalar multiple of `x'` is in `polar ๐ s`. -/
theorem smul_mem_polar {s : Set E} {x' : Dual ๐ E} {c : ๐} (hc : โ z, z โ s โ โฅx' zโฅ โค โฅcโฅ) : cโปยน โข x' โ Polar ๐ s := by
  by_cases' c_zero : c = 0
  ยท simp only [โ c_zero, โ inv_zero, โ zero_smul]
    exact (dual_pairing ๐ E).flip.zero_mem_polar _
    
  have eq : โ z, โฅcโปยน โข x' zโฅ = โฅcโปยนโฅ * โฅx' zโฅ := fun z => norm_smul cโปยน _
  have le : โ z, z โ s โ โฅcโปยน โข x' zโฅ โค โฅcโปยนโฅ * โฅcโฅ := by
    intro z hzs
    rw [Eq z]
    apply mul_le_mul (le_of_eqโ rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _)
  have cancel : โฅcโปยนโฅ * โฅcโฅ = 1 := by
    simp only [โ c_zero, โ norm_eq_zero, โ Ne.def, โ not_false_iff, โ inv_mul_cancel, โ norm_inv]
  rwa [cancel] at le

theorem polar_ball_subset_closed_ball_div {c : ๐} (hc : 1 < โฅcโฅ) {r : โ} (hr : 0 < r) :
    Polar ๐ (Ball (0 : E) r) โ ClosedBall (0 : Dual ๐ E) (โฅcโฅ / r) := by
  intro x' hx'
  rw [mem_polar_iff] at hx'
  simp only [โ polar, โ mem_set_of_eq, โ mem_closed_ball_zero_iff, โ mem_ball_zero_iff] at *
  have hcr : 0 < โฅcโฅ / r := div_pos (zero_lt_one.trans hc) hr
  refine' ContinuousLinearMap.op_norm_le_of_shell hr hcr.le hc fun x hโ hโ => _
  calc โฅx' xโฅ โค 1 := hx' _ hโ _ โค โฅcโฅ / r * โฅxโฅ :=
      (inv_pos_le_iff_one_le_mul' hcr).1
        (by
          rwa [inv_div])

variable (๐)

theorem closed_ball_inv_subset_polar_closed_ball {r : โ} :
    ClosedBall (0 : Dual ๐ E) rโปยน โ Polar ๐ (ClosedBall (0 : E) r) := fun x' hx' x hx =>
  calc
    โฅx' xโฅ โค โฅx'โฅ * โฅxโฅ := x'.le_op_norm x
    _ โค rโปยน * r :=
      mul_le_mul (mem_closed_ball_zero_iff.1 hx') (mem_closed_ball_zero_iff.1 hx) (norm_nonneg _)
        (dist_nonneg.trans hx')
    _ = r / r := inv_mul_eq_div _ _
    _ โค 1 := div_self_le_one r
    

/-- The `polar` of closed ball in a normed space `E` is the closed ball of the dual with
inverse radius. -/
theorem polar_closed_ball {๐ : Type _} [IsROrC ๐] {E : Type _} [NormedGroup E] [NormedSpace ๐ E] {r : โ} (hr : 0 < r) :
    Polar ๐ (ClosedBall (0 : E) r) = ClosedBall (0 : Dual ๐ E) rโปยน := by
  refine' subset.antisymm _ (closed_ball_inv_subset_polar_closed_ball _)
  intro x' h
  simp only [โ mem_closed_ball_zero_iff]
  refine' ContinuousLinearMap.op_norm_le_of_ball hr (inv_nonneg.mpr hr.le) fun z hz => _
  simpa only [โ one_div] using LinearMap.bound_of_ball_bound' hr 1 x'.to_linear_map h z

/-- Given a neighborhood `s` of the origin in a normed space `E`, the dual norms
of all elements of the polar `polar ๐ s` are bounded by a constant. -/
theorem bounded_polar_of_mem_nhds_zero {s : Set E} (s_nhd : s โ ๐ (0 : E)) : Bounded (Polar ๐ s) := by
  obtain โจa, haโฉ : โ a : ๐, 1 < โฅaโฅ := NormedField.exists_one_lt_norm ๐
  obtain โจr, r_pos, r_ballโฉ : โ (r : โ)(hr : 0 < r), ball 0 r โ s := Metric.mem_nhds_iff.1 s_nhd
  exact
    bounded_closed_ball.mono
      (((dual_pairing ๐ E).flip.polar_antitone r_ball).trans <| polar_ball_subset_closed_ball_div ha r_pos)

end PolarSets

end NormedSpace

