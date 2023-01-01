/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies

! This file was ported from Lean 3 source module analysis.normed.group.pointwise
! leanprover-community/mathlib commit ffc3730d545623aedf5d5bd46a3153cbf41f6c2c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Topology.MetricSpace.HausdorffDistance

/-!
# Properties of pointwise addition of sets in normed groups

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/


open Metric Set

open Pointwise TopologicalSpace

variable {E : Type _}

section SeminormedGroup

variable [SeminormedGroup E] {ε δ : ℝ} {s t : Set E} {x y : E}

@[to_additive]
theorem Metric.Bounded.mul (hs : Bounded s) (ht : Bounded t) : Bounded (s * t) :=
  by
  obtain ⟨Rs, hRs⟩ : ∃ R, ∀ x ∈ s, ‖x‖ ≤ R := hs.exists_norm_le'
  obtain ⟨Rt, hRt⟩ : ∃ R, ∀ x ∈ t, ‖x‖ ≤ R := ht.exists_norm_le'
  refine' bounded_iff_forall_norm_le'.2 ⟨Rs + Rt, _⟩
  rintro z ⟨x, y, hx, hy, rfl⟩
  exact norm_mul_le_of_le (hRs x hx) (hRt y hy)
#align metric.bounded.mul Metric.Bounded.mul

@[to_additive]
theorem Metric.Bounded.inv : Bounded s → Bounded s⁻¹ :=
  by
  simp_rw [bounded_iff_forall_norm_le', ← image_inv, ball_image_iff, norm_inv']
  exact id
#align metric.bounded.inv Metric.Bounded.inv

@[to_additive]
theorem Metric.Bounded.div (hs : Bounded s) (ht : Bounded t) : Bounded (s / t) :=
  (div_eq_mul_inv _ _).symm.subst <| hs.mul ht.inv
#align metric.bounded.div Metric.Bounded.div

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] {ε δ : ℝ} {s t : Set E} {x y : E}

section Emetric

open Emetric

@[to_additive]
theorem inf_edist_inv (x : E) (s : Set E) : infEdist x⁻¹ s = infEdist x s⁻¹ :=
  eq_of_forall_le_iff fun r => by simp_rw [le_inf_edist, ← image_inv, ball_image_iff, edist_inv]
#align inf_edist_inv inf_edist_inv

@[simp, to_additive]
theorem inf_edist_inv_inv (x : E) (s : Set E) : infEdist x⁻¹ s⁻¹ = infEdist x s := by
  rw [inf_edist_inv, inv_inv]
#align inf_edist_inv_inv inf_edist_inv_inv

end Emetric

variable (ε δ s t x y)

@[simp, to_additive]
theorem inv_thickening : (thickening δ s)⁻¹ = thickening δ s⁻¹ :=
  by
  simp_rw [thickening, ← inf_edist_inv]
  rfl
#align inv_thickening inv_thickening

@[simp, to_additive]
theorem inv_cthickening : (cthickening δ s)⁻¹ = cthickening δ s⁻¹ :=
  by
  simp_rw [cthickening, ← inf_edist_inv]
  rfl
#align inv_cthickening inv_cthickening

@[simp, to_additive]
theorem inv_ball : (ball x δ)⁻¹ = ball x⁻¹ δ :=
  by
  simp_rw [ball, ← dist_inv]
  rfl
#align inv_ball inv_ball

@[simp, to_additive]
theorem inv_closed_ball : (closedBall x δ)⁻¹ = closedBall x⁻¹ δ :=
  by
  simp_rw [closed_ball, ← dist_inv]
  rfl
#align inv_closed_ball inv_closed_ball

@[to_additive]
theorem singleton_mul_ball : {x} * ball y δ = ball (x * y) δ := by
  simp only [preimage_mul_ball, image_mul_left, singleton_mul, div_inv_eq_mul, mul_comm y x]
#align singleton_mul_ball singleton_mul_ball

@[to_additive]
theorem singleton_div_ball : {x} / ball y δ = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_ball, singleton_mul_ball]
#align singleton_div_ball singleton_div_ball

@[to_additive]
theorem ball_mul_singleton : ball x δ * {y} = ball (x * y) δ := by
  rw [mul_comm, singleton_mul_ball, mul_comm y]
#align ball_mul_singleton ball_mul_singleton

@[to_additive]
theorem ball_div_singleton : ball x δ / {y} = ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_singleton, ball_mul_singleton]
#align ball_div_singleton ball_div_singleton

@[to_additive]
theorem singleton_mul_ball_one : {x} * ball 1 δ = ball x δ := by simp
#align singleton_mul_ball_one singleton_mul_ball_one

@[to_additive]
theorem singleton_div_ball_one : {x} / ball 1 δ = ball x δ := by simp [singleton_div_ball]
#align singleton_div_ball_one singleton_div_ball_one

@[to_additive]
theorem ball_one_mul_singleton : ball 1 δ * {x} = ball x δ := by simp [ball_mul_singleton]
#align ball_one_mul_singleton ball_one_mul_singleton

@[to_additive]
theorem ball_one_div_singleton : ball 1 δ / {x} = ball x⁻¹ δ := by simp [ball_div_singleton]
#align ball_one_div_singleton ball_one_div_singleton

@[to_additive]
theorem smul_ball_one : x • ball 1 δ = ball x δ :=
  by
  ext
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_div, dist_eq_norm_div]
#align smul_ball_one smul_ball_one

@[simp, to_additive]
theorem singleton_mul_closed_ball : {x} * closedBall y δ = closedBall (x * y) δ := by
  simp only [mul_comm y x, preimage_mul_closed_ball, image_mul_left, singleton_mul, div_inv_eq_mul]
#align singleton_mul_closed_ball singleton_mul_closed_ball

@[simp, to_additive]
theorem singleton_div_closed_ball : {x} / closedBall y δ = closedBall (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_closed_ball, singleton_mul_closed_ball]
#align singleton_div_closed_ball singleton_div_closed_ball

@[simp, to_additive]
theorem closed_ball_mul_singleton : closedBall x δ * {y} = closedBall (x * y) δ := by
  simp [mul_comm _ {y}, mul_comm y]
#align closed_ball_mul_singleton closed_ball_mul_singleton

@[simp, to_additive]
theorem closed_ball_div_singleton : closedBall x δ / {y} = closedBall (x / y) δ := by
  simp [div_eq_mul_inv]
#align closed_ball_div_singleton closed_ball_div_singleton

@[to_additive]
theorem singleton_mul_closed_ball_one : {x} * closedBall 1 δ = closedBall x δ := by simp
#align singleton_mul_closed_ball_one singleton_mul_closed_ball_one

@[to_additive]
theorem singleton_div_closed_ball_one : {x} / closedBall 1 δ = closedBall x δ := by simp
#align singleton_div_closed_ball_one singleton_div_closed_ball_one

@[to_additive]
theorem closed_ball_one_mul_singleton : closedBall 1 δ * {x} = closedBall x δ := by simp
#align closed_ball_one_mul_singleton closed_ball_one_mul_singleton

@[to_additive]
theorem closed_ball_one_div_singleton : closedBall 1 δ / {x} = closedBall x⁻¹ δ := by simp
#align closed_ball_one_div_singleton closed_ball_one_div_singleton

@[simp, to_additive]
theorem smul_closed_ball_one : x • closedBall 1 δ = closedBall x δ :=
  by
  ext
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_div, dist_eq_norm_div]
#align smul_closed_ball_one smul_closed_ball_one

@[to_additive]
theorem mul_ball_one : s * ball 1 δ = thickening δ s :=
  by
  rw [thickening_eq_bUnion_ball]
  convert Union₂_mul (fun x (_ : x ∈ s) => {x}) (ball (1 : E) δ)
  exact s.bUnion_of_singleton.symm
  ext (x y)
  simp_rw [singleton_mul_ball, mul_one]
#align mul_ball_one mul_ball_one

@[to_additive]
theorem div_ball_one : s / ball 1 δ = thickening δ s := by simp [div_eq_mul_inv, mul_ball_one]
#align div_ball_one div_ball_one

@[to_additive]
theorem ball_mul_one : ball 1 δ * s = thickening δ s := by rw [mul_comm, mul_ball_one]
#align ball_mul_one ball_mul_one

@[to_additive]
theorem ball_div_one : ball 1 δ / s = thickening δ s⁻¹ := by simp [div_eq_mul_inv, ball_mul_one]
#align ball_div_one ball_div_one

@[simp, to_additive]
theorem mul_ball : s * ball x δ = x • thickening δ s := by
  rw [← smul_ball_one, mul_smul_comm, mul_ball_one]
#align mul_ball mul_ball

@[simp, to_additive]
theorem div_ball : s / ball x δ = x⁻¹ • thickening δ s := by simp [div_eq_mul_inv]
#align div_ball div_ball

@[simp, to_additive]
theorem ball_mul : ball x δ * s = x • thickening δ s := by rw [mul_comm, mul_ball]
#align ball_mul ball_mul

@[simp, to_additive]
theorem ball_div : ball x δ / s = x • thickening δ s⁻¹ := by simp [div_eq_mul_inv]
#align ball_div ball_div

variable {ε δ s t x y}

@[to_additive]
theorem IsCompact.mul_closed_ball_one (hs : IsCompact s) (hδ : 0 ≤ δ) :
    s * closedBall 1 δ = cthickening δ s :=
  by
  rw [hs.cthickening_eq_bUnion_closed_ball hδ]
  ext x
  simp only [mem_mul, dist_eq_norm_div, exists_prop, mem_Union, mem_closed_ball, exists_and_left,
    mem_closed_ball_one_iff, ← eq_div_iff_mul_eq'', exists_eq_right]
#align is_compact.mul_closed_ball_one IsCompact.mul_closed_ball_one

@[to_additive]
theorem IsCompact.div_closed_ball_one (hs : IsCompact s) (hδ : 0 ≤ δ) :
    s / closedBall 1 δ = cthickening δ s := by simp [div_eq_mul_inv, hs.mul_closed_ball_one hδ]
#align is_compact.div_closed_ball_one IsCompact.div_closed_ball_one

@[to_additive]
theorem IsCompact.closed_ball_one_mul (hs : IsCompact s) (hδ : 0 ≤ δ) :
    closedBall 1 δ * s = cthickening δ s := by rw [mul_comm, hs.mul_closed_ball_one hδ]
#align is_compact.closed_ball_one_mul IsCompact.closed_ball_one_mul

@[to_additive]
theorem IsCompact.closed_ball_one_div (hs : IsCompact s) (hδ : 0 ≤ δ) :
    closedBall 1 δ / s = cthickening δ s⁻¹ := by
  simp [div_eq_mul_inv, mul_comm, hs.inv.mul_closed_ball_one hδ]
#align is_compact.closed_ball_one_div IsCompact.closed_ball_one_div

@[to_additive]
theorem IsCompact.mul_closed_ball (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s * closedBall x δ = x • cthickening δ s := by
  rw [← smul_closed_ball_one, mul_smul_comm, hs.mul_closed_ball_one hδ]
#align is_compact.mul_closed_ball IsCompact.mul_closed_ball

@[to_additive]
theorem IsCompact.div_closed_ball (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s / closedBall x δ = x⁻¹ • cthickening δ s := by
  simp [div_eq_mul_inv, mul_comm, hs.mul_closed_ball hδ]
#align is_compact.div_closed_ball IsCompact.div_closed_ball

@[to_additive]
theorem IsCompact.closed_ball_mul (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by rw [mul_comm, hs.mul_closed_ball hδ]
#align is_compact.closed_ball_mul IsCompact.closed_ball_mul

@[to_additive]
theorem IsCompact.closed_ball_div (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    closedBall x δ * s = x • cthickening δ s := by
  simp [div_eq_mul_inv, mul_comm, hs.closed_ball_mul hδ]
#align is_compact.closed_ball_div IsCompact.closed_ball_div

end SeminormedCommGroup

