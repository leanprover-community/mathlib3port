/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yaël Dillies
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
theorem Metric.Bounded.mul (hs : Bounded s) (ht : Bounded t) : Bounded (s * t) := by
  obtain ⟨Rs, hRs⟩ : ∃ R, ∀ x ∈ s, ∥x∥ ≤ R := hs.exists_norm_le'
  obtain ⟨Rt, hRt⟩ : ∃ R, ∀ x ∈ t, ∥x∥ ≤ R := ht.exists_norm_le'
  refine' bounded_iff_forall_norm_le'.2 ⟨Rs + Rt, _⟩
  rintro z ⟨x, y, hx, hy, rfl⟩
  exact norm_mul_le_of_le (hRs x hx) (hRt y hy)

@[to_additive]
theorem Metric.Bounded.inv : Bounded s → Bounded s⁻¹ := by
  simp_rw [bounded_iff_forall_norm_le', ← image_inv, ball_image_iff, norm_inv']
  exact id

@[to_additive]
theorem Metric.Bounded.div (hs : Bounded s) (ht : Bounded t) : Bounded (s / t) :=
  (div_eq_mul_inv _ _).symm.subst <| hs.mul ht.inv

end SeminormedGroup

section SeminormedCommGroup

variable [SeminormedCommGroup E] {ε δ : ℝ} {s t : Set E} {x y : E}

section Emetric

open Emetric

@[to_additive]
theorem inf_edist_inv (x : E) (s : Set E) : infEdist x⁻¹ s = infEdist x s⁻¹ :=
  eq_of_forall_le_iff fun r => by simp_rw [le_inf_edist, ← image_inv, ball_image_iff, edist_inv]

@[simp, to_additive]
theorem inf_edist_inv_inv (x : E) (s : Set E) : infEdist x⁻¹ s⁻¹ = infEdist x s := by rw [inf_edist_inv, inv_inv]

end Emetric

variable (ε δ s t x y)

@[simp, to_additive]
theorem inv_thickening : (Thickening δ s)⁻¹ = Thickening δ s⁻¹ := by
  simp_rw [thickening, ← inf_edist_inv]
  rfl

@[simp, to_additive]
theorem inv_cthickening : (Cthickening δ s)⁻¹ = Cthickening δ s⁻¹ := by
  simp_rw [cthickening, ← inf_edist_inv]
  rfl

@[simp, to_additive]
theorem inv_ball : (Ball x δ)⁻¹ = Ball x⁻¹ δ := by
  simp_rw [ball, ← dist_inv]
  rfl

@[simp, to_additive]
theorem inv_closed_ball : (ClosedBall x δ)⁻¹ = ClosedBall x⁻¹ δ := by
  simp_rw [closed_ball, ← dist_inv]
  rfl

@[to_additive]
theorem singleton_mul_ball : {x} * Ball y δ = Ball (x * y) δ := by
  simp only [preimage_mul_ball, image_mul_left, singleton_mul, div_inv_eq_mul, mul_comm y x]

@[to_additive]
theorem singleton_div_ball : {x} / Ball y δ = Ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_ball, singleton_mul_ball]

@[to_additive]
theorem ball_mul_singleton : Ball x δ * {y} = Ball (x * y) δ := by rw [mul_comm, singleton_mul_ball, mul_comm y]

@[to_additive]
theorem ball_div_singleton : Ball x δ / {y} = Ball (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_singleton, ball_mul_singleton]

@[to_additive]
theorem singleton_mul_ball_one : {x} * Ball 1 δ = Ball x δ := by simp

@[to_additive]
theorem singleton_div_ball_one : {x} / Ball 1 δ = Ball x δ := by simp [singleton_div_ball]

@[to_additive]
theorem ball_one_mul_singleton : Ball 1 δ * {x} = Ball x δ := by simp [ball_mul_singleton]

@[to_additive]
theorem ball_one_div_singleton : Ball 1 δ / {x} = Ball x⁻¹ δ := by simp [ball_div_singleton]

@[to_additive]
theorem smul_ball_one : x • Ball 1 δ = Ball x δ := by
  ext
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_div, dist_eq_norm_div]

@[simp, to_additive]
theorem singleton_mul_closed_ball : {x} * ClosedBall y δ = ClosedBall (x * y) δ := by
  simp only [mul_comm y x, preimage_mul_closed_ball, image_mul_left, singleton_mul, div_inv_eq_mul]

@[simp, to_additive]
theorem singleton_div_closed_ball : {x} / ClosedBall y δ = ClosedBall (x / y) δ := by
  simp_rw [div_eq_mul_inv, inv_closed_ball, singleton_mul_closed_ball]

@[simp, to_additive]
theorem closed_ball_mul_singleton : ClosedBall x δ * {y} = ClosedBall (x * y) δ := by simp [mul_comm _ {y}, mul_comm y]

@[simp, to_additive]
theorem closed_ball_div_singleton : ClosedBall x δ / {y} = ClosedBall (x / y) δ := by simp [div_eq_mul_inv]

@[to_additive]
theorem singleton_mul_closed_ball_one : {x} * ClosedBall 1 δ = ClosedBall x δ := by simp

@[to_additive]
theorem singleton_div_closed_ball_one : {x} / ClosedBall 1 δ = ClosedBall x δ := by simp

@[to_additive]
theorem closed_ball_one_mul_singleton : ClosedBall 1 δ * {x} = ClosedBall x δ := by simp

@[to_additive]
theorem closed_ball_one_div_singleton : ClosedBall 1 δ / {x} = ClosedBall x⁻¹ δ := by simp

@[simp, to_additive]
theorem smul_closed_ball_one : x • ClosedBall 1 δ = ClosedBall x δ := by
  ext
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_div, dist_eq_norm_div]

@[to_additive]
theorem mul_ball_one : s * Ball 1 δ = Thickening δ s := by
  rw [thickening_eq_bUnion_ball]
  convert Union₂_mul (fun x (_ : x ∈ s) => {x}) (ball (1 : E) δ)
  exact s.bUnion_of_singleton.symm
  ext (x y)
  simp_rw [singleton_mul_ball, mul_one]

@[to_additive]
theorem div_ball_one : s / Ball 1 δ = Thickening δ s := by simp [div_eq_mul_inv, mul_ball_one]

@[to_additive]
theorem ball_mul_one : Ball 1 δ * s = Thickening δ s := by rw [mul_comm, mul_ball_one]

@[to_additive]
theorem ball_div_one : Ball 1 δ / s = Thickening δ s⁻¹ := by simp [div_eq_mul_inv, ball_mul_one]

@[simp, to_additive]
theorem mul_ball : s * Ball x δ = x • Thickening δ s := by rw [← smul_ball_one, mul_smul_comm, mul_ball_one]

@[simp, to_additive]
theorem div_ball : s / Ball x δ = x⁻¹ • Thickening δ s := by simp [div_eq_mul_inv]

@[simp, to_additive]
theorem ball_mul : Ball x δ * s = x • Thickening δ s := by rw [mul_comm, mul_ball]

@[simp, to_additive]
theorem ball_div : Ball x δ / s = x • Thickening δ s⁻¹ := by simp [div_eq_mul_inv]

variable {ε δ s t x y}

@[to_additive]
theorem IsCompact.mul_closed_ball_one (hs : IsCompact s) (hδ : 0 ≤ δ) : s * ClosedBall 1 δ = Cthickening δ s := by
  rw [hs.cthickening_eq_bUnion_closed_ball hδ]
  ext x
  simp only [mem_mul, dist_eq_norm_div, exists_prop, mem_Union, mem_closed_ball, exists_and_left,
    mem_closed_ball_one_iff, ← eq_div_iff_mul_eq'', exists_eq_right]

@[to_additive]
theorem IsCompact.div_closed_ball_one (hs : IsCompact s) (hδ : 0 ≤ δ) : s / ClosedBall 1 δ = Cthickening δ s := by
  simp [div_eq_mul_inv, hs.mul_closed_ball_one hδ]

@[to_additive]
theorem IsCompact.closed_ball_one_mul (hs : IsCompact s) (hδ : 0 ≤ δ) : ClosedBall 1 δ * s = Cthickening δ s := by
  rw [mul_comm, hs.mul_closed_ball_one hδ]

@[to_additive]
theorem IsCompact.closed_ball_one_div (hs : IsCompact s) (hδ : 0 ≤ δ) : ClosedBall 1 δ / s = Cthickening δ s⁻¹ := by
  simp [div_eq_mul_inv, mul_comm, hs.inv.mul_closed_ball_one hδ]

@[to_additive]
theorem IsCompact.mul_closed_ball (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) : s * ClosedBall x δ = x • Cthickening δ s :=
  by rw [← smul_closed_ball_one, mul_smul_comm, hs.mul_closed_ball_one hδ]

@[to_additive]
theorem IsCompact.div_closed_ball (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) :
    s / ClosedBall x δ = x⁻¹ • Cthickening δ s := by simp [div_eq_mul_inv, mul_comm, hs.mul_closed_ball hδ]

@[to_additive]
theorem IsCompact.closed_ball_mul (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) : ClosedBall x δ * s = x • Cthickening δ s :=
  by rw [mul_comm, hs.mul_closed_ball hδ]

@[to_additive]
theorem IsCompact.closed_ball_div (hs : IsCompact s) (hδ : 0 ≤ δ) (x : E) : ClosedBall x δ * s = x • Cthickening δ s :=
  by simp [div_eq_mul_inv, mul_comm, hs.closed_ball_mul hδ]

end SeminormedCommGroup

