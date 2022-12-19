/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.inner_product_space.euclidean_dist
! leanprover-community/mathlib commit bbeb185db4ccee8ed07dc48449414ebfa39cb821
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.InnerProductSpace.Calculus
import Mathbin.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean distance on a finite dimensional space

When we define a smooth bump function on a normed space, it is useful to have a smooth distance on
the space. Since the default distance is not guaranteed to be smooth, we define `to_euclidean` to be
an equivalence between a finite dimensional normed space and the standard Euclidean space of the
same dimension. Then we define `euclidean.dist x y = dist (to_euclidean x) (to_euclidean y)` and
provide some definitions (`euclidean.ball`, `euclidean.closed_ball`) and simple lemmas about this
distance. This way we hide the usage of `to_euclidean` behind an API.
-/


open TopologicalSpace

open Set

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- If `E` is a finite dimensional space over `ℝ`, then `to_euclidean` is a continuous `ℝ`-linear
equivalence between `E` and the Euclidean space of the same dimension. -/
def toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Fin <| FiniteDimensional.finrank ℝ E) :=
  ContinuousLinearEquiv.ofFinrankEq finrank_euclidean_space_fin.symm
#align to_euclidean toEuclidean

namespace Euclidean

/-- If `x` and `y` are two points in a finite dimensional space over `ℝ`, then `euclidean.dist x y`
is the distance between these points in the metric defined by some inner product space structure on
`E`. -/
def dist (x y : E) : ℝ :=
  dist (toEuclidean x) (toEuclidean y)
#align euclidean.dist Euclidean.dist

/-- Closed ball w.r.t. the euclidean distance. -/
def closedBall (x : E) (r : ℝ) : Set E :=
  { y | dist y x ≤ r }
#align euclidean.closed_ball Euclidean.closedBall

/-- Open ball w.r.t. the euclidean distance. -/
def ball (x : E) (r : ℝ) : Set E :=
  { y | dist y x < r }
#align euclidean.ball Euclidean.ball

theorem ball_eq_preimage (x : E) (r : ℝ) :
    ball x r = toEuclidean ⁻¹' Metric.ball (toEuclidean x) r :=
  rfl
#align euclidean.ball_eq_preimage Euclidean.ball_eq_preimage

theorem closed_ball_eq_preimage (x : E) (r : ℝ) :
    closedBall x r = toEuclidean ⁻¹' Metric.closedBall (toEuclidean x) r :=
  rfl
#align euclidean.closed_ball_eq_preimage Euclidean.closed_ball_eq_preimage

theorem ball_subset_closed_ball {x : E} {r : ℝ} : ball x r ⊆ closedBall x r := fun y (hy : _ < _) =>
  le_of_lt hy
#align euclidean.ball_subset_closed_ball Euclidean.ball_subset_closed_ball

theorem is_open_ball {x : E} {r : ℝ} : IsOpen (ball x r) :=
  Metric.is_open_ball.Preimage toEuclidean.Continuous
#align euclidean.is_open_ball Euclidean.is_open_ball

theorem mem_ball_self {x : E} {r : ℝ} (hr : 0 < r) : x ∈ ball x r :=
  Metric.mem_ball_self hr
#align euclidean.mem_ball_self Euclidean.mem_ball_self

theorem closed_ball_eq_image (x : E) (r : ℝ) :
    closedBall x r = toEuclidean.symm '' Metric.closedBall (toEuclidean x) r := by
  rw [to_euclidean.image_symm_eq_preimage, closed_ball_eq_preimage]
#align euclidean.closed_ball_eq_image Euclidean.closed_ball_eq_image

theorem is_compact_closed_ball {x : E} {r : ℝ} : IsCompact (closedBall x r) := by
  rw [closed_ball_eq_image]
  exact (is_compact_closed_ball _ _).image to_euclidean.symm.continuous
#align euclidean.is_compact_closed_ball Euclidean.is_compact_closed_ball

theorem is_closed_closed_ball {x : E} {r : ℝ} : IsClosed (closedBall x r) :=
  is_compact_closed_ball.IsClosed
#align euclidean.is_closed_closed_ball Euclidean.is_closed_closed_ball

theorem closure_ball (x : E) {r : ℝ} (h : r ≠ 0) : closure (ball x r) = closedBall x r := by
  rw [ball_eq_preimage, ← to_euclidean.preimage_closure, closure_ball (toEuclidean x) h,
    closed_ball_eq_preimage]
#align euclidean.closure_ball Euclidean.closure_ball

theorem exists_pos_lt_subset_ball {R : ℝ} {s : Set E} {x : E} (hR : 0 < R) (hs : IsClosed s)
    (h : s ⊆ ball x R) : ∃ r ∈ ioo 0 R, s ⊆ ball x r := by
  rw [ball_eq_preimage, ← image_subset_iff] at h
  rcases exists_pos_lt_subset_ball hR (to_euclidean.is_closed_image.2 hs) h with ⟨r, hr, hsr⟩
  exact ⟨r, hr, image_subset_iff.1 hsr⟩
#align euclidean.exists_pos_lt_subset_ball Euclidean.exists_pos_lt_subset_ball

theorem nhds_basis_closed_ball {x : E} : (𝓝 x).HasBasis (fun r : ℝ => 0 < r) (closedBall x) := by
  rw [to_euclidean.to_homeomorph.nhds_eq_comap]
  exact metric.nhds_basis_closed_ball.comap _
#align euclidean.nhds_basis_closed_ball Euclidean.nhds_basis_closed_ball

theorem closed_ball_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : closedBall x r ∈ 𝓝 x :=
  nhds_basis_closed_ball.mem_of_mem hr
#align euclidean.closed_ball_mem_nhds Euclidean.closed_ball_mem_nhds

theorem nhds_basis_ball {x : E} : (𝓝 x).HasBasis (fun r : ℝ => 0 < r) (ball x) := by
  rw [to_euclidean.to_homeomorph.nhds_eq_comap]
  exact metric.nhds_basis_ball.comap _
#align euclidean.nhds_basis_ball Euclidean.nhds_basis_ball

theorem ball_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : ball x r ∈ 𝓝 x :=
  nhds_basis_ball.mem_of_mem hr
#align euclidean.ball_mem_nhds Euclidean.ball_mem_nhds

end Euclidean

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : F → E} {n : ℕ∞}

theorem ContDiff.euclideanDist (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (h : ∀ x, f x ≠ g x) :
    ContDiff ℝ n fun x => Euclidean.dist (f x) (g x) := by
  simp only [Euclidean.dist]
  apply @ContDiff.dist ℝ
  exacts[(@toEuclidean E _ _ _).ContDiff.comp hf, (@toEuclidean E _ _ _).ContDiff.comp hg, fun x =>
    to_euclidean.injective.ne (h x)]
#align cont_diff.euclidean_dist ContDiff.euclideanDist

