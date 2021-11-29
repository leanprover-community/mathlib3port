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


open_locale TopologicalSpace

open Set

variable{E : Type _}[NormedGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]

noncomputable theory

/-- If `E` is a finite dimensional space over `ℝ`, then `to_euclidean` is a continuous `ℝ`-linear
equivalence between `E` and the Euclidean space of the same dimension. -/
def toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Finₓ$ FiniteDimensional.finrank ℝ E) :=
  ContinuousLinearEquiv.ofFinrankEq finrank_euclidean_space_fin.symm

namespace Euclidean

/-- If `x` and `y` are two points in a finite dimensional space over `ℝ`, then `euclidean.dist x y`
is the distance between these points in the metric defined by some inner product space structure on
`E`. -/
def dist (x y : E) : ℝ :=
  dist (toEuclidean x) (toEuclidean y)

/-- Closed ball w.r.t. the euclidean distance. -/
def closed_ball (x : E) (r : ℝ) : Set E :=
  { y | dist y x ≤ r }

/-- Open ball w.r.t. the euclidean distance. -/
def ball (x : E) (r : ℝ) : Set E :=
  { y | dist y x < r }

theorem ball_eq_preimage (x : E) (r : ℝ) : ball x r = toEuclidean ⁻¹' Metric.Ball (toEuclidean x) r :=
  rfl

theorem closed_ball_eq_preimage (x : E) (r : ℝ) :
  closed_ball x r = toEuclidean ⁻¹' Metric.ClosedBall (toEuclidean x) r :=
  rfl

-- error in Analysis.InnerProductSpace.EuclideanDist: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem ball_subset_closed_ball {x : E} {r : exprℝ()} : «expr ⊆ »(ball x r, closed_ball x r) :=
λ (y) (hy : «expr < »(_, _)), le_of_lt hy

theorem is_open_ball {x : E} {r : ℝ} : IsOpen (ball x r) :=
  Metric.is_open_ball.Preimage toEuclidean.Continuous

theorem mem_ball_self {x : E} {r : ℝ} (hr : 0 < r) : x ∈ ball x r :=
  Metric.mem_ball_self hr

theorem closed_ball_eq_image (x : E) (r : ℝ) :
  closed_ball x r = toEuclidean.symm '' Metric.ClosedBall (toEuclidean x) r :=
  by 
    rw [to_euclidean.image_symm_eq_preimage, closed_ball_eq_preimage]

theorem is_compact_closed_ball {x : E} {r : ℝ} : IsCompact (closed_ball x r) :=
  by 
    rw [closed_ball_eq_image]
    exact (ProperSpace.is_compact_closed_ball _ _).Image to_euclidean.symm.continuous

theorem is_closed_closed_ball {x : E} {r : ℝ} : IsClosed (closed_ball x r) :=
  is_compact_closed_ball.IsClosed

theorem closure_ball (x : E) {r : ℝ} (h : 0 < r) : Closure (ball x r) = closed_ball x r :=
  by 
    rw [ball_eq_preimage, ←to_euclidean.preimage_closure, closure_ball (toEuclidean x) h, closed_ball_eq_preimage]

theorem exists_pos_lt_subset_ball {R : ℝ} {s : Set E} {x : E} (hR : 0 < R) (hs : IsClosed s) (h : s ⊆ ball x R) :
  ∃ (r : _)(_ : r ∈ Ioo 0 R), s ⊆ ball x r :=
  by 
    rw [ball_eq_preimage, ←image_subset_iff] at h 
    rcases exists_pos_lt_subset_ball hR (to_euclidean.is_closed_image.2 hs) h with ⟨r, hr, hsr⟩
    exact ⟨r, hr, image_subset_iff.1 hsr⟩

-- error in Analysis.InnerProductSpace.EuclideanDist: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem nhds_basis_closed_ball {x : E} : (expr𝓝() x).has_basis (λ r : exprℝ(), «expr < »(0, r)) (closed_ball x) :=
begin
  rw ["[", expr to_euclidean.to_homeomorph.nhds_eq_comap, "]"] [],
  exact [expr metric.nhds_basis_closed_ball.comap _]
end

theorem closed_ball_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : closed_ball x r ∈ 𝓝 x :=
  nhds_basis_closed_ball.mem_of_mem hr

-- error in Analysis.InnerProductSpace.EuclideanDist: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem nhds_basis_ball {x : E} : (expr𝓝() x).has_basis (λ r : exprℝ(), «expr < »(0, r)) (ball x) :=
begin
  rw ["[", expr to_euclidean.to_homeomorph.nhds_eq_comap, "]"] [],
  exact [expr metric.nhds_basis_ball.comap _]
end

theorem ball_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : ball x r ∈ 𝓝 x :=
  nhds_basis_ball.mem_of_mem hr

end Euclidean

variable{F : Type _}[NormedGroup F][NormedSpace ℝ F]{f g : F → E}{n : WithTop ℕ}

theorem TimesContDiff.euclidean_dist (hf : TimesContDiff ℝ n f) (hg : TimesContDiff ℝ n g) (h : ∀ x, f x ≠ g x) :
  TimesContDiff ℝ n fun x => Euclidean.dist (f x) (g x) :=
  by 
    simp only [Euclidean.dist]
    apply @TimesContDiff.dist ℝ 
    exacts[(@toEuclidean E _ _ _).TimesContDiff.comp hf, (@toEuclidean E _ _ _).TimesContDiff.comp hg,
      fun x => to_euclidean.injective.ne (h x)]

