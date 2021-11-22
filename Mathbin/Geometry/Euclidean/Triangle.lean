import Mathbin.Geometry.Euclidean.Basic 
import Mathbin.Tactic.IntervalCases

/-!
# Triangles

This file proves basic geometrical results about distances and angles
in (possibly degenerate) triangles in real inner product spaces and
Euclidean affine spaces.  More specialized results, and results
developed for simplices in general rather than just for triangles, are
in separate files.  Definitions and results that make sense in more
general affine spaces rather than just in the Euclidean case go under
`linear_algebra.affine_space`.

## Implementation notes

Results in this file are generally given in a form with only those
non-degeneracy conditions needed for the particular result, rather
than requiring affine independence of the points of a triangle
unnecessarily.

## References

* https://en.wikipedia.org/wiki/Pythagorean_theorem
* https://en.wikipedia.org/wiki/Law_of_cosines
* https://en.wikipedia.org/wiki/Pons_asinorum
* https://en.wikipedia.org/wiki/Sum_of_angles_of_a_triangle

-/


noncomputable theory

open_locale BigOperators

open_locale Classical

open_locale Real

open_locale RealInnerProductSpace

namespace InnerProductGeometry

/-!
### Geometrical results on triangles in real inner product spaces

This section develops some results on (possibly degenerate) triangles
in real inner product spaces, where those definitions and results can
most conveniently be developed in terms of vectors and then used to
deduce corresponding results for Euclidean affine spaces.
-/


variable{V : Type _}[InnerProductSpace ℝ V]

/-- Pythagorean theorem, if-and-only-if vector angle form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
  ((∥x+y∥*∥x+y∥) = (∥x∥*∥x∥)+∥y∥*∥y∥) ↔ angle x y = π / 2 :=
  by 
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
    exact inner_eq_zero_iff_angle_eq_pi_div_two x y

/-- Pythagorean theorem, vector angle form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) : (∥x+y∥*∥x+y∥) = (∥x∥*∥x∥)+∥y∥*∥y∥ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector angle form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two (x y : V) :
  ((∥x - y∥*∥x - y∥) = (∥x∥*∥x∥)+∥y∥*∥y∥) ↔ angle x y = π / 2 :=
  by 
    rw [norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
    exact inner_eq_zero_iff_angle_eq_pi_div_two x y

/-- Pythagorean theorem, subtracting vectors, vector angle form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq' (x y : V) (h : angle x y = π / 2) : (∥x - y∥*∥x - y∥) = (∥x∥*∥x∥)+∥y∥*∥y∥ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two x y).2 h

/-- Law of cosines (cosine rule), vector angle form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle (x y : V) :
  (∥x - y∥*∥x - y∥) = ((∥x∥*∥x∥)+∥y∥*∥y∥) - ((2*∥x∥)*∥y∥)*Real.cos (angle x y) :=
  by 
    rw
      [show (((2*∥x∥)*∥y∥)*Real.cos (angle x y)) = 2*Real.cos (angle x y)*∥x∥*∥y∥by 
        ring,
      cos_angle_mul_norm_mul_norm, ←real_inner_self_eq_norm_mul_norm, ←real_inner_self_eq_norm_mul_norm,
      ←real_inner_self_eq_norm_mul_norm, real_inner_sub_sub_self, sub_add_eq_add_sub]

/-- Pons asinorum, vector angle form. -/
theorem angle_sub_eq_angle_sub_rev_of_norm_eq {x y : V} (h : ∥x∥ = ∥y∥) : angle x (x - y) = angle y (y - x) :=
  by 
    refine' Real.inj_on_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨angle_nonneg _ _, angle_le_pi _ _⟩ _ 
    rw [cos_angle, cos_angle, h, ←neg_sub, norm_neg, neg_sub, inner_sub_right, inner_sub_right,
      real_inner_self_eq_norm_mul_norm, real_inner_self_eq_norm_mul_norm, h, real_inner_comm x y]

-- error in Geometry.Euclidean.Triangle: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contradiction: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- Converse of pons asinorum, vector angle form. -/
theorem norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi
{x y : V}
(h : «expr = »(angle x «expr - »(x, y), angle y «expr - »(y, x)))
(hpi : «expr ≠ »(angle x y, exprπ())) : «expr = »(«expr∥ ∥»(x), «expr∥ ∥»(y)) :=
begin
  replace [ident h] [] [":=", expr real.arccos_inj_on (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one x «expr - »(x, y))) (abs_le.mp (abs_real_inner_div_norm_mul_norm_le_one y «expr - »(y, x))) h],
  by_cases [expr hxy, ":", expr «expr = »(x, y)],
  { rw [expr hxy] [] },
  { rw ["[", "<-", expr norm_neg «expr - »(y, x), ",", expr neg_sub, ",", expr mul_comm, ",", expr mul_comm «expr∥ ∥»(y), ",", expr div_eq_mul_inv, ",", expr div_eq_mul_inv, ",", expr mul_inv_rev₀, ",", expr mul_inv_rev₀, ",", "<-", expr mul_assoc, ",", "<-", expr mul_assoc, "]"] ["at", ident h],
    replace [ident h] [] [":=", expr mul_right_cancel₀ (inv_ne_zero (λ
       hz, hxy (eq_of_sub_eq_zero (norm_eq_zero.1 hz)))) h],
    rw ["[", expr inner_sub_right, ",", expr inner_sub_right, ",", expr real_inner_comm x y, ",", expr real_inner_self_eq_norm_mul_norm, ",", expr real_inner_self_eq_norm_mul_norm, ",", expr mul_sub_right_distrib, ",", expr mul_sub_right_distrib, ",", expr mul_self_mul_inv, ",", expr mul_self_mul_inv, ",", expr sub_eq_sub_iff_sub_eq_sub, ",", "<-", expr mul_sub_left_distrib, "]"] ["at", ident h],
    by_cases [expr hx0, ":", expr «expr = »(x, 0)],
    { rw ["[", expr hx0, ",", expr norm_zero, ",", expr inner_zero_left, ",", expr zero_mul, ",", expr zero_sub, ",", expr neg_eq_zero, "]"] ["at", ident h],
      rw ["[", expr hx0, ",", expr norm_zero, ",", expr h, "]"] [] },
    { by_cases [expr hy0, ":", expr «expr = »(y, 0)],
      { rw ["[", expr hy0, ",", expr norm_zero, ",", expr inner_zero_right, ",", expr zero_mul, ",", expr sub_zero, "]"] ["at", ident h],
        rw ["[", expr hy0, ",", expr norm_zero, ",", expr h, "]"] [] },
      { rw ["[", expr inv_sub_inv (λ
          hz, hx0 (norm_eq_zero.1 hz)) (λ
          hz, hy0 (norm_eq_zero.1 hz)), ",", "<-", expr neg_sub, ",", "<-", expr mul_div_assoc, ",", expr mul_comm, ",", expr mul_div_assoc, ",", "<-", expr mul_neg_one, "]"] ["at", ident h],
        symmetry,
        by_contradiction [ident hyx],
        replace [ident h] [] [":=", expr (mul_left_cancel₀ (sub_ne_zero_of_ne hyx) h).symm],
        rw ["[", expr real_inner_div_norm_mul_norm_eq_neg_one_iff, ",", "<-", expr angle_eq_pi_iff, "]"] ["at", ident h],
        exact [expr hpi h] } } }
end

/-- The cosine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
theorem cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  Real.cos (angle x (x - y)+angle y (y - x)) = -Real.cos (angle x y) :=
  by 
    byCases' hxy : x = y
    ·
      rw [hxy, angle_self hy]
      simp 
    ·
      rw [Real.cos_add, cos_angle, cos_angle, cos_angle]
      have hxn : ∥x∥ ≠ 0 := fun h => hx (norm_eq_zero.1 h)
      have hyn : ∥y∥ ≠ 0 := fun h => hy (norm_eq_zero.1 h)
      have hxyn : ∥x - y∥ ≠ 0 := fun h => hxy (eq_of_sub_eq_zero (norm_eq_zero.1 h))
      apply mul_right_cancel₀ hxn 
      apply mul_right_cancel₀ hyn 
      apply mul_right_cancel₀ hxyn 
      apply mul_right_cancel₀ hxyn 
      have H1 :
        (((((Real.sin (angle x (x - y))*Real.sin (angle y (y - x)))*∥x∥)*∥y∥)*∥x - y∥)*∥x - y∥) =
          (Real.sin (angle x (x - y))*∥x∥*∥x - y∥)*Real.sin (angle y (y - x))*∥y∥*∥x - y∥
      ·
        ring 
      have H2 :
        ((⟪x, x⟫*inner x x - inner x y - (inner x y - inner y y)) - (inner x x - inner x y)*inner x x - inner x y) =
          (inner x x*inner y y) - inner x y*inner x y
      ·
        ring 
      have H3 :
        ((⟪y, y⟫*inner y y - inner x y - (inner x y - inner x x)) - (inner y y - inner x y)*inner y y - inner x y) =
          (inner x x*inner y y) - inner x y*inner x y
      ·
        ring 
      rw [mul_sub_right_distrib, mul_sub_right_distrib, mul_sub_right_distrib, mul_sub_right_distrib, H1,
        sin_angle_mul_norm_mul_norm, norm_sub_rev x y, sin_angle_mul_norm_mul_norm, norm_sub_rev y x, inner_sub_left,
        inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_right, inner_sub_right, real_inner_comm x y, H2, H3,
        Real.mul_self_sqrt (sub_nonneg_of_le (real_inner_mul_inner_self_le x y)), real_inner_self_eq_norm_mul_norm,
        real_inner_self_eq_norm_mul_norm, real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
      fieldSimp [hxn, hyn, hxyn]
      ring

/-- The sine of the sum of two angles in a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
theorem sin_angle_sub_add_angle_sub_rev_eq_sin_angle {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  Real.sin (angle x (x - y)+angle y (y - x)) = Real.sin (angle x y) :=
  by 
    byCases' hxy : x = y
    ·
      rw [hxy, angle_self hy]
      simp 
    ·
      rw [Real.sin_add, cos_angle, cos_angle]
      have hxn : ∥x∥ ≠ 0 := fun h => hx (norm_eq_zero.1 h)
      have hyn : ∥y∥ ≠ 0 := fun h => hy (norm_eq_zero.1 h)
      have hxyn : ∥x - y∥ ≠ 0 := fun h => hxy (eq_of_sub_eq_zero (norm_eq_zero.1 h))
      apply mul_right_cancel₀ hxn 
      apply mul_right_cancel₀ hyn 
      apply mul_right_cancel₀ hxyn 
      apply mul_right_cancel₀ hxyn 
      have H1 :
        ((((Real.sin (angle x (x - y))*⟪y, y - x⟫ / ∥y∥*∥y - x∥)*∥x∥)*∥y∥)*∥x - y∥) =
          ((Real.sin (angle x (x - y))*∥x∥*∥x - y∥)*⟪y, y - x⟫ / ∥y∥*∥y - x∥)*∥y∥
      ·
        ring 
      have H2 :
        (((((⟪x, x - y⟫ / ∥x∥*∥y - x∥)*Real.sin (angle y (y - x)))*∥x∥)*∥y∥)*∥y - x∥) =
          ((⟪x, x - y⟫ / ∥x∥*∥y - x∥)*Real.sin (angle y (y - x))*∥y∥*∥y - x∥)*∥x∥
      ·
        ring 
      have H3 :
        ((⟪x, x⟫*⟪x, x⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪y, y⟫)) - (⟪x, x⟫ - ⟪x, y⟫)*⟪x, x⟫ - ⟪x, y⟫) =
          (⟪x, x⟫*⟪y, y⟫) - ⟪x, y⟫*⟪x, y⟫
      ·
        ring 
      have H4 :
        ((⟪y, y⟫*⟪y, y⟫ - ⟪x, y⟫ - (⟪x, y⟫ - ⟪x, x⟫)) - (⟪y, y⟫ - ⟪x, y⟫)*⟪y, y⟫ - ⟪x, y⟫) =
          (⟪x, x⟫*⟪y, y⟫) - ⟪x, y⟫*⟪x, y⟫
      ·
        ring 
      rw [right_distrib, right_distrib, right_distrib, right_distrib, H1, sin_angle_mul_norm_mul_norm, norm_sub_rev x y,
        H2, sin_angle_mul_norm_mul_norm, norm_sub_rev y x, mul_assocₓ (Real.sin (angle x y)),
        sin_angle_mul_norm_mul_norm, inner_sub_left, inner_sub_left, inner_sub_right, inner_sub_right, inner_sub_right,
        inner_sub_right, real_inner_comm x y, H3, H4, real_inner_self_eq_norm_mul_norm,
        real_inner_self_eq_norm_mul_norm, real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
      fieldSimp [hxn, hyn, hxyn]
      ring

/-- The cosine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
theorem cos_angle_add_angle_sub_add_angle_sub_eq_neg_one {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  Real.cos ((angle x y+angle x (x - y))+angle y (y - x)) = -1 :=
  by 
    rw [add_assocₓ, Real.cos_add, cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle hx hy,
      sin_angle_sub_add_angle_sub_rev_eq_sin_angle hx hy, ←neg_mul_eq_mul_neg, ←neg_add', add_commₓ, ←sq, ←sq,
      Real.sin_sq_add_cos_sq]

/-- The sine of the sum of the angles of a possibly degenerate
triangle (where two given sides are nonzero), vector angle form. -/
theorem sin_angle_add_angle_sub_add_angle_sub_eq_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
  Real.sin ((angle x y+angle x (x - y))+angle y (y - x)) = 0 :=
  by 
    rw [add_assocₓ, Real.sin_add, cos_angle_sub_add_angle_sub_rev_eq_neg_cos_angle hx hy,
      sin_angle_sub_add_angle_sub_rev_eq_sin_angle hx hy]
    ring

-- error in Geometry.Euclidean.Triangle: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contradiction: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- The sum of the angles of a possibly degenerate triangle (where the
two given sides are nonzero), vector angle form. -/
theorem angle_add_angle_sub_add_angle_sub_eq_pi
{x y : V}
(hx : «expr ≠ »(x, 0))
(hy : «expr ≠ »(y, 0)) : «expr = »(«expr + »(«expr + »(angle x y, angle x «expr - »(x, y)), angle y «expr - »(y, x)), exprπ()) :=
begin
  have [ident hcos] [] [":=", expr cos_angle_add_angle_sub_add_angle_sub_eq_neg_one hx hy],
  have [ident hsin] [] [":=", expr sin_angle_add_angle_sub_add_angle_sub_eq_zero hx hy],
  rw [expr real.sin_eq_zero_iff] ["at", ident hsin],
  cases [expr hsin] ["with", ident n, ident hn],
  symmetry' ["at", ident hn],
  have [ident h0] [":", expr «expr ≤ »(0, «expr + »(«expr + »(angle x y, angle x «expr - »(x, y)), angle y «expr - »(y, x)))] [":=", expr add_nonneg (add_nonneg (angle_nonneg _ _) (angle_nonneg _ _)) (angle_nonneg _ _)],
  have [ident h3] [":", expr «expr ≤ »(«expr + »(«expr + »(angle x y, angle x «expr - »(x, y)), angle y «expr - »(y, x)), «expr + »(«expr + »(exprπ(), exprπ()), exprπ()))] [":=", expr add_le_add (add_le_add (angle_le_pi _ _) (angle_le_pi _ _)) (angle_le_pi _ _)],
  have [ident h3lt] [":", expr «expr < »(«expr + »(«expr + »(angle x y, angle x «expr - »(x, y)), angle y «expr - »(y, x)), «expr + »(«expr + »(exprπ(), exprπ()), exprπ()))] [],
  { by_contradiction [ident hnlt],
    have [ident hxy] [":", expr «expr = »(angle x y, exprπ())] [],
    { by_contradiction [ident hxy],
      exact [expr hnlt (add_lt_add_of_lt_of_le (add_lt_add_of_lt_of_le (lt_of_le_of_ne (angle_le_pi _ _) hxy) (angle_le_pi _ _)) (angle_le_pi _ _))] },
    rw [expr hxy] ["at", ident hnlt],
    rw [expr angle_eq_pi_iff] ["at", ident hxy],
    rcases [expr hxy, "with", "⟨", ident hx, ",", "⟨", ident r, ",", "⟨", ident hr, ",", ident hxr, "⟩", "⟩", "⟩"],
    rw ["[", expr hxr, ",", "<-", expr one_smul exprℝ() x, ",", "<-", expr mul_smul, ",", expr mul_one, ",", "<-", expr sub_smul, ",", expr one_smul, ",", expr sub_eq_add_neg, ",", expr angle_smul_right_of_pos _ _ (add_pos zero_lt_one (neg_pos_of_neg hr)), ",", expr angle_self hx, ",", expr add_zero, "]"] ["at", ident hnlt],
    apply [expr hnlt],
    rw [expr add_assoc] [],
    exact [expr add_lt_add_left (lt_of_le_of_lt (angle_le_pi _ _) (lt_add_of_pos_right exprπ() real.pi_pos)) _] },
  have [ident hn0] [":", expr «expr ≤ »(0, n)] [],
  { rw ["[", expr hn, ",", expr mul_nonneg_iff_right_nonneg_of_pos real.pi_pos, "]"] ["at", ident h0],
    norm_cast ["at", ident h0],
    exact [expr h0] },
  have [ident hn3] [":", expr «expr < »(n, 3)] [],
  { rw ["[", expr hn, ",", expr show «expr = »(«expr + »(«expr + »(exprπ(), exprπ()), exprπ()), «expr * »(3, exprπ())), by ring [], "]"] ["at", ident h3lt],
    replace [ident h3lt] [] [":=", expr lt_of_mul_lt_mul_right h3lt (le_of_lt real.pi_pos)],
    norm_cast ["at", ident h3lt],
    exact [expr h3lt] },
  interval_cases [expr n] [] [],
  { rw [expr hn] ["at", ident hcos],
    simp [] [] [] [] [] ["at", ident hcos],
    norm_num [] ["at", ident hcos] },
  { rw [expr hn] [],
    norm_num [] [] },
  { rw [expr hn] ["at", ident hcos],
    simp [] [] [] [] [] ["at", ident hcos],
    norm_num [] ["at", ident hcos] }
end

end InnerProductGeometry

namespace EuclideanGeometry

/-!
### Geometrical results on triangles in Euclidean affine spaces

This section develops some geometrical definitions and results on
(possible degenerate) triangles in Euclidean affine spaces.
-/


open InnerProductGeometry

open_locale EuclideanGeometry

variable{V : Type _}{P : Type _}[InnerProductSpace ℝ V][MetricSpace P][NormedAddTorsor V P]

include V

/-- **Pythagorean theorem**, if-and-only-if angle-at-point form. -/
theorem dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two (p1 p2 p3 : P) :
  ((dist p1 p3*dist p1 p3) = (dist p1 p2*dist p1 p2)+dist p3 p2*dist p3 p2) ↔ ∠ p1 p2 p3 = π / 2 :=
  by 
    erw [PseudoMetricSpace.dist_comm p3 p2, dist_eq_norm_vsub V p1 p3, dist_eq_norm_vsub V p1 p2,
      dist_eq_norm_vsub V p2 p3, ←norm_sub_sq_eq_norm_sq_add_norm_sq_iff_angle_eq_pi_div_two,
      vsub_sub_vsub_cancel_right p1, ←neg_vsub_eq_vsub_rev p2 p3, norm_neg]

/-- **Law of cosines** (cosine rule), angle-at-point form. -/
theorem dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle (p1 p2 p3 : P) :
  (dist p1 p3*dist p1 p3) =
    ((dist p1 p2*dist p1 p2)+dist p3 p2*dist p3 p2) - ((2*dist p1 p2)*dist p3 p2)*Real.cos (∠ p1 p2 p3) :=
  by 
    rw [dist_eq_norm_vsub V p1 p3, dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p3 p2]
    unfold angle 
    convert norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle (p1 -ᵥ p2 : V) (p3 -ᵥ p2 : V)
    ·
      exact (vsub_sub_vsub_cancel_right p1 p3 p2).symm
    ·
      exact (vsub_sub_vsub_cancel_right p1 p3 p2).symm

alias dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle ← law_cos

/-- **Isosceles Triangle Theorem**: Pons asinorum, angle-at-point form. -/
theorem angle_eq_angle_of_dist_eq {p1 p2 p3 : P} (h : dist p1 p2 = dist p1 p3) : ∠ p1 p2 p3 = ∠ p1 p3 p2 :=
  by 
    rw [dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p1 p3] at h 
    unfold angle 
    convert angle_sub_eq_angle_sub_rev_of_norm_eq h
    ·
      exact (vsub_sub_vsub_cancel_left p3 p2 p1).symm
    ·
      exact (vsub_sub_vsub_cancel_left p2 p3 p1).symm

/-- Converse of pons asinorum, angle-at-point form. -/
theorem dist_eq_of_angle_eq_angle_of_angle_ne_pi {p1 p2 p3 : P} (h : ∠ p1 p2 p3 = ∠ p1 p3 p2) (hpi : ∠ p2 p1 p3 ≠ π) :
  dist p1 p2 = dist p1 p3 :=
  by 
    unfold angle  at h hpi 
    rw [dist_eq_norm_vsub V p1 p2, dist_eq_norm_vsub V p1 p3]
    rw [←angle_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev] at hpi 
    rw [←vsub_sub_vsub_cancel_left p3 p2 p1, ←vsub_sub_vsub_cancel_left p2 p3 p1] at h 
    exact norm_eq_of_angle_sub_eq_angle_sub_rev_of_angle_ne_pi h hpi

/-- The **sum of the angles of a triangle** (possibly degenerate, where the
given vertex is distinct from the others), angle-at-point. -/
theorem angle_add_angle_add_angle_eq_pi {p1 p2 p3 : P} (h2 : p2 ≠ p1) (h3 : p3 ≠ p1) :
  ((∠ p1 p2 p3+∠ p2 p3 p1)+∠ p3 p1 p2) = π :=
  by 
    rw [add_assocₓ, add_commₓ, add_commₓ (∠ p2 p3 p1), angle_comm p2 p3 p1]
    unfold angle 
    rw [←angle_neg_neg (p1 -ᵥ p3), ←angle_neg_neg (p1 -ᵥ p2), neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev,
      neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, ←vsub_sub_vsub_cancel_right p3 p2 p1,
      ←vsub_sub_vsub_cancel_right p2 p3 p1]
    exact
      angle_add_angle_sub_add_angle_sub_eq_pi (fun he => h3 (vsub_eq_zero_iff_eq.1 he))
        fun he => h2 (vsub_eq_zero_iff_eq.1 he)

/-- **Stewart's Theorem**. -/
theorem dist_sq_mul_dist_add_dist_sq_mul_dist (a b c p : P) (h : ∠ b p c = π) :
  (((dist a b^2)*dist c p)+(dist a c^2)*dist b p) = dist b c*(dist a p^2)+dist b p*dist c p :=
  by 
    rw [pow_two, pow_two, law_cos a p b, law_cos a p c, eq_sub_of_add_eq (angle_add_angle_eq_pi_of_angle_eq_pi a h),
      Real.cos_pi_sub, dist_eq_add_dist_of_angle_eq_pi h]
    ring

/-- **Apollonius's Theorem**. -/
theorem dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq (a b c : P) :
  ((dist a b^2)+dist a c^2) = 2*(dist a (midpoint ℝ b c)^2)+dist b c / 2^2 :=
  by 
    byCases' hbc : b = c
    ·
      simp [hbc, midpoint_self, dist_self, two_mul]
    ·
      let m := midpoint ℝ b c 
      have  : dist b c ≠ 0 := (dist_pos.mpr hbc).ne' 
      have hm := dist_sq_mul_dist_add_dist_sq_mul_dist a b c m (angle_midpoint_eq_pi b c hbc)
      simp only [dist_left_midpoint, dist_right_midpoint, Real.norm_two] at hm 
      calc ((dist a b^2)+dist a c^2) = (2 / dist b c)*((dist a b^2)*2⁻¹*dist b c)+(dist a c^2)*2⁻¹*dist b c :=
        by 
          fieldSimp 
          ring _ = 2*(dist a (midpoint ℝ b c)^2)+dist b c / 2^2 :=
        by 
          rw [hm]
          fieldSimp 
          ring

theorem dist_mul_of_eq_angle_of_dist_mul (a b c a' b' c' : P) (r : ℝ) (h : ∠ a' b' c' = ∠ a b c)
  (hab : dist a' b' = r*dist a b) (hcb : dist c' b' = r*dist c b) : dist a' c' = r*dist a c :=
  by 
    have h' : (dist a' c'^2) = ((r*dist a c)^2)
    calc (dist a' c'^2) = ((dist a' b'^2)+dist c' b'^2) - ((2*dist a' b')*dist c' b')*Real.cos (∠ a' b' c') :=
      by 
        simp [pow_two,
          law_cos a' b' c']_ = (r^2)*((dist a b^2)+dist c b^2) - ((2*dist a b)*dist c b)*Real.cos (∠ a b c) :=
      by 
        rw [h, hab, hcb]
        ring _ = ((r*dist a c)^2) :=
      by 
        simp [pow_two, ←law_cos a b c, mul_powₓ]
    byCases' hab₁ : a = b
    ·
      have hab'₁ : a' = b'
      ·
        rw [←dist_eq_zero, hab, dist_eq_zero.mpr hab₁, mul_zero r]
      rw [hab₁, hab'₁, dist_comm b' c', dist_comm b c, hcb]
    ·
      have h1 : 0 ≤ r*dist a b
      ·
        rw [←hab]
        exact dist_nonneg 
      have h2 : 0 ≤ r := nonneg_of_mul_nonneg_right h1 (dist_pos.mpr hab₁)
      exact (sq_eq_sq dist_nonneg (mul_nonneg h2 dist_nonneg)).mp h'

end EuclideanGeometry

