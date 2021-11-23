import Mathbin.Geometry.Euclidean.Triangle

/-!
# Spheres

This file proves basic geometrical results about distances and angles
in spheres in real inner product spaces and Euclidean affine spaces.

## Main theorems

* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi`: Intersecting Chords Theorem (Freek No. 55).
* `mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero`: Intersecting Secants Theorem.
* `mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`: Ptolemy’s Theorem (Freek No. 95).

TODO: The current statement of Ptolemy’s theorem works around the lack of a "cyclic polygon" concept
in mathlib, which is what the theorem statement would naturally use (or two such concepts, since
both a strict version, where all vertices must be distinct, and a weak version, where consecutive
vertices may be equal, would be useful; Ptolemy's theorem should then use the weak one).

An API needs to be built around that concept, which would include:
- strict cyclic implies weak cyclic,
- weak cyclic and consecutive points distinct implies strict cyclic,
- weak/strict cyclic implies weak/strict cyclic for any subsequence,
- any three points on a sphere are weakly or strictly cyclic according to whether they are distinct,
- any number of points on a sphere intersected with a two-dimensional affine subspace are cyclic in
  some order,
- a list of points is cyclic if and only if its reversal is,
- a list of points is cyclic if and only if any cyclic permutation is, while other permutations
  are not when the points are distinct,
- a point P where the diagonals of a cyclic polygon cross exists (and is unique) with weak/strict
  betweenness depending on weak/strict cyclicity,
- four points on a sphere with such a point P are cyclic in the appropriate order,
and so on.
-/


open Real

open_locale EuclideanGeometry RealInnerProductSpace Real

variable{V : Type _}[InnerProductSpace ℝ V]

namespace InnerProductGeometry

/-!
### Geometrical results on spheres in real inner product spaces

This section develops some results on spheres in real inner product spaces,
which are used to deduce corresponding results for Euclidean affine spaces.
-/


-- error in Geometry.Euclidean.Sphere: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_norm_eq_abs_sub_sq_norm
{x y z : V}
(h₁ : «expr∃ , »((k : exprℝ()), «expr ∧ »(«expr ≠ »(k, 1), «expr = »(«expr + »(x, y), «expr • »(k, «expr - »(x, y))))))
(h₂ : «expr = »(«expr∥ ∥»(«expr - »(z, y)), «expr∥ ∥»(«expr + »(z, y)))) : «expr = »(«expr * »(«expr∥ ∥»(«expr - »(x, y)), «expr∥ ∥»(«expr + »(x, y))), «expr| |»(«expr - »(«expr ^ »(«expr∥ ∥»(«expr + »(z, y)), 2), «expr ^ »(«expr∥ ∥»(«expr - »(z, x)), 2)))) :=
begin
  obtain ["⟨", ident k, ",", ident hk_ne_one, ",", ident hk, "⟩", ":=", expr h₁],
  let [ident r] [] [":=", expr «expr * »(«expr ⁻¹»(«expr - »(k, 1)), «expr + »(k, 1))],
  have [ident hxy] [":", expr «expr = »(x, «expr • »(r, y))] [],
  { rw ["[", "<-", expr smul_smul, ",", expr eq_inv_smul_iff₀ (sub_ne_zero.mpr hk_ne_one), ",", "<-", expr sub_eq_zero, "]"] [],
    calc
      «expr = »(«expr - »(«expr • »(«expr - »(k, 1), x), «expr • »(«expr + »(k, 1), y)), «expr - »(«expr - »(«expr • »(k, x), x), «expr + »(«expr • »(k, y), y))) : by simp_rw ["[", expr sub_smul, ",", expr add_smul, ",", expr one_smul, "]"] []
      «expr = »(..., «expr - »(«expr - »(«expr • »(k, x), «expr • »(k, y)), «expr + »(x, y))) : by simp_rw ["[", "<-", expr sub_sub, ",", expr sub_right_comm, "]"] []
      «expr = »(..., «expr - »(«expr • »(k, «expr - »(x, y)), «expr + »(x, y))) : by rw ["<-", expr smul_sub k x y] []
      «expr = »(..., 0) : sub_eq_zero.mpr hk.symm },
  have [ident hzy] [":", expr «expr = »(«expr⟪ , ⟫»(z, y), 0)] [],
  by rwa ["[", expr inner_eq_zero_iff_angle_eq_pi_div_two, ",", "<-", expr norm_add_eq_norm_sub_iff_angle_eq_pi_div_two, ",", expr eq_comm, "]"] [],
  have [ident hzx] [":", expr «expr = »(«expr⟪ , ⟫»(z, x), 0)] [":=", expr by rw ["[", expr hxy, ",", expr inner_smul_right, ",", expr hzy, ",", expr mul_zero, "]"] []],
  calc
    «expr = »(«expr * »(«expr∥ ∥»(«expr - »(x, y)), «expr∥ ∥»(«expr + »(x, y))), «expr * »(«expr∥ ∥»(«expr • »(«expr - »(r, 1), y)), «expr∥ ∥»(«expr • »(«expr + »(r, 1), y)))) : by simp [] [] [] ["[", expr sub_smul, ",", expr add_smul, ",", expr hxy, "]"] [] []
    «expr = »(..., «expr * »(«expr * »(«expr∥ ∥»(«expr - »(r, 1)), «expr∥ ∥»(y)), «expr * »(«expr∥ ∥»(«expr + »(r, 1)), «expr∥ ∥»(y)))) : by simp_rw ["[", expr norm_smul, "]"] []
    «expr = »(..., «expr * »(«expr * »(«expr∥ ∥»(«expr - »(r, 1)), «expr∥ ∥»(«expr + »(r, 1))), «expr ^ »(«expr∥ ∥»(y), 2))) : by ring []
    «expr = »(..., «expr| |»(«expr * »(«expr * »(«expr - »(r, 1), «expr + »(r, 1)), «expr ^ »(«expr∥ ∥»(y), 2)))) : by simp [] [] [] ["[", expr abs_mul, ",", expr norm_eq_abs, "]"] [] []
    «expr = »(..., «expr| |»(«expr - »(«expr * »(«expr ^ »(r, 2), «expr ^ »(«expr∥ ∥»(y), 2)), «expr ^ »(«expr∥ ∥»(y), 2)))) : by ring_nf [] [] []
    «expr = »(..., «expr| |»(«expr - »(«expr ^ »(«expr∥ ∥»(x), 2), «expr ^ »(«expr∥ ∥»(y), 2)))) : by simp [] [] [] ["[", expr hxy, ",", expr norm_smul, ",", expr mul_pow, ",", expr norm_eq_abs, ",", expr sq_abs, "]"] [] []
    «expr = »(..., «expr| |»(«expr - »(«expr ^ »(«expr∥ ∥»(«expr + »(z, y)), 2), «expr ^ »(«expr∥ ∥»(«expr - »(z, x)), 2)))) : by simp [] [] [] ["[", expr norm_add_sq_real, ",", expr norm_sub_sq_real, ",", expr hzy, ",", expr hzx, ",", expr abs_sub_comm, "]"] [] []
end

end InnerProductGeometry

namespace EuclideanGeometry

/-!
### Geometrical results on spheres in Euclidean affine spaces

This section develops some results on spheres in Euclidean affine spaces.
-/


open InnerProductGeometry

variable{P : Type _}[MetricSpace P][NormedAddTorsor V P]

include V

-- error in Geometry.Euclidean.Sphere: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `P` is a point on the line `AB` and `Q` is equidistant from `A` and `B`, then
`AP * BP = abs (BQ ^ 2 - PQ ^ 2)`. -/
theorem mul_dist_eq_abs_sub_sq_dist
{a b p q : P}
(hp : «expr∃ , »((k : exprℝ()), «expr ∧ »(«expr ≠ »(k, 1), «expr = »(«expr -ᵥ »(b, p), «expr • »(k, «expr -ᵥ »(a, p))))))
(hq : «expr = »(dist a q, dist b q)) : «expr = »(«expr * »(dist a p, dist b p), «expr| |»(«expr - »(«expr ^ »(dist b q, 2), «expr ^ »(dist p q, 2)))) :=
begin
  let [ident m] [":", expr P] [":=", expr midpoint exprℝ() a b],
  obtain ["⟨", ident v, ",", ident h1, ",", ident h2, ",", ident h3, "⟩", ":=", "⟨", expr vsub_sub_vsub_cancel_left, ",", expr v a p m, ",", expr v p q m, ",", expr v a q m, "⟩"],
  have [ident h] [":", expr ∀
   r, «expr = »(«expr -ᵥ »(b, r), «expr + »(«expr -ᵥ »(m, r), «expr -ᵥ »(m, a)))] [":=", expr λ
   r, by rw ["[", expr midpoint_vsub_left, ",", "<-", expr right_vsub_midpoint, ",", expr add_comm, ",", expr vsub_add_vsub_cancel, "]"] []],
  iterate [4] { rw [expr dist_eq_norm_vsub V] [] },
  rw ["[", "<-", expr h1, ",", "<-", expr h2, ",", expr h, ",", expr h, "]"] [],
  rw ["[", "<-", expr h1, ",", expr h, "]"] ["at", ident hp],
  rw ["[", expr dist_eq_norm_vsub V a q, ",", expr dist_eq_norm_vsub V b q, ",", "<-", expr h3, ",", expr h, "]"] ["at", ident hq],
  exact [expr mul_norm_eq_abs_sub_sq_norm hp hq]
end

/-- If `A`, `B`, `C`, `D` are cospherical and `P` is on both lines `AB` and `CD`, then
`AP * BP = CP * DP`. -/
theorem mul_dist_eq_mul_dist_of_cospherical {a b c d p : P} (h : cospherical ({a, b, c, d} : Set P))
  (hapb : ∃ k₁ : ℝ, k₁ ≠ 1 ∧ b -ᵥ p = k₁ • (a -ᵥ p)) (hcpd : ∃ k₂ : ℝ, k₂ ≠ 1 ∧ d -ᵥ p = k₂ • (c -ᵥ p)) :
  (dist a p*dist b p) = dist c p*dist d p :=
  by 
    obtain ⟨q, r, h'⟩ := (cospherical_def {a, b, c, d}).mp h 
    obtain ⟨ha, hb, hc, hd⟩ := h' a _, h' b _, h' c _, h' d _
    ·
      rw [←hd] at hc 
      rw [←hb] at ha 
      rw [mul_dist_eq_abs_sub_sq_dist hapb ha, hb, mul_dist_eq_abs_sub_sq_dist hcpd hc, hd]
    all_goals 
      simp 

/-- **Intersecting Chords Theorem**. -/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi {a b c d p : P} (h : cospherical ({a, b, c, d} : Set P))
  (hapb : ∠ a p b = π) (hcpd : ∠ c p d = π) : (dist a p*dist b p) = dist c p*dist d p :=
  by 
    obtain ⟨-, k₁, _, hab⟩ := angle_eq_pi_iff.mp hapb 
    obtain ⟨-, k₂, _, hcd⟩ := angle_eq_pi_iff.mp hcpd 
    exact
      mul_dist_eq_mul_dist_of_cospherical h
        ⟨k₁,
          by 
            linarith,
          hab⟩
        ⟨k₂,
          by 
            linarith,
          hcd⟩

/-- **Intersecting Secants Theorem**. -/
theorem mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero {a b c d p : P} (h : cospherical ({a, b, c, d} : Set P))
  (hab : a ≠ b) (hcd : c ≠ d) (hapb : ∠ a p b = 0) (hcpd : ∠ c p d = 0) : (dist a p*dist b p) = dist c p*dist d p :=
  by 
    obtain ⟨-, k₁, -, hab₁⟩ := angle_eq_zero_iff.mp hapb 
    obtain ⟨-, k₂, -, hcd₁⟩ := angle_eq_zero_iff.mp hcpd 
    refine' mul_dist_eq_mul_dist_of_cospherical h ⟨k₁, _, hab₁⟩ ⟨k₂, _, hcd₁⟩ <;>
      byContra hnot <;> simp_all only [not_not, one_smul]
    exacts[hab (vsub_left_cancel hab₁).symm, hcd (vsub_left_cancel hcd₁).symm]

-- error in Geometry.Euclidean.Sphere: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Ptolemy’s Theorem**. -/
theorem mul_dist_add_mul_dist_eq_mul_dist_of_cospherical
{a b c d p : P}
(h : cospherical ({a, b, c, d} : set P))
(hapc : «expr = »(«expr∠»() a p c, exprπ()))
(hbpd : «expr = »(«expr∠»() b p d, exprπ())) : «expr = »(«expr + »(«expr * »(dist a b, dist c d), «expr * »(dist b c, dist d a)), «expr * »(dist a c, dist b d)) :=
begin
  have [ident h'] [":", expr cospherical ({a, c, b, d} : set P)] [],
  { rwa [expr set.insert_comm c b {d}] [] },
  have [ident hmul] [] [":=", expr mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi h' hapc hbpd],
  have [ident hbp] [] [":=", expr left_dist_ne_zero_of_angle_eq_pi hbpd],
  have [ident h₁] [":", expr «expr = »(dist c d, «expr * »(«expr / »(dist c p, dist b p), dist a b))] [],
  { rw ["[", expr dist_mul_of_eq_angle_of_dist_mul b p a c p d, ",", expr dist_comm a b, "]"] [],
    { rw ["[", expr angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hbpd hapc, ",", expr angle_comm, "]"] [] },
    all_goals { field_simp [] ["[", expr mul_comm, ",", expr hmul, "]"] [] [] } },
  have [ident h₂] [":", expr «expr = »(dist d a, «expr * »(«expr / »(dist a p, dist b p), dist b c))] [],
  { rw ["[", expr dist_mul_of_eq_angle_of_dist_mul c p b d p a, ",", expr dist_comm c b, "]"] [],
    { rwa ["[", expr angle_comm, ",", expr angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi, "]"] [],
      rwa [expr angle_comm] [] },
    all_goals { field_simp [] ["[", expr mul_comm, ",", expr hmul, "]"] [] [] } },
  have [ident h₃] [":", expr «expr = »(dist d p, «expr / »(«expr * »(dist a p, dist c p), dist b p))] [],
  { field_simp [] ["[", expr mul_comm, ",", expr hmul, "]"] [] [] },
  have [ident h₄] [":", expr ∀
   x
   y : exprℝ(), «expr = »(«expr * »(x, «expr * »(y, x)), «expr * »(«expr * »(x, x), y))] [":=", expr λ
   x y, by rw ["[", expr mul_left_comm, ",", expr mul_comm, "]"] []],
  field_simp [] ["[", expr h₁, ",", expr h₂, ",", expr dist_eq_add_dist_of_angle_eq_pi hbpd, ",", expr h₃, ",", expr hbp, ",", expr dist_comm a b, ",", expr h₄, ",", "<-", expr sq, ",", expr dist_sq_mul_dist_add_dist_sq_mul_dist b, ",", expr hapc, "]"] [] []
end

end EuclideanGeometry

