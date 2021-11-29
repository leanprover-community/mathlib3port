import Mathbin.Geometry.Euclidean.Circumcenter

/-!
# Monge point and orthocenter

This file defines the orthocenter of a triangle, via its n-dimensional
generalization, the Monge point of a simplex.

## Main definitions

* `monge_point` is the Monge point of a simplex, defined in terms of
  its position on the Euler line and then shown to be the point of
  concurrence of the Monge planes.

* `monge_plane` is a Monge plane of an (n+2)-simplex, which is the
  (n+1)-dimensional affine subspace of the subspace spanned by the
  simplex that passes through the centroid of an n-dimensional face
  and is orthogonal to the opposite edge (in 2 dimensions, this is the
  same as an altitude).

* `altitude` is the line that passes through a vertex of a simplex and
  is orthogonal to the opposite face.

* `orthocenter` is defined, for the case of a triangle, to be the same
  as its Monge point, then shown to be the point of concurrence of the
  altitudes.

* `orthocentric_system` is a predicate on sets of points that says
  whether they are four points, one of which is the orthocenter of the
  other three (in which case various other properties hold, including
  that each is the orthocenter of the other three).

## References

* <https://en.wikipedia.org/wiki/Altitude_(triangle)>
* <https://en.wikipedia.org/wiki/Monge_point>
* <https://en.wikipedia.org/wiki/Orthocentric_system>
* Małgorzata Buba-Brzozowa, [The Monge Point and the 3(n+1) Point
  Sphere of an
  n-Simplex](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf)

-/


noncomputable theory

open_locale BigOperators

open_locale Classical

open_locale Real

open_locale RealInnerProductSpace

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry PointsWithCircumcenterIndex

variable {V : Type _} {P : Type _} [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

include V

/-- The Monge point of a simplex (in 2 or more dimensions) is a
generalization of the orthocenter of a triangle.  It is defined to be
the intersection of the Monge planes, where a Monge plane is the
(n-1)-dimensional affine subspace of the subspace spanned by the
simplex that passes through the centroid of an (n-2)-dimensional face
and is orthogonal to the opposite edge (in 2 dimensions, this is the
same as an altitude).  The circumcenter O, centroid G and Monge point
M are collinear in that order on the Euler line, with OG : GM = (n-1)
: 2.  Here, we use that ratio to define the Monge point (so resulting
in a point that equals the centroid in 0 or 1 dimensions), and then
show in subsequent lemmas that the point so defined lies in the Monge
planes and is their unique point of intersection. -/
def monge_point {n : ℕ} (s : simplex ℝ P n) : P :=
  (((n+1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ)) • ((univ : Finset (Finₓ (n+1))).centroid ℝ s.points -ᵥ s.circumcenter) +ᵥ
    s.circumcenter

/-- The position of the Monge point in relation to the circumcenter
and centroid. -/
theorem monge_point_eq_smul_vsub_vadd_circumcenter {n : ℕ} (s : simplex ℝ P n) :
  s.monge_point =
    (((n+1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ)) • ((univ : Finset (Finₓ (n+1))).centroid ℝ s.points -ᵥ s.circumcenter) +ᵥ
      s.circumcenter :=
  rfl

/-- The Monge point lies in the affine span. -/
theorem monge_point_mem_affine_span {n : ℕ} (s : simplex ℝ P n) : s.monge_point ∈ affineSpan ℝ (Set.Range s.points) :=
  smul_vsub_vadd_mem _ _ (centroid_mem_affine_span_of_card_eq_add_one ℝ _ (card_fin (n+1)))
    s.circumcenter_mem_affine_span s.circumcenter_mem_affine_span

/-- Two simplices with the same points have the same Monge point. -/
theorem monge_point_eq_of_range_eq {n : ℕ} {s₁ s₂ : simplex ℝ P n} (h : Set.Range s₁.points = Set.Range s₂.points) :
  s₁.monge_point = s₂.monge_point :=
  by 
    simpRw [monge_point_eq_smul_vsub_vadd_circumcenter, centroid_eq_of_range_eq h, circumcenter_eq_of_range_eq h]

omit V

/-- The weights for the Monge point of an (n+2)-simplex, in terms of
`points_with_circumcenter`. -/
def monge_point_weights_with_circumcenter (n : ℕ) : points_with_circumcenter_index (n+2) → ℝ
| point_index i => ((n+1 : ℕ) : ℝ)⁻¹
| circumcenter_index => -2 / ((n+1 : ℕ) : ℝ)

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `monge_point_weights_with_circumcenter` sums to 1. -/
@[simp]
theorem sum_monge_point_weights_with_circumcenter
(n : exprℕ()) : «expr = »(«expr∑ , »((i), monge_point_weights_with_circumcenter n i), 1) :=
begin
  simp_rw ["[", expr sum_points_with_circumcenter, ",", expr monge_point_weights_with_circumcenter, ",", expr sum_const, ",", expr card_fin, ",", expr nsmul_eq_mul, "]"] [],
  have [ident hn1] [":", expr «expr ≠ »((«expr + »(n, 1) : exprℝ()), 0)] [],
  { exact_mod_cast [expr nat.succ_ne_zero _] },
  field_simp [] ["[", expr hn1, "]"] [] [],
  ring []
end

include V

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Monge point of an (n+2)-simplex, in terms of
`points_with_circumcenter`. -/
theorem monge_point_eq_affine_combination_of_points_with_circumcenter
{n : exprℕ()}
(s : simplex exprℝ() P «expr + »(n, 2)) : «expr = »(s.monge_point, (univ : finset (points_with_circumcenter_index «expr + »(n, 2))).affine_combination s.points_with_circumcenter (monge_point_weights_with_circumcenter n)) :=
begin
  rw ["[", expr monge_point_eq_smul_vsub_vadd_circumcenter, ",", expr centroid_eq_affine_combination_of_points_with_circumcenter, ",", expr circumcenter_eq_affine_combination_of_points_with_circumcenter, ",", expr affine_combination_vsub, ",", "<-", expr linear_map.map_smul, ",", expr weighted_vsub_vadd_affine_combination, "]"] [],
  congr' [] ["with", ident i],
  rw ["[", expr pi.add_apply, ",", expr pi.smul_apply, ",", expr smul_eq_mul, ",", expr pi.sub_apply, "]"] [],
  have [ident hn1] [":", expr «expr ≠ »((«expr + »(n, 1) : exprℝ()), 0)] [],
  { exact_mod_cast [expr nat.succ_ne_zero _] },
  cases [expr i] []; simp_rw ["[", expr centroid_weights_with_circumcenter, ",", expr circumcenter_weights_with_circumcenter, ",", expr monge_point_weights_with_circumcenter, "]"] []; rw ["[", expr add_tsub_assoc_of_le (exprdec_trivial() : «expr ≤ »(1, 2)), ",", expr (exprdec_trivial() : «expr = »(«expr - »(2, 1), 1)), "]"] [],
  { rw ["[", expr if_pos (mem_univ _), ",", expr sub_zero, ",", expr add_zero, ",", expr card_fin, "]"] [],
    have [ident hn3] [":", expr «expr ≠ »((«expr + »(«expr + »(n, 2), 1) : exprℝ()), 0)] [],
    { exact_mod_cast [expr nat.succ_ne_zero _] },
    field_simp [] ["[", expr hn1, ",", expr hn3, ",", expr mul_comm, "]"] [] [] },
  { field_simp [] ["[", expr hn1, "]"] [] [],
    ring [] }
end

omit V

/-- The weights for the Monge point of an (n+2)-simplex, minus the
centroid of an n-dimensional face, in terms of
`points_with_circumcenter`.  This definition is only valid when `i₁ ≠ i₂`. -/
def monge_point_vsub_face_centroid_weights_with_circumcenter {n : ℕ} (i₁ i₂ : Finₓ (n+3)) :
  points_with_circumcenter_index (n+2) → ℝ
| point_index i => if i = i₁ ∨ i = i₂ then ((n+1 : ℕ) : ℝ)⁻¹ else 0
| circumcenter_index => -2 / ((n+1 : ℕ) : ℝ)

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `monge_point_vsub_face_centroid_weights_with_circumcenter` is the
result of subtracting `centroid_weights_with_circumcenter` from
`monge_point_weights_with_circumcenter`. -/
theorem monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub
{n : exprℕ()}
{i₁ i₂ : fin «expr + »(n, 3)}
(h : «expr ≠ »(i₁, i₂)) : «expr = »(monge_point_vsub_face_centroid_weights_with_circumcenter i₁ i₂, «expr - »(monge_point_weights_with_circumcenter n, centroid_weights_with_circumcenter «expr ᶜ»({i₁, i₂}))) :=
begin
  ext [] [ident i] [],
  cases [expr i] [],
  { rw ["[", expr pi.sub_apply, ",", expr monge_point_weights_with_circumcenter, ",", expr centroid_weights_with_circumcenter, ",", expr monge_point_vsub_face_centroid_weights_with_circumcenter, "]"] [],
    have [ident hu] [":", expr «expr = »(card («expr ᶜ»({i₁, i₂}) : finset (fin «expr + »(n, 3))), «expr + »(n, 1))] [],
    { simp [] [] [] ["[", expr card_compl, ",", expr fintype.card_fin, ",", expr h, "]"] [] [] },
    rw [expr hu] [],
    by_cases [expr hi, ":", expr «expr ∨ »(«expr = »(i, i₁), «expr = »(i, i₂))]; simp [] [] [] ["[", expr compl_eq_univ_sdiff, ",", expr hi, "]"] [] [] },
  { simp [] [] [] ["[", expr monge_point_weights_with_circumcenter, ",", expr centroid_weights_with_circumcenter, ",", expr monge_point_vsub_face_centroid_weights_with_circumcenter, "]"] [] [] }
end

/-- `monge_point_vsub_face_centroid_weights_with_circumcenter` sums to 0. -/
@[simp]
theorem sum_monge_point_vsub_face_centroid_weights_with_circumcenter {n : ℕ} {i₁ i₂ : Finₓ (n+3)} (h : i₁ ≠ i₂) :
  (∑i, monge_point_vsub_face_centroid_weights_with_circumcenter i₁ i₂ i) = 0 :=
  by 
    rw [monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub h]
    simpRw [Pi.sub_apply, sum_sub_distrib, sum_monge_point_weights_with_circumcenter]
    rw [sum_centroid_weights_with_circumcenter, sub_self]
    simp [←card_pos, card_compl, h]

include V

/-- The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, in terms of `points_with_circumcenter`. -/
theorem monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter {n : ℕ} (s : simplex ℝ P (n+2))
  {i₁ i₂ : Finₓ (n+3)} (h : i₁ ≠ i₂) :
  s.monge_point -ᵥ («expr ᶜ» {i₁, i₂} : Finset (Finₓ (n+3))).centroid ℝ s.points =
    (univ : Finset (points_with_circumcenter_index (n+2))).weightedVsub s.points_with_circumcenter
      (monge_point_vsub_face_centroid_weights_with_circumcenter i₁ i₂) :=
  by 
    simpRw [monge_point_eq_affine_combination_of_points_with_circumcenter,
      centroid_eq_affine_combination_of_points_with_circumcenter, affine_combination_vsub,
      monge_point_vsub_face_centroid_weights_with_circumcenter_eq_sub h]

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Monge point of an (n+2)-simplex, minus the centroid of an
n-dimensional face, is orthogonal to the difference of the two
vertices not in that face. -/
theorem inner_monge_point_vsub_face_centroid_vsub
{n : exprℕ()}
(s : simplex exprℝ() P «expr + »(n, 2))
{i₁ i₂ : fin «expr + »(n, 3)}
(h : «expr ≠ »(i₁, i₂)) : «expr = »(«expr⟪ , ⟫»(«expr -ᵥ »(s.monge_point, («expr ᶜ»({i₁, i₂}) : finset (fin «expr + »(n, 3))).centroid exprℝ() s.points), «expr -ᵥ »(s.points i₁, s.points i₂)), 0) :=
begin
  simp_rw ["[", expr monge_point_vsub_face_centroid_eq_weighted_vsub_of_points_with_circumcenter s h, ",", expr point_eq_affine_combination_of_points_with_circumcenter, ",", expr affine_combination_vsub, "]"] [],
  have [ident hs] [":", expr «expr = »(«expr∑ , »((i), «expr - »(point_weights_with_circumcenter i₁, point_weights_with_circumcenter i₂) i), 0)] [],
  { simp [] [] [] [] [] [] },
  rw ["[", expr inner_weighted_vsub _ (sum_monge_point_vsub_face_centroid_weights_with_circumcenter h) _ hs, ",", expr sum_points_with_circumcenter, ",", expr points_with_circumcenter_eq_circumcenter, "]"] [],
  simp [] [] ["only"] ["[", expr monge_point_vsub_face_centroid_weights_with_circumcenter, ",", expr points_with_circumcenter_point, "]"] [] [],
  let [ident fs] [":", expr finset (fin «expr + »(n, 3))] [":=", expr {i₁, i₂}],
  have [ident hfs] [":", expr ∀
   i : fin «expr + »(n, 3), «expr ∉ »(i, fs) → «expr ∧ »(«expr ≠ »(i, i₁), «expr ≠ »(i, i₂))] [],
  { intros [ident i, ident hi],
    split; { intro [ident hj],
      simpa [] [] [] ["[", "<-", expr hj, "]"] [] ["using", expr hi] } },
  rw ["<-", expr sum_subset fs.subset_univ _] [],
  { simp_rw ["[", expr sum_points_with_circumcenter, ",", expr points_with_circumcenter_eq_circumcenter, ",", expr points_with_circumcenter_point, ",", expr pi.sub_apply, ",", expr point_weights_with_circumcenter, "]"] [],
    rw ["[", "<-", expr sum_subset fs.subset_univ _, "]"] [],
    { simp_rw ["[", expr sum_insert (not_mem_singleton.2 h), ",", expr sum_singleton, "]"] [],
      repeat { rw ["<-", expr sum_subset fs.subset_univ _] [] },
      { simp_rw ["[", expr sum_insert (not_mem_singleton.2 h), ",", expr sum_singleton, "]"] [],
        simp [] [] [] ["[", expr h, ",", expr h.symm, ",", expr dist_comm (s.points i₁), "]"] [] [] },
      all_goals { intros [ident i, ident hu, ident hi],
        simp [] [] [] ["[", expr hfs i hi, "]"] [] [] } },
    { intros [ident i, ident hu, ident hi],
      simp [] [] [] ["[", expr hfs i hi, ",", expr point_weights_with_circumcenter, "]"] [] [] } },
  { intros [ident i, ident hu, ident hi],
    simp [] [] [] ["[", expr hfs i hi, "]"] [] [] }
end

/-- A Monge plane of an (n+2)-simplex is the (n+1)-dimensional affine
subspace of the subspace spanned by the simplex that passes through
the centroid of an n-dimensional face and is orthogonal to the
opposite edge (in 2 dimensions, this is the same as an altitude).
This definition is only intended to be used when `i₁ ≠ i₂`. -/
def monge_plane {n : ℕ} (s : simplex ℝ P (n+2)) (i₁ i₂ : Finₓ (n+3)) : AffineSubspace ℝ P :=
  mk' ((«expr ᶜ» {i₁, i₂} : Finset (Finₓ (n+3))).centroid ℝ s.points)
      (ℝ∙s.points i₁ -ᵥ s.points i₂)ᗮ⊓affineSpan ℝ (Set.Range s.points)

/-- The definition of a Monge plane. -/
theorem monge_plane_def {n : ℕ} (s : simplex ℝ P (n+2)) (i₁ i₂ : Finₓ (n+3)) :
  s.monge_plane i₁ i₂ =
    mk' ((«expr ᶜ» {i₁, i₂} : Finset (Finₓ (n+3))).centroid ℝ s.points)
        (ℝ∙s.points i₁ -ᵥ s.points i₂)ᗮ⊓affineSpan ℝ (Set.Range s.points) :=
  rfl

/-- The Monge plane associated with vertices `i₁` and `i₂` equals that
associated with `i₂` and `i₁`. -/
theorem monge_plane_comm {n : ℕ} (s : simplex ℝ P (n+2)) (i₁ i₂ : Finₓ (n+3)) :
  s.monge_plane i₁ i₂ = s.monge_plane i₂ i₁ :=
  by 
    simpRw [monge_plane_def]
    congr 3
    ·
      congr 1 
      exact insert_singleton_comm _ _
    ·
      ext 
      simpRw [Submodule.mem_span_singleton]
      split 
      all_goals 
        rintro ⟨r, rfl⟩
        use -r 
        rw [neg_smul, ←smul_neg, neg_vsub_eq_vsub_rev]

/-- The Monge point lies in the Monge planes. -/
theorem monge_point_mem_monge_plane {n : ℕ} (s : simplex ℝ P (n+2)) {i₁ i₂ : Finₓ (n+3)} (h : i₁ ≠ i₂) :
  s.monge_point ∈ s.monge_plane i₁ i₂ :=
  by 
    rw [monge_plane_def, mem_inf_iff, ←vsub_right_mem_direction_iff_mem (self_mem_mk' _ _), direction_mk',
      Submodule.mem_orthogonal']
    refine' ⟨_, s.monge_point_mem_affine_span⟩
    intro v hv 
    rcases submodule.mem_span_singleton.mp hv with ⟨r, rfl⟩
    rw [inner_smul_right, s.inner_monge_point_vsub_face_centroid_vsub h, mul_zero]

/-- The direction of a Monge plane. -/
theorem direction_monge_plane {n : ℕ} (s : simplex ℝ P (n+2)) {i₁ i₂ : Finₓ (n+3)} (h : i₁ ≠ i₂) :
  (s.monge_plane i₁ i₂).direction = (ℝ∙s.points i₁ -ᵥ s.points i₂)ᗮ⊓vectorSpan ℝ (Set.Range s.points) :=
  by 
    rw [monge_plane_def, direction_inf_of_mem_inf (s.monge_point_mem_monge_plane h), direction_mk',
      direction_affine_span]

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The Monge point is the only point in all the Monge planes from any
one vertex. -/
theorem eq_monge_point_of_forall_mem_monge_plane
{n : exprℕ()}
{s : simplex exprℝ() P «expr + »(n, 2)}
{i₁ : fin «expr + »(n, 3)}
{p : P}
(h : ∀ i₂, «expr ≠ »(i₁, i₂) → «expr ∈ »(p, s.monge_plane i₁ i₂)) : «expr = »(p, s.monge_point) :=
begin
  rw ["<-", expr @vsub_eq_zero_iff_eq V] [],
  have [ident h'] [":", expr ∀
   i₂, «expr ≠ »(i₁, i₂) → «expr ∈ »(«expr -ᵥ »(p, s.monge_point), «expr ⊓ »(«expr ᗮ»(«expr ∙ »(exprℝ(), «expr -ᵥ »(s.points i₁, s.points i₂))), vector_span exprℝ() (set.range s.points)))] [],
  { intros [ident i₂, ident hne],
    rw ["[", "<-", expr s.direction_monge_plane hne, ",", expr vsub_right_mem_direction_iff_mem (s.monge_point_mem_monge_plane hne), "]"] [],
    exact [expr h i₂ hne] },
  have [ident hi] [":", expr «expr ∈ »(«expr -ᵥ »(p, s.monge_point), «expr⨅ , »((i₂ : {i // «expr ≠ »(i₁, i)}), «expr ᗮ»(«expr ∙ »(exprℝ(), «expr -ᵥ »(s.points i₁, s.points i₂)))))] [],
  { rw [expr submodule.mem_infi] [],
    exact [expr λ i, (submodule.mem_inf.1 (h' i i.property)).1] },
  rw ["[", expr submodule.infi_orthogonal, ",", "<-", expr submodule.span_Union, "]"] ["at", ident hi],
  have [ident hu] [":", expr «expr = »(«expr⋃ , »((i : {i // «expr ≠ »(i₁, i)}), ({«expr -ᵥ »(s.points i₁, s.points i)} : set V)), «expr '' »(((«expr -ᵥ »)) (s.points i₁), «expr '' »(s.points, «expr \ »(set.univ, {i₁}))))] [],
  { rw ["[", expr set.image_image, "]"] [],
    ext [] [ident x] [],
    simp_rw ["[", expr set.mem_Union, ",", expr set.mem_image, ",", expr set.mem_singleton_iff, ",", expr set.mem_diff_singleton, "]"] [],
    split,
    { rintros ["⟨", ident i, ",", ident rfl, "⟩"],
      use ["[", expr i, ",", expr ⟨set.mem_univ _, i.property.symm⟩, "]"] },
    { rintros ["⟨", ident i, ",", "⟨", ident hiu, ",", ident hi, "⟩", ",", ident rfl, "⟩"],
      use ["[", expr ⟨i, hi.symm⟩, ",", expr rfl, "]"] } },
  rw ["[", expr hu, ",", "<-", expr vector_span_image_eq_span_vsub_set_left_ne exprℝ() _ (set.mem_univ _), ",", expr set.image_univ, "]"] ["at", ident hi],
  have [ident hv] [":", expr «expr ∈ »(«expr -ᵥ »(p, s.monge_point), vector_span exprℝ() (set.range s.points))] [],
  { let [ident s₁] [":", expr finset (fin «expr + »(n, 3))] [":=", expr univ.erase i₁],
    obtain ["⟨", ident i₂, ",", ident h₂, "⟩", ":=", expr card_pos.1 (show «expr < »(0, card s₁), by simp [] [] [] ["[", expr card_erase_of_mem, "]"] [] [])],
    have [ident h₁₂] [":", expr «expr ≠ »(i₁, i₂)] [":=", expr (ne_of_mem_erase h₂).symm],
    exact [expr (submodule.mem_inf.1 (h' i₂ h₁₂)).2] },
  exact [expr submodule.disjoint_def.1 (vector_span exprℝ() (set.range s.points)).orthogonal_disjoint _ hv hi]
end

/-- An altitude of a simplex is the line that passes through a vertex
and is orthogonal to the opposite face. -/
def altitude {n : ℕ} (s : simplex ℝ P (n+1)) (i : Finₓ (n+2)) : AffineSubspace ℝ P :=
  mk' (s.points i) (affineSpan ℝ (s.points '' «expr↑ » (univ.erase i))).directionᗮ⊓affineSpan ℝ (Set.Range s.points)

/-- The definition of an altitude. -/
theorem altitude_def {n : ℕ} (s : simplex ℝ P (n+1)) (i : Finₓ (n+2)) :
  s.altitude i =
    mk' (s.points i)
        (affineSpan ℝ (s.points '' «expr↑ » (univ.erase i))).directionᗮ⊓affineSpan ℝ (Set.Range s.points) :=
  rfl

/-- A vertex lies in the corresponding altitude. -/
theorem mem_altitude {n : ℕ} (s : simplex ℝ P (n+1)) (i : Finₓ (n+2)) : s.points i ∈ s.altitude i :=
  (mem_inf_iff _ _ _).2 ⟨self_mem_mk' _ _, mem_affine_span ℝ (Set.mem_range_self _)⟩

/-- The direction of an altitude. -/
theorem direction_altitude {n : ℕ} (s : simplex ℝ P (n+1)) (i : Finₓ (n+2)) :
  (s.altitude i).direction =
    (vectorSpan ℝ (s.points '' «expr↑ » (Finset.univ.erase i)))ᗮ⊓vectorSpan ℝ (Set.Range s.points) :=
  by 
    rw [altitude_def, direction_inf_of_mem (self_mem_mk' (s.points i) _) (mem_affine_span ℝ (Set.mem_range_self _)),
      direction_mk', direction_affine_span, direction_affine_span]

/-- The vector span of the opposite face lies in the direction
orthogonal to an altitude. -/
theorem vector_span_le_altitude_direction_orthogonal {n : ℕ} (s : simplex ℝ P (n+1)) (i : Finₓ (n+2)) :
  vectorSpan ℝ (s.points '' «expr↑ » (Finset.univ.erase i)) ≤ (s.altitude i).directionᗮ :=
  by 
    rw [direction_altitude]
    exact
      le_transₓ (vectorSpan ℝ (s.points '' «expr↑ » (finset.univ.erase i))).le_orthogonal_orthogonal
        (Submodule.orthogonal_le inf_le_left)

open FiniteDimensional

/-- An altitude is finite-dimensional. -/
instance finite_dimensional_direction_altitude {n : ℕ} (s : simplex ℝ P (n+1)) (i : Finₓ (n+2)) :
  FiniteDimensional ℝ (s.altitude i).direction :=
  by 
    rw [direction_altitude]
    infer_instance

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An altitude is one-dimensional (i.e., a line). -/
@[simp]
theorem finrank_direction_altitude
{n : exprℕ()}
(s : simplex exprℝ() P «expr + »(n, 1))
(i : fin «expr + »(n, 2)) : «expr = »(finrank exprℝ() (s.altitude i).direction, 1) :=
begin
  rw [expr direction_altitude] [],
  have [ident h] [] [":=", expr submodule.finrank_add_inf_finrank_orthogonal (vector_span_mono exprℝ() (set.image_subset_range s.points «expr↑ »(univ.erase i)))],
  have [ident hc] [":", expr «expr = »(card (univ.erase i), «expr + »(n, 1))] [],
  { rw [expr card_erase_of_mem (mem_univ _)] [],
    simp [] [] [] [] [] [] },
  refine [expr add_left_cancel (trans h _)],
  rw ["[", expr s.independent.finrank_vector_span (fintype.card_fin _), ",", "<-", expr finset.coe_image, ",", expr s.independent.finrank_vector_span_image_finset hc, "]"] []
end

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A line through a vertex is the altitude through that vertex if and
only if it is orthogonal to the opposite face. -/
theorem affine_span_insert_singleton_eq_altitude_iff
{n : exprℕ()}
(s : simplex exprℝ() P «expr + »(n, 1))
(i : fin «expr + »(n, 2))
(p : P) : «expr ↔ »(«expr = »(affine_span exprℝ() {p, s.points i}, s.altitude i), «expr ∧ »(«expr ≠ »(p, s.points i), «expr ∧ »(«expr ∈ »(p, affine_span exprℝ() (set.range s.points)), «expr ∈ »(«expr -ᵥ »(p, s.points i), «expr ᗮ»((affine_span exprℝ() «expr '' »(s.points, «expr↑ »(finset.univ.erase i))).direction))))) :=
begin
  rw ["[", expr eq_iff_direction_eq_of_mem (mem_affine_span exprℝ() (set.mem_insert_of_mem _ (set.mem_singleton _))) (s.mem_altitude _), ",", "<-", expr vsub_right_mem_direction_iff_mem (mem_affine_span exprℝ() (set.mem_range_self i)) p, ",", expr direction_affine_span, ",", expr direction_affine_span, ",", expr direction_affine_span, "]"] [],
  split,
  { intro [ident h],
    split,
    { intro [ident heq],
      rw ["[", expr heq, ",", expr set.pair_eq_singleton, ",", expr vector_span_singleton, "]"] ["at", ident h],
      have [ident hd] [":", expr «expr = »(finrank exprℝ() (s.altitude i).direction, 0)] [],
      { rw ["[", "<-", expr h, ",", expr finrank_bot, "]"] [] },
      simpa [] [] [] [] [] ["using", expr hd] },
    { rw ["[", "<-", expr submodule.mem_inf, ",", expr inf_comm, ",", "<-", expr direction_altitude, ",", "<-", expr h, "]"] [],
      exact [expr vsub_mem_vector_span exprℝ() (set.mem_insert _ _) (set.mem_insert_of_mem _ (set.mem_singleton _))] } },
  { rintro ["⟨", ident hne, ",", ident h, "⟩"],
    rw ["[", "<-", expr submodule.mem_inf, ",", expr inf_comm, ",", "<-", expr direction_altitude, "]"] ["at", ident h],
    rw ["[", expr vector_span_eq_span_vsub_set_left_ne exprℝ() (set.mem_insert _ _), ",", expr set.insert_diff_of_mem _ (set.mem_singleton _), ",", expr set.diff_singleton_eq_self (λ
      h, hne (set.mem_singleton_iff.1 h)), ",", expr set.image_singleton, "]"] [],
    refine [expr eq_of_le_of_finrank_eq _ _],
    { rw [expr submodule.span_le] [],
      simpa [] [] [] [] [] ["using", expr h] },
    { rw ["[", expr finrank_direction_altitude, ",", expr finrank_span_set_eq_card, "]"] [],
      { simp [] [] [] [] [] [] },
      { refine [expr linear_independent_singleton _],
        simpa [] [] [] [] [] ["using", expr hne] } } }
end

end Simplex

namespace Triangle

open EuclideanGeometry Finset Simplex AffineSubspace FiniteDimensional

variable {V : Type _} {P : Type _} [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

include V

/-- The orthocenter of a triangle is the intersection of its
altitudes.  It is defined here as the 2-dimensional case of the
Monge point. -/
def orthocenter (t : triangle ℝ P) : P :=
  t.monge_point

/-- The orthocenter equals the Monge point. -/
theorem orthocenter_eq_monge_point (t : triangle ℝ P) : t.orthocenter = t.monge_point :=
  rfl

/-- The position of the orthocenter in relation to the circumcenter
and centroid. -/
theorem orthocenter_eq_smul_vsub_vadd_circumcenter (t : triangle ℝ P) :
  t.orthocenter = (3 : ℝ) • ((univ : Finset (Finₓ 3)).centroid ℝ t.points -ᵥ t.circumcenter : V) +ᵥ t.circumcenter :=
  by 
    rw [orthocenter_eq_monge_point, monge_point_eq_smul_vsub_vadd_circumcenter]
    normNum

/-- The orthocenter lies in the affine span. -/
theorem orthocenter_mem_affine_span (t : triangle ℝ P) : t.orthocenter ∈ affineSpan ℝ (Set.Range t.points) :=
  t.monge_point_mem_affine_span

/-- Two triangles with the same points have the same orthocenter. -/
theorem orthocenter_eq_of_range_eq {t₁ t₂ : triangle ℝ P} (h : Set.Range t₁.points = Set.Range t₂.points) :
  t₁.orthocenter = t₂.orthocenter :=
  monge_point_eq_of_range_eq h

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In the case of a triangle, altitudes are the same thing as Monge
planes. -/
theorem altitude_eq_monge_plane
(t : triangle exprℝ() P)
{i₁ i₂ i₃ : fin 3}
(h₁₂ : «expr ≠ »(i₁, i₂))
(h₁₃ : «expr ≠ »(i₁, i₃))
(h₂₃ : «expr ≠ »(i₂, i₃)) : «expr = »(t.altitude i₁, t.monge_plane i₂ i₃) :=
begin
  have [ident hs] [":", expr «expr = »((«expr ᶜ»({i₂, i₃}) : finset (fin 3)), {i₁})] [],
  by dec_trivial ["!"],
  have [ident he] [":", expr «expr = »(univ.erase i₁, {i₂, i₃})] [],
  by dec_trivial ["!"],
  rw ["[", expr monge_plane_def, ",", expr altitude_def, ",", expr direction_affine_span, ",", expr hs, ",", expr he, ",", expr centroid_singleton, ",", expr coe_insert, ",", expr coe_singleton, ",", expr vector_span_image_eq_span_vsub_set_left_ne exprℝ() _ (set.mem_insert i₂ _), "]"] [],
  simp [] [] [] ["[", expr h₂₃, ",", expr submodule.span_insert_eq_span, "]"] [] []
end

/-- The orthocenter lies in the altitudes. -/
theorem orthocenter_mem_altitude (t : triangle ℝ P) {i₁ : Finₓ 3} : t.orthocenter ∈ t.altitude i₁ :=
  by 
    obtain ⟨i₂, i₃, h₁₂, h₂₃, h₁₃⟩ : ∃ i₂ i₃, i₁ ≠ i₂ ∧ i₂ ≠ i₃ ∧ i₁ ≠ i₃
    ·
      decide! 
    rw [orthocenter_eq_monge_point, t.altitude_eq_monge_plane h₁₂ h₁₃ h₂₃]
    exact t.monge_point_mem_monge_plane h₂₃

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The orthocenter is the only point lying in any two of the
altitudes. -/
theorem eq_orthocenter_of_forall_mem_altitude
{t : triangle exprℝ() P}
{i₁ i₂ : fin 3}
{p : P}
(h₁₂ : «expr ≠ »(i₁, i₂))
(h₁ : «expr ∈ »(p, t.altitude i₁))
(h₂ : «expr ∈ »(p, t.altitude i₂)) : «expr = »(p, t.orthocenter) :=
begin
  obtain ["⟨", ident i₃, ",", ident h₂₃, ",", ident h₁₃, "⟩", ":", expr «expr∃ , »((i₃), «expr ∧ »(«expr ≠ »(i₂, i₃), «expr ≠ »(i₁, i₃)))],
  { clear [ident h₁, ident h₂],
    dec_trivial ["!"] },
  rw [expr t.altitude_eq_monge_plane h₁₃ h₁₂ h₂₃.symm] ["at", ident h₁],
  rw [expr t.altitude_eq_monge_plane h₂₃ h₁₂.symm h₁₃.symm] ["at", ident h₂],
  rw [expr orthocenter_eq_monge_point] [],
  have [ident ha] [":", expr ∀ i, «expr ≠ »(i₃, i) → «expr ∈ »(p, t.monge_plane i₃ i)] [],
  { intros [ident i, ident hi],
    have [ident hi₁₂] [":", expr «expr ∨ »(«expr = »(i₁, i), «expr = »(i₂, i))] [],
    { clear [ident h₁, ident h₂],
      dec_trivial ["!"] },
    cases [expr hi₁₂] [],
    { exact [expr «expr ▸ »(hi₁₂, h₂)] },
    { exact [expr «expr ▸ »(hi₁₂, h₁)] } },
  exact [expr eq_monge_point_of_forall_mem_monge_plane ha]
end

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius. -/
theorem dist_orthocenter_reflection_circumcenter
(t : triangle exprℝ() P)
{i₁ i₂ : fin 3}
(h : «expr ≠ »(i₁, i₂)) : «expr = »(dist t.orthocenter (reflection (affine_span exprℝ() «expr '' »(t.points, {i₁, i₂})) t.circumcenter), t.circumradius) :=
begin
  rw ["[", "<-", expr mul_self_inj_of_nonneg dist_nonneg t.circumradius_nonneg, ",", expr t.reflection_circumcenter_eq_affine_combination_of_points_with_circumcenter h, ",", expr t.orthocenter_eq_monge_point, ",", expr monge_point_eq_affine_combination_of_points_with_circumcenter, ",", expr dist_affine_combination t.points_with_circumcenter (sum_monge_point_weights_with_circumcenter _) (sum_reflection_circumcenter_weights_with_circumcenter h), "]"] [],
  simp_rw ["[", expr sum_points_with_circumcenter, ",", expr pi.sub_apply, ",", expr monge_point_weights_with_circumcenter, ",", expr reflection_circumcenter_weights_with_circumcenter, "]"] [],
  have [ident hu] [":", expr «expr ⊆ »(({i₁, i₂} : finset (fin 3)), univ)] [":=", expr subset_univ _],
  obtain ["⟨", ident i₃, ",", ident hi₃, ",", ident hi₃₁, ",", ident hi₃₂, "⟩", ":", expr «expr∃ , »((i₃), «expr ∧ »(«expr = »(«expr \ »(univ, ({i₁, i₂} : finset (fin 3))), {i₃}), «expr ∧ »(«expr ≠ »(i₃, i₁), «expr ≠ »(i₃, i₂))))],
  by dec_trivial ["!"],
  simp_rw ["[", "<-", expr sum_sdiff hu, ",", expr hi₃, "]"] [],
  simp [] [] [] ["[", expr hi₃₁, ",", expr hi₃₂, "]"] [] [],
  norm_num [] []
end

/-- The distance from the orthocenter to the reflection of the
circumcenter in a side equals the circumradius, variant using a
`finset`. -/
theorem dist_orthocenter_reflection_circumcenter_finset (t : triangle ℝ P) {i₁ i₂ : Finₓ 3} (h : i₁ ≠ i₂) :
  dist t.orthocenter (reflection (affineSpan ℝ (t.points '' «expr↑ » ({i₁, i₂} : Finset (Finₓ 3)))) t.circumcenter) =
    t.circumradius :=
  by 
    convert dist_orthocenter_reflection_circumcenter _ h 
    simp 

/-- The affine span of the orthocenter and a vertex is contained in
the altitude. -/
theorem affine_span_orthocenter_point_le_altitude (t : triangle ℝ P) (i : Finₓ 3) :
  affineSpan ℝ {t.orthocenter, t.points i} ≤ t.altitude i :=
  by 
    refine' span_points_subset_coe_of_subset_coe _ 
    rw [Set.insert_subset, Set.singleton_subset_iff]
    exact ⟨t.orthocenter_mem_altitude, t.mem_altitude i⟩

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then an altitude of `t₂` from
a vertex that was not replaced is the corresponding side of `t₁`. -/
theorem altitude_replace_orthocenter_eq_affine_span
{t₁ t₂ : triangle exprℝ() P}
{i₁ i₂ i₃ j₁ j₂ j₃ : fin 3}
(hi₁₂ : «expr ≠ »(i₁, i₂))
(hi₁₃ : «expr ≠ »(i₁, i₃))
(hi₂₃ : «expr ≠ »(i₂, i₃))
(hj₁₂ : «expr ≠ »(j₁, j₂))
(hj₁₃ : «expr ≠ »(j₁, j₃))
(hj₂₃ : «expr ≠ »(j₂, j₃))
(h₁ : «expr = »(t₂.points j₁, t₁.orthocenter))
(h₂ : «expr = »(t₂.points j₂, t₁.points i₂))
(h₃ : «expr = »(t₂.points j₃, t₁.points i₃)) : «expr = »(t₂.altitude j₂, affine_span exprℝ() {t₁.points i₁, t₁.points i₂}) :=
begin
  symmetry,
  rw ["[", "<-", expr h₂, ",", expr t₂.affine_span_insert_singleton_eq_altitude_iff, "]"] [],
  rw ["[", expr h₂, "]"] [],
  use [expr t₁.independent.injective.ne hi₁₂],
  have [ident he] [":", expr «expr = »(affine_span exprℝ() (set.range t₂.points), affine_span exprℝ() (set.range t₁.points))] [],
  { refine [expr ext_of_direction_eq _ ⟨t₁.points i₃, mem_affine_span exprℝ() ⟨j₃, h₃⟩, mem_affine_span exprℝ() (set.mem_range_self _)⟩],
    refine [expr eq_of_le_of_finrank_eq (direction_le (span_points_subset_coe_of_subset_coe _)) _],
    { have [ident hu] [":", expr «expr = »((finset.univ : finset (fin 3)), {j₁, j₂, j₃})] [],
      { clear [ident h₁, ident h₂, ident h₃],
        dec_trivial ["!"] },
      rw ["[", "<-", expr set.image_univ, ",", "<-", expr finset.coe_univ, ",", expr hu, ",", expr finset.coe_insert, ",", expr finset.coe_insert, ",", expr finset.coe_singleton, ",", expr set.image_insert_eq, ",", expr set.image_insert_eq, ",", expr set.image_singleton, ",", expr h₁, ",", expr h₂, ",", expr h₃, ",", expr set.insert_subset, ",", expr set.insert_subset, ",", expr set.singleton_subset_iff, "]"] [],
      exact [expr ⟨t₁.orthocenter_mem_affine_span, mem_affine_span exprℝ() (set.mem_range_self _), mem_affine_span exprℝ() (set.mem_range_self _)⟩] },
    { rw ["[", expr direction_affine_span, ",", expr direction_affine_span, ",", expr t₁.independent.finrank_vector_span (fintype.card_fin _), ",", expr t₂.independent.finrank_vector_span (fintype.card_fin _), "]"] [] } },
  rw [expr he] [],
  use [expr mem_affine_span exprℝ() (set.mem_range_self _)],
  have [ident hu] [":", expr «expr = »(finset.univ.erase j₂, {j₁, j₃})] [],
  { clear [ident h₁, ident h₂, ident h₃],
    dec_trivial ["!"] },
  rw ["[", expr hu, ",", expr finset.coe_insert, ",", expr finset.coe_singleton, ",", expr set.image_insert_eq, ",", expr set.image_singleton, ",", expr h₁, ",", expr h₃, "]"] [],
  have [ident hle] [":", expr «expr ≤ »(«expr ᗮ»((t₁.altitude i₃).direction), «expr ᗮ»((affine_span exprℝ() ({t₁.orthocenter, t₁.points i₃} : set P)).direction))] [":=", expr submodule.orthogonal_le (direction_le (affine_span_orthocenter_point_le_altitude _ _))],
  refine [expr hle (t₁.vector_span_le_altitude_direction_orthogonal i₃ _)],
  have [ident hui] [":", expr «expr = »(finset.univ.erase i₃, {i₁, i₂})] [],
  { clear [ident hle, ident h₂, ident h₃],
    dec_trivial ["!"] },
  rw ["[", expr hui, ",", expr finset.coe_insert, ",", expr finset.coe_singleton, ",", expr set.image_insert_eq, ",", expr set.image_singleton, "]"] [],
  refine [expr vsub_mem_vector_span exprℝ() (set.mem_insert _ _) (set.mem_insert_of_mem _ (set.mem_singleton _))]
end

/-- Suppose we are given a triangle `t₁`, and replace one of its
vertices by its orthocenter, yielding triangle `t₂` (with vertices not
necessarily listed in the same order).  Then the orthocenter of `t₂`
is the vertex of `t₁` that was replaced. -/
theorem orthocenter_replace_orthocenter_eq_point {t₁ t₂ : triangle ℝ P} {i₁ i₂ i₃ j₁ j₂ j₃ : Finₓ 3} (hi₁₂ : i₁ ≠ i₂)
  (hi₁₃ : i₁ ≠ i₃) (hi₂₃ : i₂ ≠ i₃) (hj₁₂ : j₁ ≠ j₂) (hj₁₃ : j₁ ≠ j₃) (hj₂₃ : j₂ ≠ j₃)
  (h₁ : t₂.points j₁ = t₁.orthocenter) (h₂ : t₂.points j₂ = t₁.points i₂) (h₃ : t₂.points j₃ = t₁.points i₃) :
  t₂.orthocenter = t₁.points i₁ :=
  by 
    refine' (triangle.eq_orthocenter_of_forall_mem_altitude hj₂₃ _ _).symm
    ·
      rw [altitude_replace_orthocenter_eq_affine_span hi₁₂ hi₁₃ hi₂₃ hj₁₂ hj₁₃ hj₂₃ h₁ h₂ h₃]
      exact mem_affine_span ℝ (Set.mem_insert _ _)
    ·
      rw [altitude_replace_orthocenter_eq_affine_span hi₁₃ hi₁₂ hi₂₃.symm hj₁₃ hj₁₂ hj₂₃.symm h₁ h₃ h₂]
      exact mem_affine_span ℝ (Set.mem_insert _ _)

end Triangle

end Affine

namespace EuclideanGeometry

open Affine AffineSubspace FiniteDimensional

variable {V : Type _} {P : Type _} [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

include V

/-- Four points form an orthocentric system if they consist of the
vertices of a triangle and its orthocenter. -/
def orthocentric_system (s : Set P) : Prop :=
  ∃ t : triangle ℝ P, t.orthocenter ∉ Set.Range t.points ∧ s = insert t.orthocenter (Set.Range t.points)

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This is an auxiliary lemma giving information about the relation
of two triangles in an orthocentric system; it abstracts some
reasoning, with no geometric content, that is common to some other
lemmas.  Suppose the orthocentric system is generated by triangle `t`,
and we are given three points `p` in the orthocentric system.  Then
either we can find indices `i₁`, `i₂` and `i₃` for `p` such that `p
i₁` is the orthocenter of `t` and `p i₂` and `p i₃` are points `j₂`
and `j₃` of `t`, or `p` has the same points as `t`. -/
theorem exists_of_range_subset_orthocentric_system
{t : triangle exprℝ() P}
(ho : «expr ∉ »(t.orthocenter, set.range t.points))
{p : fin 3 → P}
(hps : «expr ⊆ »(set.range p, insert t.orthocenter (set.range t.points)))
(hpi : function.injective p) : «expr ∨ »(«expr∃ , »((i₁
   i₂
   i₃
   j₂
   j₃ : fin 3), «expr ∧ »(«expr ≠ »(i₁, i₂), «expr ∧ »(«expr ≠ »(i₁, i₃), «expr ∧ »(«expr ≠ »(i₂, i₃), «expr ∧ »(∀
      i : fin 3, «expr ∨ »(«expr = »(i, i₁), «expr ∨ »(«expr = »(i, i₂), «expr = »(i, i₃))), «expr ∧ »(«expr = »(p i₁, t.orthocenter), «expr ∧ »(«expr ≠ »(j₂, j₃), «expr ∧ »(«expr = »(t.points j₂, p i₂), «expr = »(t.points j₃, p i₃))))))))), «expr = »(set.range p, set.range t.points)) :=
begin
  by_cases [expr h, ":", expr «expr ∈ »(t.orthocenter, set.range p)],
  { left,
    rcases [expr h, "with", "⟨", ident i₁, ",", ident h₁, "⟩"],
    obtain ["⟨", ident i₂, ",", ident i₃, ",", ident h₁₂, ",", ident h₁₃, ",", ident h₂₃, ",", ident h₁₂₃, "⟩", ":", expr «expr∃ , »((i₂
       i₃ : fin 3), «expr ∧ »(«expr ≠ »(i₁, i₂), «expr ∧ »(«expr ≠ »(i₁, i₃), «expr ∧ »(«expr ≠ »(i₂, i₃), ∀
         i : fin 3, «expr ∨ »(«expr = »(i, i₁), «expr ∨ »(«expr = »(i, i₂), «expr = »(i, i₃)))))))],
    { clear [ident h₁],
      dec_trivial ["!"] },
    have [ident h] [":", expr ∀ i, «expr ≠ »(i₁, i) → «expr∃ , »((j : fin 3), «expr = »(t.points j, p i))] [],
    { intros [ident i, ident hi],
      replace [ident hps] [] [":=", expr set.mem_of_mem_insert_of_ne (set.mem_of_mem_of_subset (set.mem_range_self i) hps) «expr ▸ »(h₁, hpi.ne hi.symm)],
      exact [expr hps] },
    rcases [expr h i₂ h₁₂, "with", "⟨", ident j₂, ",", ident h₂, "⟩"],
    rcases [expr h i₃ h₁₃, "with", "⟨", ident j₃, ",", ident h₃, "⟩"],
    have [ident hj₂₃] [":", expr «expr ≠ »(j₂, j₃)] [],
    { intro [ident he],
      rw ["[", expr he, ",", expr h₃, "]"] ["at", ident h₂],
      exact [expr h₂₃.symm (hpi h₂)] },
    exact [expr ⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩] },
  { right,
    have [ident hs] [] [":=", expr set.subset_diff_singleton hps h],
    rw [expr set.insert_diff_self_of_not_mem ho] ["at", ident hs],
    refine [expr set.eq_of_subset_of_card_le hs _],
    rw ["[", expr set.card_range_of_injective hpi, ",", expr set.card_range_of_injective t.independent.injective, "]"] [] }
end

/-- For any three points in an orthocentric system generated by
triangle `t`, there is a point in the subspace spanned by the triangle
from which the distance of all those three points equals the circumradius. -/
theorem exists_dist_eq_circumradius_of_subset_insert_orthocenter {t : triangle ℝ P}
  (ho : t.orthocenter ∉ Set.Range t.points) {p : Finₓ 3 → P}
  (hps : Set.Range p ⊆ insert t.orthocenter (Set.Range t.points)) (hpi : Function.Injective p) :
  ∃ (c : _)(_ : c ∈ affineSpan ℝ (Set.Range t.points)), ∀ p₁ _ : p₁ ∈ Set.Range p, dist p₁ c = t.circumradius :=
  by 
    rcases exists_of_range_subset_orthocentric_system ho hps hpi with
      (⟨i₁, i₂, i₃, j₂, j₃, h₁₂, h₁₃, h₂₃, h₁₂₃, h₁, hj₂₃, h₂, h₃⟩ | hs)
    ·
      use reflection (affineSpan ℝ (t.points '' {j₂, j₃})) t.circumcenter,
        reflection_mem_of_le_of_mem (affine_span_mono ℝ (Set.image_subset_range _ _)) t.circumcenter_mem_affine_span 
      intro p₁ hp₁ 
      rcases hp₁ with ⟨i, rfl⟩
      replace h₁₂₃ := h₁₂₃ i 
      repeat' 
        cases h₁₂₃
      ·
        rw [h₁]
        exact triangle.dist_orthocenter_reflection_circumcenter t hj₂₃
      ·
        rw [←h₂, dist_reflection_eq_of_mem _ (mem_affine_span ℝ (Set.mem_image_of_mem _ (Set.mem_insert _ _)))]
        exact t.dist_circumcenter_eq_circumradius _
      ·
        rw [←h₃,
          dist_reflection_eq_of_mem _
            (mem_affine_span ℝ (Set.mem_image_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))]
        exact t.dist_circumcenter_eq_circumradius _
    ·
      use t.circumcenter, t.circumcenter_mem_affine_span 
      intro p₁ hp₁ 
      rw [hs] at hp₁ 
      rcases hp₁ with ⟨i, rfl⟩
      exact t.dist_circumcenter_eq_circumradius _

/-- Any three points in an orthocentric system are affinely independent. -/
theorem orthocentric_system.affine_independent {s : Set P} (ho : orthocentric_system s) {p : Finₓ 3 → P}
  (hps : Set.Range p ⊆ s) (hpi : Function.Injective p) : AffineIndependent ℝ p :=
  by 
    rcases ho with ⟨t, hto, hst⟩
    rw [hst] at hps 
    rcases exists_dist_eq_circumradius_of_subset_insert_orthocenter hto hps hpi with ⟨c, hcs, hc⟩
    exact cospherical.affine_independent ⟨c, t.circumradius, hc⟩ Set.Subset.rfl hpi

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any three points in an orthocentric system span the same subspace
as the whole orthocentric system. -/
theorem affine_span_of_orthocentric_system
{s : set P}
(ho : orthocentric_system s)
{p : fin 3 → P}
(hps : «expr ⊆ »(set.range p, s))
(hpi : function.injective p) : «expr = »(affine_span exprℝ() (set.range p), affine_span exprℝ() s) :=
begin
  have [ident ha] [] [":=", expr ho.affine_independent hps hpi],
  rcases [expr ho, "with", "⟨", ident t, ",", ident hto, ",", ident hts, "⟩"],
  have [ident hs] [":", expr «expr = »(affine_span exprℝ() s, affine_span exprℝ() (set.range t.points))] [],
  { rw ["[", expr hts, ",", expr affine_span_insert_eq_affine_span exprℝ() t.orthocenter_mem_affine_span, "]"] [] },
  refine [expr ext_of_direction_eq _ ⟨p 0, mem_affine_span exprℝ() (set.mem_range_self _), mem_affine_span exprℝ() (hps (set.mem_range_self _))⟩],
  have [ident hfd] [":", expr finite_dimensional exprℝ() (affine_span exprℝ() s).direction] [],
  { rw [expr hs] [],
    apply_instance },
  haveI [] [] [":=", expr hfd],
  refine [expr eq_of_le_of_finrank_eq (direction_le (affine_span_mono exprℝ() hps)) _],
  rw ["[", expr hs, ",", expr direction_affine_span, ",", expr direction_affine_span, ",", expr ha.finrank_vector_span (fintype.card_fin _), ",", expr t.independent.finrank_vector_span (fintype.card_fin _), "]"] []
end

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- All triangles in an orthocentric system have the same circumradius. -/
theorem orthocentric_system.exists_circumradius_eq
{s : set P}
(ho : orthocentric_system s) : «expr∃ , »((r : exprℝ()), ∀
 t : triangle exprℝ() P, «expr ⊆ »(set.range t.points, s) → «expr = »(t.circumradius, r)) :=
begin
  rcases [expr ho, "with", "⟨", ident t, ",", ident hto, ",", ident hts, "⟩"],
  use [expr t.circumradius],
  intros [ident t₂, ident ht₂],
  have [ident ht₂s] [] [":=", expr ht₂],
  rw [expr hts] ["at", ident ht₂],
  rcases [expr exists_dist_eq_circumradius_of_subset_insert_orthocenter hto ht₂ t₂.independent.injective, "with", "⟨", ident c, ",", ident hc, ",", ident h, "⟩"],
  rw [expr set.forall_range_iff] ["at", ident h],
  have [ident hs] [":", expr «expr ⊆ »(set.range t.points, s)] [],
  { rw [expr hts] [],
    exact [expr set.subset_insert _ _] },
  rw ["[", expr affine_span_of_orthocentric_system ⟨t, hto, hts⟩ hs t.independent.injective, ",", "<-", expr affine_span_of_orthocentric_system ⟨t, hto, hts⟩ ht₂s t₂.independent.injective, "]"] ["at", ident hc],
  exact [expr (t₂.eq_circumradius_of_dist_eq hc h).symm]
end

-- error in Geometry.Euclidean.MongePoint: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given any triangle in an orthocentric system, the fourth point is
its orthocenter. -/
theorem orthocentric_system.eq_insert_orthocenter
{s : set P}
(ho : orthocentric_system s)
{t : triangle exprℝ() P}
(ht : «expr ⊆ »(set.range t.points, s)) : «expr = »(s, insert t.orthocenter (set.range t.points)) :=
begin
  rcases [expr ho, "with", "⟨", ident t₀, ",", ident ht₀o, ",", ident ht₀s, "⟩"],
  rw [expr ht₀s] ["at", ident ht],
  rcases [expr exists_of_range_subset_orthocentric_system ht₀o ht t.independent.injective, "with", "⟨", ident i₁, ",", ident i₂, ",", ident i₃, ",", ident j₂, ",", ident j₃, ",", ident h₁₂, ",", ident h₁₃, ",", ident h₂₃, ",", ident h₁₂₃, ",", ident h₁, ",", ident hj₂₃, ",", ident h₂, ",", ident h₃, "⟩", "|", ident hs],
  { obtain ["⟨", ident j₁, ",", ident hj₁₂, ",", ident hj₁₃, ",", ident hj₁₂₃, "⟩", ":", expr «expr∃ , »((j₁ : fin 3), «expr ∧ »(«expr ≠ »(j₁, j₂), «expr ∧ »(«expr ≠ »(j₁, j₃), ∀
        j : fin 3, «expr ∨ »(«expr = »(j, j₁), «expr ∨ »(«expr = »(j, j₂), «expr = »(j, j₃))))))],
    { clear [ident h₂, ident h₃],
      dec_trivial ["!"] },
    suffices [ident h] [":", expr «expr = »(t₀.points j₁, t.orthocenter)],
    { have [ident hui] [":", expr «expr = »((set.univ : set (fin 3)), {i₁, i₂, i₃})] [],
      { ext [] [ident x] [],
        simpa [] [] [] [] [] ["using", expr h₁₂₃ x] },
      have [ident huj] [":", expr «expr = »((set.univ : set (fin 3)), {j₁, j₂, j₃})] [],
      { ext [] [ident x] [],
        simpa [] [] [] [] [] ["using", expr hj₁₂₃ x] },
      rw ["[", "<-", expr h, ",", expr ht₀s, ",", "<-", expr set.image_univ, ",", expr huj, ",", "<-", expr set.image_univ, ",", expr hui, "]"] [],
      simp_rw ["[", expr set.image_insert_eq, ",", expr set.image_singleton, ",", expr h₁, ",", "<-", expr h₂, ",", "<-", expr h₃, "]"] [],
      rw [expr set.insert_comm] [] },
    exact [expr (triangle.orthocenter_replace_orthocenter_eq_point hj₁₂ hj₁₃ hj₂₃ h₁₂ h₁₃ h₂₃ h₁ h₂.symm h₃.symm).symm] },
  { rw [expr hs] [],
    convert [] [expr ht₀s] ["using", 2],
    exact [expr triangle.orthocenter_eq_of_range_eq hs] }
end

end EuclideanGeometry

