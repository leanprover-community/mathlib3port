import Mathbin.Geometry.Euclidean.Basic 
import Mathbin.LinearAlgebra.AffineSpace.FiniteDimensional 
import Mathbin.Tactic.DeriveFintype

/-!
# Circumcenter and circumradius

This file proves some lemmas on points equidistant from a set of
points, and defines the circumradius and circumcenter of a simplex.
There are also some definitions for use in calculations where it is
convenient to work with affine combinations of vertices together with
the circumcenter.

## Main definitions

* `circumcenter` and `circumradius` are the circumcenter and
  circumradius of a simplex.

## References

* https://en.wikipedia.org/wiki/Circumscribed_circle

-/


noncomputable theory

open_locale BigOperators

open_locale Classical

open_locale Real

open_locale RealInnerProductSpace

namespace EuclideanGeometry

open InnerProductGeometry

variable{V : Type _}{P : Type _}[InnerProductSpace ℝ V][MetricSpace P][NormedAddTorsor V P]

include V

open AffineSubspace

/-- `p` is equidistant from two points in `s` if and only if its
`orthogonal_projection` is. -/
theorem dist_eq_iff_dist_orthogonal_projection_eq {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
  {p1 p2 : P} (p3 : P) (hp1 : p1 ∈ s) (hp2 : p2 ∈ s) :
  dist p1 p3 = dist p2 p3 ↔ dist p1 (orthogonalProjection s p3) = dist p2 (orthogonalProjection s p3) :=
  by 
    rw [←mul_self_inj_of_nonneg dist_nonneg dist_nonneg, ←mul_self_inj_of_nonneg dist_nonneg dist_nonneg,
      dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq p3 hp1,
      dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq p3 hp2]
    simp 

/-- `p` is equidistant from a set of points in `s` if and only if its
`orthogonal_projection` is. -/
theorem dist_set_eq_iff_dist_orthogonal_projection_eq {s : AffineSubspace ℝ P} [Nonempty s] [CompleteSpace s.direction]
  {ps : Set P} (hps : ps ⊆ s) (p : P) :
  (Set.Pairwise ps fun p1 p2 => dist p1 p = dist p2 p) ↔
    Set.Pairwise ps fun p1 p2 => dist p1 (orthogonalProjection s p) = dist p2 (orthogonalProjection s p) :=
  ⟨fun h p1 hp1 p2 hp2 hne => (dist_eq_iff_dist_orthogonal_projection_eq p (hps hp1) (hps hp2)).1 (h p1 hp1 p2 hp2 hne),
    fun h p1 hp1 p2 hp2 hne =>
      (dist_eq_iff_dist_orthogonal_projection_eq p (hps hp1) (hps hp2)).2 (h p1 hp1 p2 hp2 hne)⟩

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- There exists `r` such that `p` has distance `r` from all the
points of a set of points in `s` if and only if there exists (possibly
different) `r` such that its `orthogonal_projection` has that distance
from all the points in that set. -/
theorem exists_dist_eq_iff_exists_dist_orthogonal_projection_eq
{s : affine_subspace exprℝ() P}
[nonempty s]
[complete_space s.direction]
{ps : set P}
(hps : «expr ⊆ »(ps, s))
(p : P) : «expr ↔ »(«expr∃ , »((r), ∀
  p1 «expr ∈ » ps, «expr = »(dist p1 p, r)), «expr∃ , »((r), ∀
  p1 «expr ∈ » ps, «expr = »(dist p1 «expr↑ »(orthogonal_projection s p), r))) :=
begin
  have [ident h] [] [":=", expr dist_set_eq_iff_dist_orthogonal_projection_eq hps p],
  simp_rw [expr set.pairwise_eq_iff_exists_eq] ["at", ident h],
  exact [expr h]
end

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The induction step for the existence and uniqueness of the
circumcenter.  Given a nonempty set of points in a nonempty affine
subspace whose direction is complete, such that there is a unique
(circumcenter, circumradius) pair for those points in that subspace,
and a point `p` not in that subspace, there is a unique (circumcenter,
circumradius) pair for the set with `p` added, in the span of the
subspace with `p` added. -/
theorem exists_unique_dist_eq_of_insert
{s : affine_subspace exprℝ() P}
[complete_space s.direction]
{ps : set P}
(hnps : ps.nonempty)
{p : P}
(hps : «expr ⊆ »(ps, s))
(hp : «expr ∉ »(p, s))
(hu : «expr∃! , »((cccr : «expr × »(P, exprℝ())), «expr ∧ »(«expr ∈ »(cccr.fst, s), ∀
   p1 «expr ∈ » ps, «expr = »(dist p1 cccr.fst, cccr.snd)))) : «expr∃! , »((cccr₂ : «expr × »(P, exprℝ())), «expr ∧ »(«expr ∈ »(cccr₂.fst, affine_span exprℝ() (insert p (s : set P))), ∀
  p1 «expr ∈ » insert p ps, «expr = »(dist p1 cccr₂.fst, cccr₂.snd))) :=
begin
  haveI [] [":", expr nonempty s] [":=", expr set.nonempty.to_subtype (hnps.mono hps)],
  rcases [expr hu, "with", "⟨", "⟨", ident cc, ",", ident cr, "⟩", ",", "⟨", ident hcc, ",", ident hcr, "⟩", ",", ident hcccru, "⟩"],
  simp [] [] ["only"] ["[", expr prod.fst, ",", expr prod.snd, "]"] [] ["at", ident hcc, ident hcr, ident hcccru],
  let [ident x] [] [":=", expr dist cc (orthogonal_projection s p)],
  let [ident y] [] [":=", expr dist p (orthogonal_projection s p)],
  have [ident hy0] [":", expr «expr ≠ »(y, 0)] [":=", expr dist_orthogonal_projection_ne_zero_of_not_mem hp],
  let [ident ycc₂] [] [":=", expr «expr / »(«expr - »(«expr + »(«expr * »(x, x), «expr * »(y, y)), «expr * »(cr, cr)), «expr * »(2, y))],
  let [ident cc₂] [] [":=", expr «expr +ᵥ »(«expr • »(«expr / »(ycc₂, y), («expr -ᵥ »(p, orthogonal_projection s p) : V)), cc)],
  let [ident cr₂] [] [":=", expr real.sqrt «expr + »(«expr * »(cr, cr), «expr * »(ycc₂, ycc₂))],
  use [expr (cc₂, cr₂)],
  simp [] [] ["only"] ["[", expr prod.fst, ",", expr prod.snd, "]"] [] [],
  have [ident hpo] [":", expr «expr = »(p, «expr +ᵥ »(«expr • »((1 : exprℝ()), («expr -ᵥ »(p, orthogonal_projection s p) : V)), orthogonal_projection s p))] [],
  { simp [] [] [] [] [] [] },
  split,
  { split,
    { refine [expr vadd_mem_of_mem_direction _ (mem_affine_span exprℝ() (set.mem_insert_of_mem _ hcc))],
      rw [expr direction_affine_span] [],
      exact [expr submodule.smul_mem _ _ (vsub_mem_vector_span exprℝ() (set.mem_insert _ _) (set.mem_insert_of_mem _ (orthogonal_projection_mem _)))] },
    { intros [ident p1, ident hp1],
      rw ["[", "<-", expr mul_self_inj_of_nonneg dist_nonneg (real.sqrt_nonneg _), ",", expr real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)), "]"] [],
      cases [expr hp1] [],
      { rw [expr hp1] [],
        rw ["[", expr hpo, ",", expr dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd (orthogonal_projection_mem p) hcc _ _ (vsub_orthogonal_projection_mem_direction_orthogonal s p), ",", "<-", expr dist_eq_norm_vsub V p, ",", expr dist_comm _ cc, "]"] [],
        field_simp [] ["[", expr hy0, "]"] [] [],
        ring [] },
      { rw ["[", expr dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq _ (hps hp1), ",", expr orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hcc, ",", expr subtype.coe_mk, ",", expr hcr _ hp1, ",", expr dist_eq_norm_vsub V cc₂ cc, ",", expr vadd_vsub, ",", expr norm_smul, ",", "<-", expr dist_eq_norm_vsub V, ",", expr real.norm_eq_abs, ",", expr abs_div, ",", expr abs_of_nonneg dist_nonneg, ",", expr div_mul_cancel _ hy0, ",", expr abs_mul_abs_self, "]"] [] } } },
  { rintros ["⟨", ident cc₃, ",", ident cr₃, "⟩", "⟨", ident hcc₃, ",", ident hcr₃, "⟩"],
    simp [] [] ["only"] ["[", expr prod.fst, ",", expr prod.snd, "]"] [] ["at", ident hcc₃, ident hcr₃],
    obtain ["⟨", ident t₃, ",", ident cc₃', ",", ident hcc₃', ",", ident hcc₃'', "⟩", ":", expr «expr∃ , »((r : exprℝ())
      (p0 : P)
      (hp0 : «expr ∈ »(p0, s)), «expr = »(cc₃, «expr +ᵥ »(«expr • »(r, «expr -ᵥ »(p, «expr↑ »(orthogonal_projection s p))), p0)))],
    { rwa [expr mem_affine_span_insert_iff (orthogonal_projection_mem p)] ["at", ident hcc₃] },
    have [ident hcr₃'] [":", expr «expr∃ , »((r), ∀
      p1 «expr ∈ » ps, «expr = »(dist p1 cc₃, r))] [":=", expr ⟨cr₃, λ p1 hp1, hcr₃ p1 (set.mem_insert_of_mem _ hp1)⟩],
    rw ["[", expr exists_dist_eq_iff_exists_dist_orthogonal_projection_eq hps cc₃, ",", expr hcc₃'', ",", expr orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hcc₃', "]"] ["at", ident hcr₃'],
    cases [expr hcr₃'] ["with", ident cr₃', ident hcr₃'],
    have [ident hu] [] [":=", expr hcccru (cc₃', cr₃')],
    simp [] [] ["only"] ["[", expr prod.fst, ",", expr prod.snd, "]"] [] ["at", ident hu],
    replace [ident hu] [] [":=", expr hu ⟨hcc₃', hcr₃'⟩],
    rw [expr prod.ext_iff] ["at", ident hu],
    simp [] [] ["only"] ["[", expr prod.fst, ",", expr prod.snd, "]"] [] ["at", ident hu],
    cases [expr hu] ["with", ident hucc, ident hucr],
    substs [ident hucc, ident hucr],
    have [ident hcr₃val] [":", expr «expr = »(cr₃, real.sqrt «expr + »(«expr * »(cr₃', cr₃'), «expr * »(«expr * »(t₃, y), «expr * »(t₃, y))))] [],
    { cases [expr hnps] ["with", ident p0, ident hp0],
      have [ident h'] [":", expr «expr = »(«expr↑ »((⟨cc₃', hcc₃'⟩ : s)), cc₃')] [":=", expr rfl],
      rw ["[", "<-", expr hcr₃ p0 (set.mem_insert_of_mem _ hp0), ",", expr hcc₃'', ",", "<-", expr mul_self_inj_of_nonneg dist_nonneg (real.sqrt_nonneg _), ",", expr real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)), ",", expr dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq _ (hps hp0), ",", expr orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hcc₃', ",", expr h', ",", expr hcr p0 hp0, ",", expr dist_eq_norm_vsub V _ cc₃', ",", expr vadd_vsub, ",", expr norm_smul, ",", "<-", expr dist_eq_norm_vsub V p, ",", expr real.norm_eq_abs, ",", "<-", expr mul_assoc, ",", expr mul_comm _ «expr| |»(t₃), ",", "<-", expr mul_assoc, ",", expr abs_mul_abs_self, "]"] [],
      ring [] },
    replace [ident hcr₃] [] [":=", expr hcr₃ p (set.mem_insert _ _)],
    rw ["[", expr hpo, ",", expr hcc₃'', ",", expr hcr₃val, ",", "<-", expr mul_self_inj_of_nonneg dist_nonneg (real.sqrt_nonneg _), ",", expr dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd (orthogonal_projection_mem p) hcc₃' _ _ (vsub_orthogonal_projection_mem_direction_orthogonal s p), ",", expr dist_comm, ",", "<-", expr dist_eq_norm_vsub V p, ",", expr real.mul_self_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)), "]"] ["at", ident hcr₃],
    change [expr «expr = »(«expr + »(«expr * »(x, x), «expr * »(_, «expr * »(y, y))), _)] [] ["at", ident hcr₃],
    rw ["[", expr show «expr = »(«expr + »(«expr * »(x, x), «expr * »(«expr * »(«expr - »(1, t₃), «expr - »(1, t₃)), «expr * »(y, y))), «expr + »(«expr - »(«expr + »(«expr * »(x, x), «expr * »(y, y)), «expr * »(«expr * »(2, y), «expr * »(t₃, y))), «expr * »(«expr * »(t₃, y), «expr * »(t₃, y)))), by ring [], ",", expr add_left_inj, "]"] ["at", ident hcr₃],
    have [ident ht₃] [":", expr «expr = »(t₃, «expr / »(ycc₂, y))] [],
    { field_simp [] ["[", "<-", expr hcr₃, ",", expr hy0, "]"] [] [],
      ring [] },
    subst [expr ht₃],
    change [expr «expr = »(cc₃, cc₂)] [] ["at", ident hcc₃''],
    congr' [] [],
    rw [expr hcr₃val] [],
    congr' [2] [],
    field_simp [] ["[", expr hy0, "]"] [] [],
    ring [] }
end

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:341:40: in conv: ././Mathport/Syntax/Translate/Basic.lean:385:40: in conv: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- Given a finite nonempty affinely independent family of points,
there is a unique (circumcenter, circumradius) pair for those points
in the affine subspace they span. -/
theorem _root_.affine_independent.exists_unique_dist_eq
{ι : Type*}
[hne : nonempty ι]
[fintype ι]
{p : ι → P}
(ha : affine_independent exprℝ() p) : «expr∃! , »((cccr : «expr × »(P, exprℝ())), «expr ∧ »(«expr ∈ »(cccr.fst, affine_span exprℝ() (set.range p)), ∀
  i, «expr = »(dist (p i) cccr.fst, cccr.snd))) :=
begin
  unfreezingI { induction [expr hn, ":", expr fintype.card ι] [] ["with", ident m, ident hm] ["generalizing", ident ι] },
  { exfalso,
    have [ident h] [] [":=", expr fintype.card_pos_iff.2 hne],
    rw [expr hn] ["at", ident h],
    exact [expr lt_irrefl 0 h] },
  { cases [expr m] [],
    { rw [expr fintype.card_eq_one_iff] ["at", ident hn],
      cases [expr hn] ["with", ident i, ident hi],
      haveI [] [":", expr unique ι] [":=", expr ⟨⟨i⟩, hi⟩],
      use [expr (p i, 0)],
      simp [] [] ["only"] ["[", expr prod.fst, ",", expr prod.snd, ",", expr set.range_unique, ",", expr affine_subspace.mem_affine_span_singleton, "]"] [] [],
      split,
      { simp_rw ["[", expr hi (default ι), "]"] [],
        use [expr rfl],
        intro [ident i1],
        rw [expr hi i1] [],
        exact [expr dist_self _] },
      { rintros ["⟨", ident cc, ",", ident cr, "⟩"],
        simp [] [] ["only"] ["[", expr prod.fst, ",", expr prod.snd, "]"] [] [],
        rintros ["⟨", ident rfl, ",", ident hdist, "⟩"],
        rw [expr hi (default ι)] [],
        congr' [] [],
        rw ["<-", expr hdist (default ι)] [],
        exact [expr dist_self _] } },
    { have [ident i] [] [":=", expr hne.some],
      let [ident ι2] [] [":=", expr {x // «expr ≠ »(x, i)}],
      have [ident hc] [":", expr «expr = »(fintype.card ι2, «expr + »(m, 1))] [],
      { rw [expr fintype.card_of_subtype (finset.univ.filter (λ x, «expr ≠ »(x, i)))] [],
        { rw [expr finset.filter_not] [],
          simp_rw [expr eq_comm] [],
          rw ["[", expr finset.filter_eq, ",", expr if_pos (finset.mem_univ _), ",", expr finset.card_sdiff (finset.subset_univ _), ",", expr finset.card_singleton, ",", expr finset.card_univ, ",", expr hn, "]"] [],
          simp [] [] [] [] [] [] },
        { simp [] [] [] [] [] [] } },
      haveI [] [":", expr nonempty ι2] [":=", expr fintype.card_pos_iff.1 «expr ▸ »(hc.symm, nat.zero_lt_succ _)],
      have [ident ha2] [":", expr affine_independent exprℝ() (λ i2 : ι2, p i2)] [":=", expr ha.subtype _],
      replace [ident hm] [] [":=", expr hm ha2 hc],
      have [ident hr] [":", expr «expr = »(set.range p, insert (p i) (set.range (λ i2 : ι2, p i2)))] [],
      { change [expr «expr = »(_, insert _ (set.range (λ i2 : {x | «expr ≠ »(x, i)}, p i2)))] [] [],
        rw ["[", "<-", expr set.image_eq_range, ",", "<-", expr set.image_univ, ",", "<-", expr set.image_insert_eq, "]"] [],
        congr' [] ["with", ident j],
        simp [] [] [] ["[", expr classical.em, "]"] [] [] },
      change [expr «expr∃! , »((cccr : «expr × »(P, exprℝ())), «expr ∧ »(_, ∀
         i2, λ q, «expr = »(dist q cccr.fst, cccr.snd) (p i2)))] [] [],
      conv [] [] { congr,
        funext,
        conv { congr,
          skip,
          rw ["<-", expr set.forall_range_iff] } },
      dsimp ["only"] [] [] [],
      rw [expr hr] [],
      change [expr «expr∃! , »((cccr : «expr × »(P, exprℝ())), «expr ∧ »(_, ∀
         i2 : ι2, λ q, «expr = »(dist q cccr.fst, cccr.snd) (p i2)))] [] ["at", ident hm],
      conv ["at", ident hm] [] { congr,
        funext,
        conv { congr,
          skip,
          rw ["<-", expr set.forall_range_iff] } },
      rw ["<-", expr affine_span_insert_affine_span] [],
      refine [expr exists_unique_dist_eq_of_insert (set.range_nonempty _) (subset_span_points exprℝ() _) _ hm],
      convert [] [expr ha.not_mem_affine_span_diff i set.univ] [],
      change [expr «expr = »(set.range (λ i2 : {x | «expr ≠ »(x, i)}, p i2), _)] [] [],
      rw ["<-", expr set.image_eq_range] [],
      congr' [] ["with", ident j],
      simp [] [] [] [] [] [],
      refl } }
end

end EuclideanGeometry

namespace Affine

namespace Simplex

open Finset AffineSubspace EuclideanGeometry

variable{V : Type _}{P : Type _}[InnerProductSpace ℝ V][MetricSpace P][NormedAddTorsor V P]

include V

/-- The pair (circumcenter, circumradius) of a simplex. -/
def circumcenter_circumradius {n : ℕ} (s : simplex ℝ P n) : P × ℝ :=
  s.independent.exists_unique_dist_eq.some

/-- The property satisfied by the (circumcenter, circumradius) pair. -/
theorem circumcenter_circumradius_unique_dist_eq {n : ℕ} (s : simplex ℝ P n) :
  (s.circumcenter_circumradius.fst ∈ affineSpan ℝ (Set.Range s.points) ∧
      ∀ i, dist (s.points i) s.circumcenter_circumradius.fst = s.circumcenter_circumradius.snd) ∧
    ∀ cccr : P × ℝ,
      (cccr.fst ∈ affineSpan ℝ (Set.Range s.points) ∧ ∀ i, dist (s.points i) cccr.fst = cccr.snd) →
        cccr = s.circumcenter_circumradius :=
  s.independent.exists_unique_dist_eq.some_spec

/-- The circumcenter of a simplex. -/
def circumcenter {n : ℕ} (s : simplex ℝ P n) : P :=
  s.circumcenter_circumradius.fst

/-- The circumradius of a simplex. -/
def circumradius {n : ℕ} (s : simplex ℝ P n) : ℝ :=
  s.circumcenter_circumradius.snd

/-- The circumcenter lies in the affine span. -/
theorem circumcenter_mem_affine_span {n : ℕ} (s : simplex ℝ P n) : s.circumcenter ∈ affineSpan ℝ (Set.Range s.points) :=
  s.circumcenter_circumradius_unique_dist_eq.1.1

/-- All points have distance from the circumcenter equal to the
circumradius. -/
@[simp]
theorem dist_circumcenter_eq_circumradius {n : ℕ} (s : simplex ℝ P n) :
  ∀ i, dist (s.points i) s.circumcenter = s.circumradius :=
  s.circumcenter_circumradius_unique_dist_eq.1.2

/-- All points have distance to the circumcenter equal to the
circumradius. -/
@[simp]
theorem dist_circumcenter_eq_circumradius' {n : ℕ} (s : simplex ℝ P n) :
  ∀ i, dist s.circumcenter (s.points i) = s.circumradius :=
  by 
    intro i 
    rw [dist_comm]
    exact dist_circumcenter_eq_circumradius _ _

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a point in the affine span from which all the points are
equidistant, that point is the circumcenter. -/
theorem eq_circumcenter_of_dist_eq
{n : exprℕ()}
(s : simplex exprℝ() P n)
{p : P}
(hp : «expr ∈ »(p, affine_span exprℝ() (set.range s.points)))
{r : exprℝ()}
(hr : ∀ i, «expr = »(dist (s.points i) p, r)) : «expr = »(p, s.circumcenter) :=
begin
  have [ident h] [] [":=", expr s.circumcenter_circumradius_unique_dist_eq.2 (p, r)],
  simp [] [] ["only"] ["[", expr hp, ",", expr hr, ",", expr forall_const, ",", expr eq_self_iff_true, ",", expr and_self, ",", expr prod.ext_iff, "]"] [] ["at", ident h],
  exact [expr h.1]
end

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a point in the affine span from which all the points are
equidistant, that distance is the circumradius. -/
theorem eq_circumradius_of_dist_eq
{n : exprℕ()}
(s : simplex exprℝ() P n)
{p : P}
(hp : «expr ∈ »(p, affine_span exprℝ() (set.range s.points)))
{r : exprℝ()}
(hr : ∀ i, «expr = »(dist (s.points i) p, r)) : «expr = »(r, s.circumradius) :=
begin
  have [ident h] [] [":=", expr s.circumcenter_circumradius_unique_dist_eq.2 (p, r)],
  simp [] [] ["only"] ["[", expr hp, ",", expr hr, ",", expr forall_const, ",", expr eq_self_iff_true, ",", expr and_self, ",", expr prod.ext_iff, "]"] [] ["at", ident h],
  exact [expr h.2]
end

/-- The circumradius is non-negative. -/
theorem circumradius_nonneg {n : ℕ} (s : simplex ℝ P n) : 0 ≤ s.circumradius :=
  s.dist_circumcenter_eq_circumradius 0 ▸ dist_nonneg

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The circumradius of a simplex with at least two points is
positive. -/
theorem circumradius_pos {n : exprℕ()} (s : simplex exprℝ() P «expr + »(n, 1)) : «expr < »(0, s.circumradius) :=
begin
  refine [expr lt_of_le_of_ne s.circumradius_nonneg _],
  intro [ident h],
  have [ident hr] [] [":=", expr s.dist_circumcenter_eq_circumradius],
  simp_rw ["[", "<-", expr h, ",", expr dist_eq_zero, "]"] ["at", ident hr],
  have [ident h01] [] [":=", expr s.independent.injective.ne (exprdec_trivial() : «expr ≠ »((0 : fin «expr + »(n, 2)), 1))],
  simpa [] [] [] ["[", expr hr, "]"] [] ["using", expr h01]
end

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The circumcenter of a 0-simplex equals its unique point. -/
theorem circumcenter_eq_point (s : simplex exprℝ() P 0) (i : fin 1) : «expr = »(s.circumcenter, s.points i) :=
begin
  have [ident h] [] [":=", expr s.circumcenter_mem_affine_span],
  rw ["[", expr set.range_unique, ",", expr mem_affine_span_singleton, "]"] ["at", ident h],
  rw [expr h] [],
  congr
end

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The circumcenter of a 1-simplex equals its centroid. -/
theorem circumcenter_eq_centroid
(s : simplex exprℝ() P 1) : «expr = »(s.circumcenter, finset.univ.centroid exprℝ() s.points) :=
begin
  have [ident hr] [":", expr set.pairwise set.univ (λ
    i
    j : fin 2, «expr = »(dist (s.points i) (finset.univ.centroid exprℝ() s.points), dist (s.points j) (finset.univ.centroid exprℝ() s.points)))] [],
  { intros [ident i, ident hi, ident j, ident hj, ident hij],
    rw ["[", expr finset.centroid_insert_singleton_fin, ",", expr dist_eq_norm_vsub V (s.points i), ",", expr dist_eq_norm_vsub V (s.points j), ",", expr vsub_vadd_eq_vsub_sub, ",", expr vsub_vadd_eq_vsub_sub, ",", "<-", expr one_smul exprℝ() «expr -ᵥ »(s.points i, s.points 0), ",", "<-", expr one_smul exprℝ() «expr -ᵥ »(s.points j, s.points 0), "]"] [],
    fin_cases [ident i] []; fin_cases [ident j] []; simp [] [] [] ["[", "-", ident one_smul, ",", "<-", expr sub_smul, "]"] [] []; norm_num [] [] },
  rw [expr set.pairwise_eq_iff_exists_eq] ["at", ident hr],
  cases [expr hr] ["with", ident r, ident hr],
  exact [expr (s.eq_circumcenter_of_dist_eq (centroid_mem_affine_span_of_card_eq_add_one exprℝ() _ (finset.card_fin 2)) (λ
     i, hr i (set.mem_univ _))).symm]
end

/-- If there exists a distance that a point has from all vertices of a
simplex, the orthogonal projection of that point onto the subspace
spanned by that simplex is its circumcenter.  -/
theorem orthogonal_projection_eq_circumcenter_of_exists_dist_eq {n : ℕ} (s : simplex ℝ P n) {p : P}
  (hr : ∃ r, ∀ i, dist (s.points i) p = r) :
  «expr↑ » (orthogonalProjection (affineSpan ℝ (Set.Range s.points)) p) = s.circumcenter :=
  by 
    change ∃ r : ℝ, ∀ i, (fun x => dist x p = r) (s.points i) at hr 
    conv  at hr => congr ext rw [←Set.forall_range_iff]
    rw [exists_dist_eq_iff_exists_dist_orthogonal_projection_eq (subset_affine_span ℝ _) p] at hr 
    cases' hr with r hr 
    exact s.eq_circumcenter_of_dist_eq (orthogonal_projection_mem p) fun i => hr _ (Set.mem_range_self i)

/-- If a point has the same distance from all vertices of a simplex,
the orthogonal projection of that point onto the subspace spanned by
that simplex is its circumcenter.  -/
theorem orthogonal_projection_eq_circumcenter_of_dist_eq {n : ℕ} (s : simplex ℝ P n) {p : P} {r : ℝ}
  (hr : ∀ i, dist (s.points i) p = r) :
  «expr↑ » (orthogonalProjection (affineSpan ℝ (Set.Range s.points)) p) = s.circumcenter :=
  s.orthogonal_projection_eq_circumcenter_of_exists_dist_eq ⟨r, hr⟩

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The orthogonal projection of the circumcenter onto a face is the
circumcenter of that face. -/
theorem orthogonal_projection_circumcenter
{n : exprℕ()}
(s : simplex exprℝ() P n)
{fs : finset (fin «expr + »(n, 1))}
{m : exprℕ()}
(h : «expr = »(fs.card, «expr + »(m, 1))) : «expr = »(«expr↑ »(orthogonal_projection (affine_span exprℝ() (set.range (s.face h).points)) s.circumcenter), (s.face h).circumcenter) :=
begin
  have [ident hr] [":", expr «expr∃ , »((r), ∀ i, «expr = »(dist ((s.face h).points i) s.circumcenter, r))] [],
  { use [expr s.circumradius],
    simp [] [] [] ["[", expr face_points, "]"] [] [] },
  exact [expr orthogonal_projection_eq_circumcenter_of_exists_dist_eq _ hr]
end

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Two simplices with the same points have the same circumcenter. -/
theorem circumcenter_eq_of_range_eq
{n : exprℕ()}
{s₁ s₂ : simplex exprℝ() P n}
(h : «expr = »(set.range s₁.points, set.range s₂.points)) : «expr = »(s₁.circumcenter, s₂.circumcenter) :=
begin
  have [ident hs] [":", expr «expr ∈ »(s₁.circumcenter, affine_span exprℝ() (set.range s₂.points))] [":=", expr «expr ▸ »(h, s₁.circumcenter_mem_affine_span)],
  have [ident hr] [":", expr ∀ i, «expr = »(dist (s₂.points i) s₁.circumcenter, s₁.circumradius)] [],
  { intro [ident i],
    have [ident hi] [":", expr «expr ∈ »(s₂.points i, set.range s₂.points)] [":=", expr set.mem_range_self _],
    rw ["[", "<-", expr h, ",", expr set.mem_range, "]"] ["at", ident hi],
    rcases [expr hi, "with", "⟨", ident j, ",", ident hj, "⟩"],
    rw ["[", "<-", expr hj, ",", expr s₁.dist_circumcenter_eq_circumradius j, "]"] [] },
  exact [expr s₂.eq_circumcenter_of_dist_eq hs hr]
end

omit V

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler fintype
/-- An index type for the vertices of a simplex plus its circumcenter.
This is for use in calculations where it is convenient to work with
affine combinations of vertices together with the circumcenter.  (An
equivalent form sometimes used in the literature is placing the
circumcenter at the origin and working with vectors for the vertices.) -/
@[derive #[expr fintype]]
inductive points_with_circumcenter_index (n : exprℕ())
| point_index : fin «expr + »(n, 1) → points_with_circumcenter_index
| circumcenter_index : points_with_circumcenter_index

open PointsWithCircumcenterIndex

instance points_with_circumcenter_index_inhabited (n : ℕ) : Inhabited (points_with_circumcenter_index n) :=
  ⟨circumcenter_index⟩

/-- `point_index` as an embedding. -/
def point_index_embedding (n : ℕ) : Finₓ (n+1) ↪ points_with_circumcenter_index n :=
  ⟨fun i => point_index i,
    fun _ _ h =>
      by 
        injection h⟩

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The sum of a function over `points_with_circumcenter_index`. -/
theorem sum_points_with_circumcenter
{α : Type*}
[add_comm_monoid α]
{n : exprℕ()}
(f : points_with_circumcenter_index n → α) : «expr = »(«expr∑ , »((i), f i), «expr + »(«expr∑ , »((i : fin «expr + »(n, 1)), f (point_index i)), f circumcenter_index)) :=
begin
  have [ident h] [":", expr «expr = »(univ, insert circumcenter_index (univ.map (point_index_embedding n)))] [],
  { ext [] [ident x] [],
    refine [expr ⟨λ h, _, λ _, mem_univ _⟩],
    cases [expr x] ["with", ident i],
    { exact [expr mem_insert_of_mem (mem_map_of_mem _ (mem_univ i))] },
    { exact [expr mem_insert_self _ _] } },
  change [expr «expr = »(_, «expr + »(«expr∑ , »((i), f (point_index_embedding n i)), _))] [] [],
  rw ["[", expr add_comm, ",", expr h, ",", "<-", expr sum_map, ",", expr sum_insert, "]"] [],
  simp_rw ["[", expr mem_map, ",", expr not_exists, "]"] [],
  intros [ident x, ident hx, ident h],
  injection [expr h] []
end

include V

/-- The vertices of a simplex plus its circumcenter. -/
def points_with_circumcenter {n : ℕ} (s : simplex ℝ P n) : points_with_circumcenter_index n → P
| point_index i => s.points i
| circumcenter_index => s.circumcenter

/-- `points_with_circumcenter`, applied to a `point_index` value,
equals `points` applied to that value. -/
@[simp]
theorem points_with_circumcenter_point {n : ℕ} (s : simplex ℝ P n) (i : Finₓ (n+1)) :
  s.points_with_circumcenter (point_index i) = s.points i :=
  rfl

/-- `points_with_circumcenter`, applied to `circumcenter_index`, equals the
circumcenter. -/
@[simp]
theorem points_with_circumcenter_eq_circumcenter {n : ℕ} (s : simplex ℝ P n) :
  s.points_with_circumcenter circumcenter_index = s.circumcenter :=
  rfl

omit V

/-- The weights for a single vertex of a simplex, in terms of
`points_with_circumcenter`. -/
def point_weights_with_circumcenter {n : ℕ} (i : Finₓ (n+1)) : points_with_circumcenter_index n → ℝ
| point_index j => if j = i then 1 else 0
| circumcenter_index => 0

/-- `point_weights_with_circumcenter` sums to 1. -/
@[simp]
theorem sum_point_weights_with_circumcenter {n : ℕ} (i : Finₓ (n+1)) : (∑j, point_weights_with_circumcenter i j) = 1 :=
  by 
    convert sum_ite_eq' univ (point_index i) (Function.const _ (1 : ℝ))
    ·
      ext j 
      cases j <;> simp [point_weights_with_circumcenter]
    ·
      simp 

include V

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A single vertex, in terms of `points_with_circumcenter`. -/
theorem point_eq_affine_combination_of_points_with_circumcenter
{n : exprℕ()}
(s : simplex exprℝ() P n)
(i : fin «expr + »(n, 1)) : «expr = »(s.points i, (univ : finset (points_with_circumcenter_index n)).affine_combination s.points_with_circumcenter (point_weights_with_circumcenter i)) :=
begin
  rw ["<-", expr points_with_circumcenter_point] [],
  symmetry,
  refine [expr affine_combination_of_eq_one_of_eq_zero _ _ _ (mem_univ _) (by simp [] [] [] ["[", expr point_weights_with_circumcenter, "]"] [] []) _],
  intros [ident i, ident hi, ident hn],
  cases [expr i] [],
  { have [ident h] [":", expr «expr ≠ »(i_1, i)] [":=", expr λ h, hn «expr ▸ »(h, rfl)],
    simp [] [] [] ["[", expr point_weights_with_circumcenter, ",", expr h, "]"] [] [] },
  { refl }
end

omit V

/-- The weights for the centroid of some vertices of a simplex, in
terms of `points_with_circumcenter`. -/
def centroid_weights_with_circumcenter {n : ℕ} (fs : Finset (Finₓ (n+1))) : points_with_circumcenter_index n → ℝ
| point_index i => if i ∈ fs then (card fs : ℝ)⁻¹ else 0
| circumcenter_index => 0

/-- `centroid_weights_with_circumcenter` sums to 1, if the `finset` is
nonempty. -/
@[simp]
theorem sum_centroid_weights_with_circumcenter {n : ℕ} {fs : Finset (Finₓ (n+1))} (h : fs.nonempty) :
  (∑i, centroid_weights_with_circumcenter fs i) = 1 :=
  by 
    simpRw [sum_points_with_circumcenter, centroid_weights_with_circumcenter, add_zeroₓ,
      ←fs.sum_centroid_weights_eq_one_of_nonempty ℝ h, Set.sum_indicator_subset _ fs.subset_univ]
    rcongr

include V

/-- The centroid of some vertices of a simplex, in terms of
`points_with_circumcenter`. -/
theorem centroid_eq_affine_combination_of_points_with_circumcenter {n : ℕ} (s : simplex ℝ P n)
  (fs : Finset (Finₓ (n+1))) :
  fs.centroid ℝ s.points =
    (univ : Finset (points_with_circumcenter_index n)).affineCombination s.points_with_circumcenter
      (centroid_weights_with_circumcenter fs) :=
  by 
    simpRw [centroid_def, affine_combination_apply, weighted_vsub_of_point_apply, sum_points_with_circumcenter,
      centroid_weights_with_circumcenter, points_with_circumcenter_point, zero_smul, add_zeroₓ, centroid_weights,
      Set.sum_indicator_subset_of_eq_zero (Function.const (Finₓ (n+1)) ((card fs : ℝ)⁻¹))
        (fun i wi => wi • (s.points i -ᵥ Classical.choice AddTorsor.nonempty)) fs.subset_univ fun i => zero_smul ℝ _,
      Set.indicator_apply]
    congr 
    funext 
    congr 2

omit V

/-- The weights for the circumcenter of a simplex, in terms of
`points_with_circumcenter`. -/
def circumcenter_weights_with_circumcenter (n : ℕ) : points_with_circumcenter_index n → ℝ
| point_index i => 0
| circumcenter_index => 1

/-- `circumcenter_weights_with_circumcenter` sums to 1. -/
@[simp]
theorem sum_circumcenter_weights_with_circumcenter (n : ℕ) : (∑i, circumcenter_weights_with_circumcenter n i) = 1 :=
  by 
    convert sum_ite_eq' univ circumcenter_index (Function.const _ (1 : ℝ))
    ·
      ext ⟨j⟩ <;> simp [circumcenter_weights_with_circumcenter]
    ·
      simp 

include V

/-- The circumcenter of a simplex, in terms of
`points_with_circumcenter`. -/
theorem circumcenter_eq_affine_combination_of_points_with_circumcenter {n : ℕ} (s : simplex ℝ P n) :
  s.circumcenter =
    (univ : Finset (points_with_circumcenter_index n)).affineCombination s.points_with_circumcenter
      (circumcenter_weights_with_circumcenter n) :=
  by 
    rw [←points_with_circumcenter_eq_circumcenter]
    symm 
    refine' affine_combination_of_eq_one_of_eq_zero _ _ _ (mem_univ _) rfl _ 
    rintro ⟨i⟩ hi hn <;> tauto

omit V

/-- The weights for the reflection of the circumcenter in an edge of a
simplex.  This definition is only valid with `i₁ ≠ i₂`. -/
def reflection_circumcenter_weights_with_circumcenter {n : ℕ} (i₁ i₂ : Finₓ (n+1)) :
  points_with_circumcenter_index n → ℝ
| point_index i => if i = i₁ ∨ i = i₂ then 1 else 0
| circumcenter_index => -1

/-- `reflection_circumcenter_weights_with_circumcenter` sums to 1. -/
@[simp]
theorem sum_reflection_circumcenter_weights_with_circumcenter {n : ℕ} {i₁ i₂ : Finₓ (n+1)} (h : i₁ ≠ i₂) :
  (∑i, reflection_circumcenter_weights_with_circumcenter i₁ i₂ i) = 1 :=
  by 
    simpRw [sum_points_with_circumcenter, reflection_circumcenter_weights_with_circumcenter, sum_ite, sum_const,
      filter_or, filter_eq']
    rw [card_union_eq]
    ·
      simp 
    ·
      simpa only [if_true, mem_univ, disjoint_singleton] using h

include V

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The reflection of the circumcenter of a simplex in an edge, in
terms of `points_with_circumcenter`. -/
theorem reflection_circumcenter_eq_affine_combination_of_points_with_circumcenter
{n : exprℕ()}
(s : simplex exprℝ() P n)
{i₁ i₂ : fin «expr + »(n, 1)}
(h : «expr ≠ »(i₁, i₂)) : «expr = »(reflection (affine_span exprℝ() «expr '' »(s.points, {i₁, i₂})) s.circumcenter, (univ : finset (points_with_circumcenter_index n)).affine_combination s.points_with_circumcenter (reflection_circumcenter_weights_with_circumcenter i₁ i₂)) :=
begin
  have [ident hc] [":", expr «expr = »(card ({i₁, i₂} : finset (fin «expr + »(n, 1))), 2)] [],
  { simp [] [] [] ["[", expr h, "]"] [] [] },
  have [ident h_faces] [":", expr «expr = »(«expr↑ »(orthogonal_projection (affine_span exprℝ() «expr '' »(s.points, {i₁, i₂})) s.circumcenter), «expr↑ »(orthogonal_projection (affine_span exprℝ() (set.range (s.face hc).points)) s.circumcenter))] [],
  { apply [expr eq_orthogonal_projection_of_eq_subspace],
    simp [] [] [] [] [] [] },
  rw ["[", expr euclidean_geometry.reflection_apply, ",", expr h_faces, ",", expr s.orthogonal_projection_circumcenter hc, ",", expr circumcenter_eq_centroid, ",", expr s.face_centroid_eq_centroid hc, ",", expr centroid_eq_affine_combination_of_points_with_circumcenter, ",", expr circumcenter_eq_affine_combination_of_points_with_circumcenter, ",", "<-", expr @vsub_eq_zero_iff_eq V, ",", expr affine_combination_vsub, ",", expr weighted_vsub_vadd_affine_combination, ",", expr affine_combination_vsub, ",", expr weighted_vsub_apply, ",", expr sum_points_with_circumcenter, "]"] [],
  simp_rw ["[", expr pi.sub_apply, ",", expr pi.add_apply, ",", expr pi.sub_apply, ",", expr sub_smul, ",", expr add_smul, ",", expr sub_smul, ",", expr centroid_weights_with_circumcenter, ",", expr circumcenter_weights_with_circumcenter, ",", expr reflection_circumcenter_weights_with_circumcenter, ",", expr ite_smul, ",", expr zero_smul, ",", expr sub_zero, ",", expr apply_ite2 ((«expr + »)), ",", expr add_zero, ",", "<-", expr add_smul, ",", expr hc, ",", expr zero_sub, ",", expr neg_smul, ",", expr sub_self, ",", expr add_zero, "]"] [],
  convert [] [expr sum_const_zero] [],
  norm_num [] []
end

end Simplex

end Affine

namespace EuclideanGeometry

open Affine AffineSubspace FiniteDimensional

variable{V : Type _}{P : Type _}[InnerProductSpace ℝ V][MetricSpace P][NormedAddTorsor V P]

include V

/-- Given a nonempty affine subspace, whose direction is complete,
that contains a set of points, those points are cospherical if and
only if they are equidistant from some point in that subspace. -/
theorem cospherical_iff_exists_mem_of_complete {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s) [Nonempty s]
  [CompleteSpace s.direction] :
  cospherical ps ↔ ∃ (center : _)(_ : center ∈ s)(radius : ℝ), ∀ p _ : p ∈ ps, dist p center = radius :=
  by 
    split 
    ·
      rintro ⟨c, hcr⟩
      rw [exists_dist_eq_iff_exists_dist_orthogonal_projection_eq h c] at hcr 
      exact ⟨orthogonalProjection s c, orthogonal_projection_mem _, hcr⟩
    ·
      exact fun ⟨c, hc, hd⟩ => ⟨c, hd⟩

/-- Given a nonempty affine subspace, whose direction is
finite-dimensional, that contains a set of points, those points are
cospherical if and only if they are equidistant from some point in
that subspace. -/
theorem cospherical_iff_exists_mem_of_finite_dimensional {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s) [Nonempty s]
  [FiniteDimensional ℝ s.direction] :
  cospherical ps ↔ ∃ (center : _)(_ : center ∈ s)(radius : ℝ), ∀ p _ : p ∈ ps, dist p center = radius :=
  cospherical_iff_exists_mem_of_complete h

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- All n-simplices among cospherical points in an n-dimensional
subspace have the same circumradius. -/
theorem exists_circumradius_eq_of_cospherical_subset
{s : affine_subspace exprℝ() P}
{ps : set P}
(h : «expr ⊆ »(ps, s))
[nonempty s]
{n : exprℕ()}
[finite_dimensional exprℝ() s.direction]
(hd : «expr = »(finrank exprℝ() s.direction, n))
(hc : cospherical ps) : «expr∃ , »((r : exprℝ()), ∀
 sx : simplex exprℝ() P n, «expr ⊆ »(set.range sx.points, ps) → «expr = »(sx.circumradius, r)) :=
begin
  rw [expr cospherical_iff_exists_mem_of_finite_dimensional h] ["at", ident hc],
  rcases [expr hc, "with", "⟨", ident c, ",", ident hc, ",", ident r, ",", ident hcr, "⟩"],
  use [expr r],
  intros [ident sx, ident hsxps],
  have [ident hsx] [":", expr «expr = »(affine_span exprℝ() (set.range sx.points), s)] [],
  { refine [expr sx.independent.affine_span_eq_of_le_of_card_eq_finrank_add_one (span_points_subset_coe_of_subset_coe (hsxps.trans h)) _],
    simp [] [] [] ["[", expr hd, "]"] [] [] },
  have [ident hc] [":", expr «expr ∈ »(c, affine_span exprℝ() (set.range sx.points))] [":=", expr «expr ▸ »(hsx.symm, hc)],
  exact [expr (sx.eq_circumradius_of_dist_eq hc (λ i, hcr (sx.points i) (hsxps (set.mem_range_self i)))).symm]
end

/-- Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumradius. -/
theorem circumradius_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s) [Nonempty s] {n : ℕ}
  [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = n) (hc : cospherical ps) {sx₁ sx₂ : simplex ℝ P n}
  (hsx₁ : Set.Range sx₁.points ⊆ ps) (hsx₂ : Set.Range sx₂.points ⊆ ps) : sx₁.circumradius = sx₂.circumradius :=
  by 
    rcases exists_circumradius_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
    rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- All n-simplices among cospherical points in n-space have the same
circumradius. -/
theorem exists_circumradius_eq_of_cospherical
{ps : set P}
{n : exprℕ()}
[finite_dimensional exprℝ() V]
(hd : «expr = »(finrank exprℝ() V, n))
(hc : cospherical ps) : «expr∃ , »((r : exprℝ()), ∀
 sx : simplex exprℝ() P n, «expr ⊆ »(set.range sx.points, ps) → «expr = »(sx.circumradius, r)) :=
begin
  haveI [] [":", expr nonempty («expr⊤»() : affine_subspace exprℝ() P)] [":=", expr set.univ.nonempty],
  rw ["[", "<-", expr finrank_top, ",", "<-", expr direction_top exprℝ() V P, "]"] ["at", ident hd],
  refine [expr exists_circumradius_eq_of_cospherical_subset _ hd hc],
  exact [expr set.subset_univ _]
end

/-- Two n-simplices among cospherical points in n-space have the same
circumradius. -/
theorem circumradius_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V] (hd : finrank ℝ V = n)
  (hc : cospherical ps) {sx₁ sx₂ : simplex ℝ P n} (hsx₁ : Set.Range sx₁.points ⊆ ps)
  (hsx₂ : Set.Range sx₂.points ⊆ ps) : sx₁.circumradius = sx₂.circumradius :=
  by 
    rcases exists_circumradius_eq_of_cospherical hd hc with ⟨r, hr⟩
    rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- All n-simplices among cospherical points in an n-dimensional
subspace have the same circumcenter. -/
theorem exists_circumcenter_eq_of_cospherical_subset
{s : affine_subspace exprℝ() P}
{ps : set P}
(h : «expr ⊆ »(ps, s))
[nonempty s]
{n : exprℕ()}
[finite_dimensional exprℝ() s.direction]
(hd : «expr = »(finrank exprℝ() s.direction, n))
(hc : cospherical ps) : «expr∃ , »((c : P), ∀
 sx : simplex exprℝ() P n, «expr ⊆ »(set.range sx.points, ps) → «expr = »(sx.circumcenter, c)) :=
begin
  rw [expr cospherical_iff_exists_mem_of_finite_dimensional h] ["at", ident hc],
  rcases [expr hc, "with", "⟨", ident c, ",", ident hc, ",", ident r, ",", ident hcr, "⟩"],
  use [expr c],
  intros [ident sx, ident hsxps],
  have [ident hsx] [":", expr «expr = »(affine_span exprℝ() (set.range sx.points), s)] [],
  { refine [expr sx.independent.affine_span_eq_of_le_of_card_eq_finrank_add_one (span_points_subset_coe_of_subset_coe (hsxps.trans h)) _],
    simp [] [] [] ["[", expr hd, "]"] [] [] },
  have [ident hc] [":", expr «expr ∈ »(c, affine_span exprℝ() (set.range sx.points))] [":=", expr «expr ▸ »(hsx.symm, hc)],
  exact [expr (sx.eq_circumcenter_of_dist_eq hc (λ i, hcr (sx.points i) (hsxps (set.mem_range_self i)))).symm]
end

/-- Two n-simplices among cospherical points in an n-dimensional
subspace have the same circumcenter. -/
theorem circumcenter_eq_of_cospherical_subset {s : AffineSubspace ℝ P} {ps : Set P} (h : ps ⊆ s) [Nonempty s] {n : ℕ}
  [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = n) (hc : cospherical ps) {sx₁ sx₂ : simplex ℝ P n}
  (hsx₁ : Set.Range sx₁.points ⊆ ps) (hsx₂ : Set.Range sx₂.points ⊆ ps) : sx₁.circumcenter = sx₂.circumcenter :=
  by 
    rcases exists_circumcenter_eq_of_cospherical_subset h hd hc with ⟨r, hr⟩
    rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- All n-simplices among cospherical points in n-space have the same
circumcenter. -/
theorem exists_circumcenter_eq_of_cospherical
{ps : set P}
{n : exprℕ()}
[finite_dimensional exprℝ() V]
(hd : «expr = »(finrank exprℝ() V, n))
(hc : cospherical ps) : «expr∃ , »((c : P), ∀
 sx : simplex exprℝ() P n, «expr ⊆ »(set.range sx.points, ps) → «expr = »(sx.circumcenter, c)) :=
begin
  haveI [] [":", expr nonempty («expr⊤»() : affine_subspace exprℝ() P)] [":=", expr set.univ.nonempty],
  rw ["[", "<-", expr finrank_top, ",", "<-", expr direction_top exprℝ() V P, "]"] ["at", ident hd],
  refine [expr exists_circumcenter_eq_of_cospherical_subset _ hd hc],
  exact [expr set.subset_univ _]
end

/-- Two n-simplices among cospherical points in n-space have the same
circumcenter. -/
theorem circumcenter_eq_of_cospherical {ps : Set P} {n : ℕ} [FiniteDimensional ℝ V] (hd : finrank ℝ V = n)
  (hc : cospherical ps) {sx₁ sx₂ : simplex ℝ P n} (hsx₁ : Set.Range sx₁.points ⊆ ps)
  (hsx₂ : Set.Range sx₂.points ⊆ ps) : sx₁.circumcenter = sx₂.circumcenter :=
  by 
    rcases exists_circumcenter_eq_of_cospherical hd hc with ⟨r, hr⟩
    rw [hr sx₁ hsx₁, hr sx₂ hsx₂]

-- error in Geometry.Euclidean.Circumcenter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Suppose all distances from `p₁` and `p₂` to the points of a
simplex are equal, and that `p₁` and `p₂` lie in the affine span of
`p` with the vertices of that simplex.  Then `p₁` and `p₂` are equal
or reflections of each other in the affine span of the vertices of the
simplex. -/
theorem eq_or_eq_reflection_of_dist_eq
{n : exprℕ()}
{s : simplex exprℝ() P n}
{p p₁ p₂ : P}
{r : exprℝ()}
(hp₁ : «expr ∈ »(p₁, affine_span exprℝ() (insert p (set.range s.points))))
(hp₂ : «expr ∈ »(p₂, affine_span exprℝ() (insert p (set.range s.points))))
(h₁ : ∀ i, «expr = »(dist (s.points i) p₁, r))
(h₂ : ∀
 i, «expr = »(dist (s.points i) p₂, r)) : «expr ∨ »(«expr = »(p₁, p₂), «expr = »(p₁, reflection (affine_span exprℝ() (set.range s.points)) p₂)) :=
begin
  let [ident span_s] [] [":=", expr affine_span exprℝ() (set.range s.points)],
  have [ident h₁'] [] [":=", expr s.orthogonal_projection_eq_circumcenter_of_dist_eq h₁],
  have [ident h₂'] [] [":=", expr s.orthogonal_projection_eq_circumcenter_of_dist_eq h₂],
  rw ["[", "<-", expr affine_span_insert_affine_span, ",", expr mem_affine_span_insert_iff (orthogonal_projection_mem p), "]"] ["at", ident hp₁, ident hp₂],
  obtain ["⟨", ident r₁, ",", ident p₁o, ",", ident hp₁o, ",", ident hp₁, "⟩", ":=", expr hp₁],
  obtain ["⟨", ident r₂, ",", ident p₂o, ",", ident hp₂o, ",", ident hp₂, "⟩", ":=", expr hp₂],
  obtain [ident rfl, ":", expr «expr = »(«expr↑ »(orthogonal_projection span_s p₁), p₁o)],
  { have [] [] [":=", expr orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hp₁o],
    rw ["<-", expr hp₁] ["at", ident this],
    rw [expr this] [],
    refl },
  rw [expr h₁'] ["at", ident hp₁],
  obtain [ident rfl, ":", expr «expr = »(«expr↑ »(orthogonal_projection span_s p₂), p₂o)],
  { have [] [] [":=", expr orthogonal_projection_vadd_smul_vsub_orthogonal_projection _ _ hp₂o],
    rw ["<-", expr hp₂] ["at", ident this],
    rw [expr this] [],
    refl },
  rw [expr h₂'] ["at", ident hp₂],
  have [ident h] [":", expr «expr ∈ »(s.points 0, span_s)] [":=", expr mem_affine_span exprℝ() (set.mem_range_self _)],
  have [ident hd₁] [":", expr «expr = »(«expr * »(dist p₁ s.circumcenter, dist p₁ s.circumcenter), «expr - »(«expr * »(r, r), «expr * »(s.circumradius, s.circumradius)))] [],
  { rw ["[", expr dist_comm, ",", "<-", expr h₁ 0, ",", expr dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq p₁ h, "]"] [],
    simp [] [] ["only"] ["[", expr h₁', ",", expr dist_comm p₁, ",", expr add_sub_cancel', ",", expr simplex.dist_circumcenter_eq_circumradius, "]"] [] [] },
  have [ident hd₂] [":", expr «expr = »(«expr * »(dist p₂ s.circumcenter, dist p₂ s.circumcenter), «expr - »(«expr * »(r, r), «expr * »(s.circumradius, s.circumradius)))] [],
  { rw ["[", expr dist_comm, ",", "<-", expr h₂ 0, ",", expr dist_sq_eq_dist_orthogonal_projection_sq_add_dist_orthogonal_projection_sq p₂ h, "]"] [],
    simp [] [] ["only"] ["[", expr h₂', ",", expr dist_comm p₂, ",", expr add_sub_cancel', ",", expr simplex.dist_circumcenter_eq_circumradius, "]"] [] [] },
  rw ["[", "<-", expr hd₂, ",", expr hp₁, ",", expr hp₂, ",", expr dist_eq_norm_vsub V _ s.circumcenter, ",", expr dist_eq_norm_vsub V _ s.circumcenter, ",", expr vadd_vsub, ",", expr vadd_vsub, ",", "<-", expr real_inner_self_eq_norm_mul_norm, ",", "<-", expr real_inner_self_eq_norm_mul_norm, ",", expr real_inner_smul_left, ",", expr real_inner_smul_left, ",", expr real_inner_smul_right, ",", expr real_inner_smul_right, ",", "<-", expr mul_assoc, ",", "<-", expr mul_assoc, "]"] ["at", ident hd₁],
  by_cases [expr hp, ":", expr «expr = »(p, orthogonal_projection span_s p)],
  { rw ["[", expr hp₁, ",", expr hp₂, ",", "<-", expr hp, "]"] [],
    simp [] [] ["only"] ["[", expr true_or, ",", expr eq_self_iff_true, ",", expr smul_zero, ",", expr vsub_self, "]"] [] [] },
  { have [ident hz] [":", expr «expr ≠ »(«expr⟪ , ⟫»(«expr -ᵥ »(p, orthogonal_projection span_s p), «expr -ᵥ »(p, orthogonal_projection span_s p)), 0)] [],
    by simpa [] [] ["only"] ["[", expr ne.def, ",", expr vsub_eq_zero_iff_eq, ",", expr inner_self_eq_zero, "]"] [] ["using", expr hp],
    rw ["[", expr mul_left_inj' hz, ",", expr mul_self_eq_mul_self_iff, "]"] ["at", ident hd₁],
    rw ["[", expr hp₁, ",", expr hp₂, "]"] [],
    cases [expr hd₁] [],
    { left,
      rw [expr hd₁] [] },
    { right,
      rw ["[", expr hd₁, ",", expr reflection_vadd_smul_vsub_orthogonal_projection p r₂ s.circumcenter_mem_affine_span, ",", expr neg_smul, "]"] [] } }
end

end EuclideanGeometry

