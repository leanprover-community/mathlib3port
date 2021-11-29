import Mathbin.Analysis.Convex.Jensen 
import Mathbin.Analysis.NormedSpace.FiniteDimension 
import Mathbin.Topology.PathConnected 
import Mathbin.Topology.Algebra.Affine

/-!
# Topological and metric properties of convex sets

We prove the following facts:

* `convex.interior` : interior of a convex set is convex;
* `convex.closure` : closure of a convex set is convex;
* `set.finite.compact_convex_hull` : convex hull of a finite set is compact;
* `set.finite.is_closed_convex_hull` : convex hull of a finite set is closed;
* `convex_on_dist` : distance to a fixed point is convex on any convex set;
* `convex_hull_ediam`, `convex_hull_diam` : convex hull of a set has the same (e)metric diameter
  as the original set;
* `bounded_convex_hull` : convex hull of a set is bounded if and only if the original set
  is bounded.
* `bounded_std_simplex`, `is_closed_std_simplex`, `compact_std_simplex`: topological properties
  of the standard simplex;
-/


variable{ι : Type _}{E : Type _}

open Set

open_locale Pointwise

theorem Real.convex_iff_is_preconnected {s : Set ℝ} : Convex ℝ s ↔ IsPreconnected s :=
  convex_iff_ord_connected.trans is_preconnected_iff_ord_connected.symm

alias Real.convex_iff_is_preconnected ↔ Convex.is_preconnected IsPreconnected.convex

/-! ### Standard simplex -/


section StdSimplex

variable[Fintype ι]

/-- Every vector in `std_simplex 𝕜 ι` has `max`-norm at most `1`. -/
theorem std_simplex_subset_closed_ball : StdSimplex ℝ ι ⊆ Metric.ClosedBall 0 1 :=
  by 
    intro f hf 
    rw [Metric.mem_closed_ball, dist_zero_right]
    refine' Nnreal.coe_one ▸ Nnreal.coe_le_coe.2$ Finset.sup_le$ fun x hx => _ 
    change |f x| ≤ 1
    rw [abs_of_nonneg$ hf.1 x]
    exact (mem_Icc_of_mem_std_simplex hf x).2

variable(ι)

/-- `std_simplex ℝ ι` is bounded. -/
theorem bounded_std_simplex : Metric.Bounded (StdSimplex ℝ ι) :=
  (Metric.bounded_iff_subset_ball 0).2 ⟨1, std_simplex_subset_closed_ball⟩

/-- `std_simplex ℝ ι` is closed. -/
theorem is_closed_std_simplex : IsClosed (StdSimplex ℝ ι) :=
  (std_simplex_eq_inter ℝ ι).symm ▸
    IsClosed.inter (is_closed_Inter$ fun i => is_closed_le continuous_const (continuous_apply i))
      (is_closed_eq (continuous_finset_sum _$ fun x _ => continuous_apply x) continuous_const)

/-- `std_simplex ℝ ι` is compact. -/
theorem compact_std_simplex : IsCompact (StdSimplex ℝ ι) :=
  Metric.compact_iff_closed_bounded.2 ⟨is_closed_std_simplex ι, bounded_std_simplex ι⟩

end StdSimplex

/-! ### Topological vector space -/


section HasContinuousSmul

variable[AddCommGroupₓ E][Module ℝ E][TopologicalSpace E][TopologicalAddGroup E][HasContinuousSmul ℝ E]

/-- In a topological vector space, the interior of a convex set is convex. -/
theorem Convex.interior {s : Set E} (hs : Convex ℝ s) : Convex ℝ (Interior s) :=
  convex_iff_pointwise_add_subset.mpr$
    fun a b ha hb hab =>
      have h : IsOpen ((a • Interior s)+b • Interior s) :=
        Or.elim (Classical.em (a = 0))
          (fun heq =>
            have hne : b ≠ 0 :=
              by 
                rw [HEq, zero_addₓ] at hab 
                rw [hab]
                exact one_ne_zero 
            by 
              rw [←image_smul]
              exact (is_open_map_smul₀ hne _ is_open_interior).add_left)
          fun hne =>
            by 
              rw [←image_smul]
              exact (is_open_map_smul₀ hne _ is_open_interior).add_right
      (subset_interior_iff_subset_of_open h).mpr$
        subset.trans
          (by 
            simp only [←image_smul]
            apply add_subset_add <;> exact image_subset _ interior_subset)
          (convex_iff_pointwise_add_subset.mp hs ha hb hab)

-- error in Analysis.Convex.Topology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- In a topological vector space, the closure of a convex set is convex. -/
theorem convex.closure {s : set E} (hs : convex exprℝ() s) : convex exprℝ() (closure s) :=
λ x y hx hy a b ha hb hab, let f : E → E → E := λ x' y', «expr + »(«expr • »(a, x'), «expr • »(b, y')) in
have hf : continuous (λ
 p : «expr × »(E, E), f p.1 p.2), from (continuous_const.smul continuous_fst).add (continuous_const.smul continuous_snd),
show «expr ∈ »(f x y, closure s), from mem_closure_of_continuous2 hf hx hy (λ
 x' hx' y' hy', subset_closure (hs hx' hy' ha hb hab))

-- error in Analysis.Convex.Topology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Convex hull of a finite set is compact. -/
theorem set.finite.compact_convex_hull {s : set E} (hs : finite s) : is_compact (convex_hull exprℝ() s) :=
begin
  rw ["[", expr hs.convex_hull_eq_image, "]"] [],
  apply [expr (compact_std_simplex _).image],
  haveI [] [] [":=", expr hs.fintype],
  apply [expr linear_map.continuous_on_pi]
end

/-- Convex hull of a finite set is closed. -/
theorem Set.Finite.is_closed_convex_hull [T2Space E] {s : Set E} (hs : finite s) : IsClosed (convexHull ℝ s) :=
  hs.compact_convex_hull.is_closed

-- error in Analysis.Convex.Topology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `x ∈ s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`. -/
theorem convex.add_smul_sub_mem_interior
{s : set E}
(hs : convex exprℝ() s)
{x y : E}
(hx : «expr ∈ »(x, s))
(hy : «expr ∈ »(y, interior s))
{t : exprℝ()}
(ht : «expr ∈ »(t, Ioc (0 : exprℝ()) 1)) : «expr ∈ »(«expr + »(x, «expr • »(t, «expr - »(y, x))), interior s) :=
begin
  let [ident f] [] [":=", expr λ z, «expr + »(x, «expr • »(t, «expr - »(z, x)))],
  have [] [":", expr is_open_map f] [":=", expr (is_open_map_add_left _).comp ((is_open_map_smul (units.mk0 _ ht.1.ne')).comp (is_open_map_sub_right _))],
  apply [expr mem_interior.2 ⟨«expr '' »(f, interior s), _, this _ is_open_interior, mem_image_of_mem _ hy⟩],
  refine [expr image_subset_iff.2 (λ z hz, _)],
  exact [expr hs.add_smul_sub_mem hx (interior_subset hz) ⟨ht.1.le, ht.2⟩]
end

/-- If `x ∈ s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
theorem Convex.add_smul_mem_interior {s : Set E} (hs : Convex ℝ s) {x y : E} (hx : x ∈ s) (hy : (x+y) ∈ Interior s)
  {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : (x+t • y) ∈ Interior s :=
  by 
    convert hs.add_smul_sub_mem_interior hx hy ht 
    abel

open AffineMap

-- error in Analysis.Convex.Topology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result contains the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
theorem convex.subset_interior_image_homothety_of_one_lt
{s : set E}
(hs : convex exprℝ() s)
{x : E}
(hx : «expr ∈ »(x, interior s))
(t : exprℝ())
(ht : «expr < »(1, t)) : «expr ⊆ »(s, interior (image (homothety x t) s)) :=
begin
  intros [ident y, ident hy],
  let [ident I] [] [":=", expr {z | «expr∃ , »((u : exprℝ()), «expr ∧ »(«expr ∈ »(u, Ioc (0 : exprℝ()) 1), «expr = »(z, «expr + »(y, «expr • »(u, «expr - »(x, y))))))}],
  have [ident hI] [":", expr «expr ⊆ »(I, interior s)] [],
  { rintros [ident z, "⟨", ident u, ",", ident hu, ",", ident rfl, "⟩"],
    exact [expr hs.add_smul_sub_mem_interior hy hx hu] },
  let [ident z] [] [":=", expr homothety x «expr ⁻¹»(t) y],
  have [ident hz₁] [":", expr «expr ∈ »(z, interior s)] [],
  { suffices [] [":", expr «expr ∈ »(z, I)],
    { exact [expr hI this] },
    use [expr «expr - »(1, «expr ⁻¹»(t))],
    split,
    { simp [] [] ["only"] ["[", expr mem_Ioc, ",", expr sub_le_self_iff, ",", expr inv_nonneg, ",", expr sub_pos, ",", expr inv_lt_one ht, ",", expr true_and, "]"] [] [],
      linarith [] [] [] },
    { simp [] [] ["only"] ["[", expr z, ",", expr homothety_apply, ",", expr sub_smul, ",", expr smul_sub, ",", expr vsub_eq_sub, ",", expr vadd_eq_add, ",", expr one_smul, "]"] [] [],
      abel [] [] [] } },
  have [ident ht'] [":", expr «expr ≠ »(t, 0)] [],
  { linarith [] [] [] },
  have [ident hz₂] [":", expr «expr = »(y, homothety x t z)] [],
  { simp [] [] [] ["[", expr z, ",", expr ht', ",", expr homothety_apply, ",", expr smul_smul, "]"] [] [] },
  rw [expr hz₂] [],
  rw [expr mem_interior] ["at", ident hz₁, "⊢"],
  obtain ["⟨", ident U, ",", ident hU₁, ",", ident hU₂, ",", ident hU₃, "⟩", ":=", expr hz₁],
  exact [expr ⟨image (homothety x t) U, image_subset «expr⇑ »(homothety x t) hU₁, homothety_is_open_map x t ht' U hU₂, mem_image_of_mem «expr⇑ »(homothety x t) hU₃⟩]
end

end HasContinuousSmul

/-! ### Normed vector space -/


section NormedSpace

variable[NormedGroup E][NormedSpace ℝ E]

theorem convex_on_dist (z : E) (s : Set E) (hs : Convex ℝ s) : ConvexOn ℝ s fun z' => dist z' z :=
  And.intro hs$
    fun x y hx hy a b ha hb hab =>
      calc dist ((a • x)+b • y) z = ∥((a • x)+b • y) - (a+b) • z∥ :=
        by 
          rw [hab, one_smul, NormedGroup.dist_eq]
        _ = ∥(a • (x - z))+b • (y - z)∥ :=
        by 
          rw [add_smul, smul_sub, smul_sub, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add, ←add_assocₓ,
              add_assocₓ (a • x), add_commₓ (b • y)] <;>
            simp only [add_assocₓ]
        _ ≤ ∥a • (x - z)∥+∥b • (y - z)∥ := norm_add_le (a • (x - z)) (b • (y - z))
        _ = (a*dist x z)+b*dist y z :=
        by 
          simp [norm_smul, NormedGroup.dist_eq, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
        

theorem convex_ball (a : E) (r : ℝ) : Convex ℝ (Metric.Ball a r) :=
  by 
    simpa only [Metric.Ball, sep_univ] using (convex_on_dist a _ convex_univ).convex_lt r

theorem convex_closed_ball (a : E) (r : ℝ) : Convex ℝ (Metric.ClosedBall a r) :=
  by 
    simpa only [Metric.ClosedBall, sep_univ] using (convex_on_dist a _ convex_univ).convex_le r

/-- Given a point `x` in the convex hull of `s` and a point `y`, there exists a point
of `s` at distance at least `dist x y` from `y`. -/
theorem convex_hull_exists_dist_ge {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) (y : E) :
  ∃ (x' : _)(_ : x' ∈ s), dist x y ≤ dist x' y :=
  (convex_on_dist y _ (convex_convex_hull ℝ _)).exists_ge_of_mem_convex_hull hx

/-- Given a point `x` in the convex hull of `s` and a point `y` in the convex hull of `t`,
there exist points `x' ∈ s` and `y' ∈ t` at distance at least `dist x y`. -/
theorem convex_hull_exists_dist_ge2 {s t : Set E} {x y : E} (hx : x ∈ convexHull ℝ s) (hy : y ∈ convexHull ℝ t) :
  ∃ (x' : _)(_ : x' ∈ s)(y' : _)(_ : y' ∈ t), dist x y ≤ dist x' y' :=
  by 
    rcases convex_hull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩
    rcases convex_hull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩
    use x', hx', y', hy' 
    exact le_transₓ Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')

/-- Emetric diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp]
theorem convex_hull_ediam (s : Set E) : Emetric.diam (convexHull ℝ s) = Emetric.diam s :=
  by 
    refine' (Emetric.diam_le$ fun x hx y hy => _).antisymm (Emetric.diam_mono$ subset_convex_hull ℝ s)
    rcases convex_hull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩
    rw [edist_dist]
    apply le_transₓ (Ennreal.of_real_le_of_real H)
    rw [←edist_dist]
    exact Emetric.edist_le_diam_of_mem hx' hy'

/-- Diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp]
theorem convex_hull_diam (s : Set E) : Metric.diam (convexHull ℝ s) = Metric.diam s :=
  by 
    simp only [Metric.diam, convex_hull_ediam]

/-- Convex hull of `s` is bounded if and only if `s` is bounded. -/
@[simp]
theorem bounded_convex_hull {s : Set E} : Metric.Bounded (convexHull ℝ s) ↔ Metric.Bounded s :=
  by 
    simp only [Metric.bounded_iff_ediam_ne_top, convex_hull_ediam]

-- error in Analysis.Convex.Topology: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem convex.is_path_connected {s : set E} (hconv : convex exprℝ() s) (hne : s.nonempty) : is_path_connected s :=
begin
  refine [expr is_path_connected_iff.mpr ⟨hne, _⟩],
  intros [ident x, ident y, ident x_in, ident y_in],
  let [ident f] [] [":=", expr λ θ : exprℝ(), «expr + »(x, «expr • »(θ, «expr - »(y, x)))],
  have [ident hf] [":", expr continuous f] [],
  by continuity [] [],
  have [ident h₀] [":", expr «expr = »(f 0, x)] [],
  by simp [] [] [] ["[", expr f, "]"] [] [],
  have [ident h₁] [":", expr «expr = »(f 1, y)] [],
  by { dsimp [] ["[", expr f, "]"] [] [],
    rw [expr one_smul] [],
    abel [] [] [] },
  have [ident H] [] [":=", expr hconv.segment_subset x_in y_in],
  rw [expr segment_eq_image'] ["at", ident H],
  exact [expr joined_in.of_line hf.continuous_on h₀ h₁ H]
end

instance (priority := 100)NormedSpace.path_connected : PathConnectedSpace E :=
  path_connected_space_iff_univ.mpr$ convex_univ.IsPathConnected ⟨(0 : E), trivialₓ⟩

instance (priority := 100)NormedSpace.loc_path_connected : LocPathConnectedSpace E :=
  loc_path_connected_of_bases (fun x => Metric.nhds_basis_ball)
    fun x r r_pos =>
      (convex_ball x r).IsPathConnected$
        by 
          simp [r_pos]

end NormedSpace

