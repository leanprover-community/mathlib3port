import Mathbin.Topology.MetricSpace.Gluing 
import Mathbin.Topology.MetricSpace.HausdorffDistance 
import Mathbin.Topology.ContinuousFunction.Bounded

/-!
# The Gromov-Hausdorff distance is realized

In this file, we construct of a good coupling between nonempty compact metric spaces, minimizing
their Hausdorff distance. This construction is instrumental to study the Gromov-Hausdorff
distance between nonempty compact metric spaces.

Given two nonempty compact metric spaces `X` and `Y`, we define `optimal_GH_coupling X Y` as a
compact metric space, together with two isometric embeddings `optimal_GH_injl` and `optimal_GH_injr`
respectively of `X` and `Y` into `optimal_GH_coupling X Y`. The main property of the optimal
coupling is that the Hausdorff distance between `X` and `Y` in `optimal_GH_coupling X Y` is smaller
than the corresponding distance in any other coupling. We do not prove completely this fact in this
file, but we show a good enough approximation of this fact in `Hausdorff_dist_optimal_le_HD`, that
will suffice to obtain the full statement once the Gromov-Hausdorff distance is properly defined,
in `Hausdorff_dist_optimal`.

The key point in the construction is that the set of possible distances coming from isometric
embeddings of `X` and `Y` in metric spaces is a set of equicontinuous functions. By Arzela-Ascoli,
it is compact, and one can find such a distance which is minimal. This distance defines a premetric
space structure on `X ⊕ Y`. The corresponding metric quotient is `optimal_GH_coupling X Y`.
-/


noncomputable theory

open_locale Classical TopologicalSpace Nnreal

universe u v w

open Classical Set Function TopologicalSpace Filter Metric Quotientₓ

open BoundedContinuousFunction

open sum(inl inr)

attribute [local instance] metric_space_sum

namespace GromovHausdorff

section GromovHausdorffRealized

section Definitions

variable(X : Type u)(Y : Type v)[MetricSpace X][CompactSpace X][Nonempty X][MetricSpace Y][CompactSpace Y][Nonempty Y]

@[reducible]
private def prod_space_fun : Type _ :=
  Sum X Y × Sum X Y → ℝ

@[reducible]
private def Cb : Type _ :=
  BoundedContinuousFunction (Sum X Y × Sum X Y) ℝ

private def max_var :  ℝ≥0  :=
  ((2*⟨diam (univ : Set X), diam_nonneg⟩)+1)+2*⟨diam (univ : Set Y), diam_nonneg⟩

private theorem one_le_max_var : 1 ≤ max_var X Y :=
  calc (1 : Real) = ((2*0)+1)+2*0 :=
    by 
      simp 
    _ ≤ ((2*diam (univ : Set X))+1)+2*diam (univ : Set Y) :=
    by 
      applyRules [add_le_add, mul_le_mul_of_nonneg_left, diam_nonneg] <;> normNum
    

/-- The set of functions on `X ⊕ Y` that are candidates distances to realize the
minimum of the Hausdorff distances between `X` and `Y` in a coupling -/
def candidates : Set (prod_space_fun X Y) :=
  { f |
    (((((∀ x y : X, f (Sum.inl x, Sum.inl y) = dist x y) ∧ ∀ x y : Y, f (Sum.inr x, Sum.inr y) = dist x y) ∧
            ∀ x y, f (x, y) = f (y, x)) ∧
          ∀ x y z, f (x, z) ≤ f (x, y)+f (y, z)) ∧
        ∀ x, f (x, x) = 0) ∧
      ∀ x y, f (x, y) ≤ max_var X Y }

/-- Version of the set of candidates in bounded_continuous_functions, to apply
Arzela-Ascoli -/
private def candidates_b : Set (Cb X Y) :=
  { f:Cb X Y | (f : _ → ℝ) ∈ candidates X Y }

end Definitions

section Constructions

variable{X :
    Type
      u}{Y :
    Type
      v}[MetricSpace
      X][CompactSpace
      X][Nonempty X][MetricSpace Y][CompactSpace Y][Nonempty Y]{f : prod_space_fun X Y}{x y z t : Sum X Y}

attribute [local instance] inhabited_of_nonempty'

private theorem max_var_bound : dist x y ≤ max_var X Y :=
  calc dist x y ≤ diam (univ : Set (Sum X Y)) := dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
    _ = diam (inl '' (univ : Set X) ∪ inr '' (univ : Set Y)) :=
    by 
      apply congr_argₓ <;> ext x y z <;> cases x <;> simp [mem_univ, mem_range_self]
    _ ≤ (diam (inl '' (univ : Set X))+dist (inl (default X)) (inr (default Y)))+diam (inr '' (univ : Set Y)) :=
    diam_union (mem_image_of_mem _ (mem_univ _)) (mem_image_of_mem _ (mem_univ _))
    _ = (diam (univ : Set X)+(dist (default X) (default X)+1)+dist (default Y) (default Y))+diam (univ : Set Y) :=
    by 
      rw [isometry_on_inl.diam_image, isometry_on_inr.diam_image]
      rfl 
    _ = ((1*diam (univ : Set X))+1)+1*diam (univ : Set Y) :=
    by 
      simp 
    _ ≤ ((2*diam (univ : Set X))+1)+2*diam (univ : Set Y) :=
    by 
      applyRules [add_le_add, mul_le_mul_of_nonneg_right, diam_nonneg, le_reflₓ]
      normNum 
      normNum
    

private theorem candidates_symm (fA : f ∈ candidates X Y) : f (x, y) = f (y, x) :=
  fA.1.1.1.2 x y

private theorem candidates_triangle (fA : f ∈ candidates X Y) : f (x, z) ≤ f (x, y)+f (y, z) :=
  fA.1.1.2 x y z

private theorem candidates_refl (fA : f ∈ candidates X Y) : f (x, x) = 0 :=
  fA.1.2 x

-- error in Topology.MetricSpace.GromovHausdorffRealized: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private theorem candidates_nonneg (fA : «expr ∈ »(f, candidates X Y)) : «expr ≤ »(0, f (x, y)) :=
begin
  have [] [":", expr «expr ≤ »(0, «expr * »(2, f (x, y)))] [":=", expr calc
     «expr = »(0, f (x, x)) : (candidates_refl fA).symm
     «expr ≤ »(..., «expr + »(f (x, y), f (y, x))) : candidates_triangle fA
     «expr = »(..., «expr + »(f (x, y), f (x, y))) : by rw ["[", expr candidates_symm fA, "]"] []
     «expr = »(..., «expr * »(2, f (x, y))) : by ring []],
  by linarith [] [] []
end

private theorem candidates_dist_inl (fA : f ∈ candidates X Y) (x y : X) : f (inl x, inl y) = dist x y :=
  fA.1.1.1.1.1 x y

private theorem candidates_dist_inr (fA : f ∈ candidates X Y) (x y : Y) : f (inr x, inr y) = dist x y :=
  fA.1.1.1.1.2 x y

private theorem candidates_le_max_var (fA : f ∈ candidates X Y) : f (x, y) ≤ max_var X Y :=
  fA.2 x y

/-- candidates are bounded by `max_var X Y` -/
private theorem candidates_dist_bound (fA : f ∈ candidates X Y) : ∀ {x y : Sum X Y}, f (x, y) ≤ max_var X Y*dist x y
| inl x, inl y =>
  calc f (inl x, inl y) = dist x y := candidates_dist_inl fA x y 
    _ = dist (inl x) (inl y) :=
    by 
      rw [@sum.dist_eq X Y]
      rfl 
    _ = 1*dist (inl x) (inl y) :=
    by 
      simp 
    _ ≤ max_var X Y*dist (inl x) (inl y) := mul_le_mul_of_nonneg_right (one_le_max_var X Y) dist_nonneg
    
| inl x, inr y =>
  calc f (inl x, inr y) ≤ max_var X Y := candidates_le_max_var fA 
    _ = max_var X Y*1 :=
    by 
      simp 
    _ ≤ max_var X Y*dist (inl x) (inr y) :=
    mul_le_mul_of_nonneg_left sum.one_dist_le (le_transₓ zero_le_one (one_le_max_var X Y))
    
| inr x, inl y =>
  calc f (inr x, inl y) ≤ max_var X Y := candidates_le_max_var fA 
    _ = max_var X Y*1 :=
    by 
      simp 
    _ ≤ max_var X Y*dist (inl x) (inr y) :=
    mul_le_mul_of_nonneg_left sum.one_dist_le (le_transₓ zero_le_one (one_le_max_var X Y))
    
| inr x, inr y =>
  calc f (inr x, inr y) = dist x y := candidates_dist_inr fA x y 
    _ = dist (inr x) (inr y) :=
    by 
      rw [@sum.dist_eq X Y]
      rfl 
    _ = 1*dist (inr x) (inr y) :=
    by 
      simp 
    _ ≤ max_var X Y*dist (inr x) (inr y) := mul_le_mul_of_nonneg_right (one_le_max_var X Y) dist_nonneg
    

/-- Technical lemma to prove that candidates are Lipschitz -/
private theorem candidates_lipschitz_aux (fA : f ∈ candidates X Y) :
  f (x, y) - f (z, t) ≤ (2*max_var X Y)*dist (x, y) (z, t) :=
  calc f (x, y) - f (z, t) ≤ (f (x, t)+f (t, y)) - f (z, t) := sub_le_sub_right (candidates_triangle fA) _ 
    _ ≤ ((f (x, z)+f (z, t))+f (t, y)) - f (z, t) := sub_le_sub_right (add_le_add_right (candidates_triangle fA) _) _ 
    _ = f (x, z)+f (t, y) :=
    by 
      simp [sub_eq_add_neg, add_assocₓ]
    _ ≤ (max_var X Y*dist x z)+max_var X Y*dist t y := add_le_add (candidates_dist_bound fA) (candidates_dist_bound fA)
    _ ≤ (max_var X Y*max (dist x z) (dist t y))+max_var X Y*max (dist x z) (dist t y) :=
    by 
      apply add_le_add 
      apply mul_le_mul_of_nonneg_left (le_max_leftₓ (dist x z) (dist t y)) (zero_le_one.trans (one_le_max_var X Y))
      apply mul_le_mul_of_nonneg_left (le_max_rightₓ (dist x z) (dist t y)) (zero_le_one.trans (one_le_max_var X Y))
    _ = (2*max_var X Y)*max (dist x z) (dist y t) :=
    by 
      simp [dist_comm]
      ring 
    _ = (2*max_var X Y)*dist (x, y) (z, t) :=
    by 
      rfl
    

/-- Candidates are Lipschitz -/
private theorem candidates_lipschitz (fA : f ∈ candidates X Y) : LipschitzWith (2*max_var X Y) f :=
  by 
    apply LipschitzWith.of_dist_le_mul 
    rintro ⟨x, y⟩ ⟨z, t⟩
    rw [Real.dist_eq, abs_sub_le_iff]
    use candidates_lipschitz_aux fA 
    rw [dist_comm]
    exact candidates_lipschitz_aux fA

/-- candidates give rise to elements of bounded_continuous_functions -/
def candidates_b_of_candidates (f : prod_space_fun X Y) (fA : f ∈ candidates X Y) : Cb X Y :=
  BoundedContinuousFunction.mkOfCompact ⟨f, (candidates_lipschitz fA).Continuous⟩

theorem candidates_b_of_candidates_mem (f : prod_space_fun X Y) (fA : f ∈ candidates X Y) :
  candidates_b_of_candidates f fA ∈ candidates_b X Y :=
  fA

/-- The distance on `X ⊕ Y` is a candidate -/
private theorem dist_mem_candidates : (fun p : Sum X Y × Sum X Y => dist p.1 p.2) ∈ candidates X Y :=
  by 
    simp only [candidates, dist_comm, forall_const, and_trueₓ, add_commₓ, eq_self_iff_true, and_selfₓ, Sum.forall,
      Set.mem_set_of_eq, dist_self]
    repeat' 
      first |
        split |
        exact fun a y z => dist_triangle_left _ _ _|
        exact
          fun x y =>
            by 
              rfl|
        exact fun x y => max_var_bound

/-- The distance on `X ⊕ Y` as a candidate -/
def candidates_b_dist (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Inhabited X] [MetricSpace Y]
  [CompactSpace Y] [Inhabited Y] : Cb X Y :=
  candidates_b_of_candidates _ dist_mem_candidates

theorem candidates_b_dist_mem_candidates_b : candidates_b_dist X Y ∈ candidates_b X Y :=
  candidates_b_of_candidates_mem _ _

private theorem candidates_b_nonempty : (candidates_b X Y).Nonempty :=
  ⟨_, candidates_b_dist_mem_candidates_b⟩

-- error in Topology.MetricSpace.GromovHausdorffRealized: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- To apply Arzela-Ascoli, we need to check that the set of candidates is closed and
equicontinuous. Equicontinuity follows from the Lipschitz control, we check closedness. -/
private
theorem closed_candidates_b : is_closed (candidates_b X Y) :=
begin
  have [ident I1] [":", expr ∀
   x
   y, is_closed {f : Cb X Y | «expr = »(f (inl x, inl y), dist x y)}] [":=", expr λ
   x y, is_closed_eq continuous_evalx continuous_const],
  have [ident I2] [":", expr ∀
   x
   y, is_closed {f : Cb X Y | «expr = »(f (inr x, inr y), dist x y)}] [":=", expr λ
   x y, is_closed_eq continuous_evalx continuous_const],
  have [ident I3] [":", expr ∀
   x
   y, is_closed {f : Cb X Y | «expr = »(f (x, y), f (y, x))}] [":=", expr λ
   x y, is_closed_eq continuous_evalx continuous_evalx],
  have [ident I4] [":", expr ∀
   x
   y
   z, is_closed {f : Cb X Y | «expr ≤ »(f (x, z), «expr + »(f (x, y), f (y, z)))}] [":=", expr λ
   x y z, is_closed_le continuous_evalx (continuous_evalx.add continuous_evalx)],
  have [ident I5] [":", expr ∀
   x, is_closed {f : Cb X Y | «expr = »(f (x, x), 0)}] [":=", expr λ x, is_closed_eq continuous_evalx continuous_const],
  have [ident I6] [":", expr ∀
   x
   y, is_closed {f : Cb X Y | «expr ≤ »(f (x, y), max_var X Y)}] [":=", expr λ
   x y, is_closed_le continuous_evalx continuous_const],
  have [] [":", expr «expr = »(candidates_b X Y, «expr ∩ »(«expr ∩ »(«expr ∩ »(«expr ∩ »(«expr ∩ »(«expr⋂ , »((x
           y), {f : Cb X Y | «expr = »(f (@inl X Y x, @inl X Y y), dist x y)}), «expr⋂ , »((x
           y), {f : Cb X Y | «expr = »(f (@inr X Y x, @inr X Y y), dist x y)})), «expr⋂ , »((x
          y), {f : Cb X Y | «expr = »(f (x, y), f (y, x))})), «expr⋂ , »((x
         y
         z), {f : Cb X Y | «expr ≤ »(f (x, z), «expr + »(f (x, y), f (y, z)))})), «expr⋂ , »((x), {f : Cb X Y | «expr = »(f (x, x), 0)})), «expr⋂ , »((x
       y), {f : Cb X Y | «expr ≤ »(f (x, y), max_var X Y)})))] [],
  { ext [] [] [],
    simp [] [] ["only"] ["[", expr candidates_b, ",", expr candidates, ",", expr mem_inter_eq, ",", expr mem_Inter, ",", expr mem_set_of_eq, "]"] [] [] },
  rw [expr this] [],
  repeat { apply [expr is_closed.inter _ _] <|> apply [expr is_closed_Inter _] <|> apply [expr I1 _ _] <|> apply [expr I2 _ _] <|> apply [expr I3 _ _] <|> apply [expr I4 _ _ _] <|> apply [expr I5 _] <|> apply [expr I6 _ _] <|> assume [binders
     (x)] }
end

-- error in Topology.MetricSpace.GromovHausdorffRealized: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Compactness of candidates (in bounded_continuous_functions) follows. -/
private
theorem compact_candidates_b : is_compact (candidates_b X Y) :=
begin
  refine [expr arzela_ascoli₂ (Icc 0 (max_var X Y)) is_compact_Icc (candidates_b X Y) closed_candidates_b _ _],
  { rintros [ident f, "⟨", ident x1, ",", ident x2, "⟩", ident hf],
    simp [] [] ["only"] ["[", expr set.mem_Icc, "]"] [] [],
    exact [expr ⟨candidates_nonneg hf, candidates_le_max_var hf⟩] },
  { refine [expr equicontinuous_of_continuity_modulus (λ t, «expr * »(«expr * »(2, max_var X Y), t)) _ _ _],
    { have [] [":", expr tendsto (λ
        t : exprℝ(), «expr * »(«expr * »(2, (max_var X Y : exprℝ())), t)) (expr𝓝() 0) (expr𝓝() «expr * »(«expr * »(2, max_var X Y), 0))] [":=", expr tendsto_const_nhds.mul tendsto_id],
      simpa [] [] [] [] [] ["using", expr this] },
    { assume [binders (x y f hf)],
      exact [expr (candidates_lipschitz hf).dist_le_mul _ _] } }
end

/-- We will then choose the candidate minimizing the Hausdorff distance. Except that we are not
in a metric space setting, so we need to define our custom version of Hausdorff distance,
called HD, and prove its basic properties. -/
def HD (f : Cb X Y) :=
  max (⨆x, ⨅y, f (inl x, inr y)) (⨆y, ⨅x, f (inl x, inr y))

theorem HD_below_aux1 {f : Cb X Y} (C : ℝ) {x : X} : BddBelow (range fun y : Y => f (inl x, inr y)+C) :=
  let ⟨cf, hcf⟩ := (Real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1
  ⟨cf+C, forall_range_iff.2 fun i => add_le_add_right ((fun x => hcf (mem_range_self x)) _) _⟩

private theorem HD_bound_aux1 (f : Cb X Y) (C : ℝ) : BddAbove (range fun x : X => ⨅y, f (inl x, inr y)+C) :=
  by 
    rcases(Real.bounded_iff_bdd_below_bdd_above.1 bounded_range).2 with ⟨Cf, hCf⟩
    refine' ⟨Cf+C, forall_range_iff.2 fun x => _⟩
    calc (⨅y, f (inl x, inr y)+C) ≤ f (inl x, inr (default Y))+C := cinfi_le (HD_below_aux1 C) (default Y)_ ≤ Cf+C :=
      add_le_add ((fun x => hCf (mem_range_self x)) _) (le_reflₓ _)

theorem HD_below_aux2 {f : Cb X Y} (C : ℝ) {y : Y} : BddBelow (range fun x : X => f (inl x, inr y)+C) :=
  let ⟨cf, hcf⟩ := (Real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1
  ⟨cf+C, forall_range_iff.2 fun i => add_le_add_right ((fun x => hcf (mem_range_self x)) _) _⟩

private theorem HD_bound_aux2 (f : Cb X Y) (C : ℝ) : BddAbove (range fun y : Y => ⨅x, f (inl x, inr y)+C) :=
  by 
    rcases(Real.bounded_iff_bdd_below_bdd_above.1 bounded_range).2 with ⟨Cf, hCf⟩
    refine' ⟨Cf+C, forall_range_iff.2 fun y => _⟩
    calc (⨅x, f (inl x, inr y)+C) ≤ f (inl (default X), inr y)+C := cinfi_le (HD_below_aux2 C) (default X)_ ≤ Cf+C :=
      add_le_add ((fun x => hCf (mem_range_self x)) _) (le_reflₓ _)

-- error in Topology.MetricSpace.GromovHausdorffRealized: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Explicit bound on `HD (dist)`. This means that when looking for minimizers it will
be sufficient to look for functions with `HD(f)` bounded by this bound. -/
theorem HD_candidates_b_dist_le : «expr ≤ »(HD (candidates_b_dist X Y), «expr + »(«expr + »(diam (univ : set X), 1), diam (univ : set Y))) :=
begin
  refine [expr max_le (csupr_le (λ x, _)) (csupr_le (λ y, _))],
  { have [ident A] [":", expr «expr ≤ »(«expr⨅ , »((y), candidates_b_dist X Y (inl x, inr y)), candidates_b_dist X Y (inl x, inr (default Y)))] [":=", expr cinfi_le (by simpa [] [] [] [] [] ["using", expr HD_below_aux1 0]) (default Y)],
    have [ident B] [":", expr «expr ≤ »(dist (inl x) (inr (default Y)), «expr + »(«expr + »(diam (univ : set X), 1), diam (univ : set Y)))] [":=", expr calc
       «expr = »(dist (inl x) (inr (default Y)), «expr + »(«expr + »(dist x (default X), 1), dist (default Y) (default Y))) : rfl
       «expr ≤ »(..., «expr + »(«expr + »(diam (univ : set X), 1), diam (univ : set Y))) : begin
         apply [expr add_le_add (add_le_add _ (le_refl _))],
         exact [expr dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)],
         any_goals { exact [expr ordered_add_comm_monoid.to_covariant_class_left exprℝ()] },
         any_goals { exact [expr ordered_add_comm_monoid.to_covariant_class_right exprℝ()] },
         exact [expr dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)]
       end],
    exact [expr le_trans A B] },
  { have [ident A] [":", expr «expr ≤ »(«expr⨅ , »((x), candidates_b_dist X Y (inl x, inr y)), candidates_b_dist X Y (inl (default X), inr y))] [":=", expr cinfi_le (by simpa [] [] [] [] [] ["using", expr HD_below_aux2 0]) (default X)],
    have [ident B] [":", expr «expr ≤ »(dist (inl (default X)) (inr y), «expr + »(«expr + »(diam (univ : set X), 1), diam (univ : set Y)))] [":=", expr calc
       «expr = »(dist (inl (default X)) (inr y), «expr + »(«expr + »(dist (default X) (default X), 1), dist (default Y) y)) : rfl
       «expr ≤ »(..., «expr + »(«expr + »(diam (univ : set X), 1), diam (univ : set Y))) : begin
         apply [expr add_le_add (add_le_add _ (le_refl _))],
         exact [expr dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)],
         any_goals { exact [expr ordered_add_comm_monoid.to_covariant_class_left exprℝ()] },
         any_goals { exact [expr ordered_add_comm_monoid.to_covariant_class_right exprℝ()] },
         exact [expr dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)]
       end],
    exact [expr le_trans A B] }
end

-- error in Topology.MetricSpace.GromovHausdorffRealized: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem HD_lipschitz_aux1
(f
 g : Cb X Y) : «expr ≤ »(«expr⨆ , »((x), «expr⨅ , »((y), f (inl x, inr y))), «expr + »(«expr⨆ , »((x), «expr⨅ , »((y), g (inl x, inr y))), dist f g)) :=
begin
  rcases [expr (real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1, "with", "⟨", ident cg, ",", ident hcg, "⟩"],
  have [ident Hcg] [":", expr ∀ x, «expr ≤ »(cg, g x)] [":=", expr λ x, hcg (mem_range_self x)],
  rcases [expr (real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1, "with", "⟨", ident cf, ",", ident hcf, "⟩"],
  have [ident Hcf] [":", expr ∀ x, «expr ≤ »(cf, f x)] [":=", expr λ x, hcf (mem_range_self x)],
  have [ident Z] [":", expr «expr ≤ »(«expr⨆ , »((x), «expr⨅ , »((y), f (inl x, inr y))), «expr⨆ , »((x), «expr⨅ , »((y), «expr + »(g (inl x, inr y), dist f g))))] [":=", expr csupr_le_csupr (HD_bound_aux1 _ (dist f g)) (λ
    x, cinfi_le_cinfi ⟨cf, forall_range_iff.2 (λ i, Hcf _)⟩ (λ y, coe_le_coe_add_dist))],
  have [ident E1] [":", expr ∀
   x, «expr = »(«expr + »(«expr⨅ , »((y), g (inl x, inr y)), dist f g), «expr⨅ , »((y), «expr + »(g (inl x, inr y), dist f g)))] [],
  { assume [binders (x)],
    refine [expr map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ _],
    { assume [binders (x y hx)],
      simpa [] [] [] [] [] [] },
    { show [expr bdd_below (range (λ y : Y, g (inl x, inr y)))],
      from [expr ⟨cg, forall_range_iff.2 (λ i, Hcg _)⟩] } },
  have [ident E2] [":", expr «expr = »(«expr + »(«expr⨆ , »((x), «expr⨅ , »((y), g (inl x, inr y))), dist f g), «expr⨆ , »((x), «expr + »(«expr⨅ , »((y), g (inl x, inr y)), dist f g)))] [],
  { refine [expr map_csupr_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ _],
    { assume [binders (x y hx)],
      simpa [] [] [] [] [] [] },
    { by simpa [] [] [] [] [] ["using", expr HD_bound_aux1 _ 0] } },
  simpa [] [] [] ["[", expr E2, ",", expr E1, ",", expr function.comp, "]"] [] []
end

-- error in Topology.MetricSpace.GromovHausdorffRealized: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem HD_lipschitz_aux2
(f
 g : Cb X Y) : «expr ≤ »(«expr⨆ , »((y), «expr⨅ , »((x), f (inl x, inr y))), «expr + »(«expr⨆ , »((y), «expr⨅ , »((x), g (inl x, inr y))), dist f g)) :=
begin
  rcases [expr (real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1, "with", "⟨", ident cg, ",", ident hcg, "⟩"],
  have [ident Hcg] [":", expr ∀ x, «expr ≤ »(cg, g x)] [":=", expr λ x, hcg (mem_range_self x)],
  rcases [expr (real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1, "with", "⟨", ident cf, ",", ident hcf, "⟩"],
  have [ident Hcf] [":", expr ∀ x, «expr ≤ »(cf, f x)] [":=", expr λ x, hcf (mem_range_self x)],
  have [ident Z] [":", expr «expr ≤ »(«expr⨆ , »((y), «expr⨅ , »((x), f (inl x, inr y))), «expr⨆ , »((y), «expr⨅ , »((x), «expr + »(g (inl x, inr y), dist f g))))] [":=", expr csupr_le_csupr (HD_bound_aux2 _ (dist f g)) (λ
    y, cinfi_le_cinfi ⟨cf, forall_range_iff.2 (λ i, Hcf _)⟩ (λ y, coe_le_coe_add_dist))],
  have [ident E1] [":", expr ∀
   y, «expr = »(«expr + »(«expr⨅ , »((x), g (inl x, inr y)), dist f g), «expr⨅ , »((x), «expr + »(g (inl x, inr y), dist f g)))] [],
  { assume [binders (y)],
    refine [expr map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ _],
    { assume [binders (x y hx)],
      simpa [] [] [] [] [] [] },
    { show [expr bdd_below (range (λ x : X, g (inl x, inr y)))],
      from [expr ⟨cg, forall_range_iff.2 (λ i, Hcg _)⟩] } },
  have [ident E2] [":", expr «expr = »(«expr + »(«expr⨆ , »((y), «expr⨅ , »((x), g (inl x, inr y))), dist f g), «expr⨆ , »((y), «expr + »(«expr⨅ , »((x), g (inl x, inr y)), dist f g)))] [],
  { refine [expr map_csupr_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ _],
    { assume [binders (x y hx)],
      simpa [] [] [] [] [] [] },
    { by simpa [] [] [] [] [] ["using", expr HD_bound_aux2 _ 0] } },
  simpa [] [] [] ["[", expr E2, ",", expr E1, "]"] [] []
end

private theorem HD_lipschitz_aux3 (f g : Cb X Y) : HD f ≤ HD g+dist f g :=
  max_leₓ (le_transₓ (HD_lipschitz_aux1 f g) (add_le_add_right (le_max_leftₓ _ _) _))
    (le_transₓ (HD_lipschitz_aux2 f g) (add_le_add_right (le_max_rightₓ _ _) _))

/-- Conclude that HD, being Lipschitz, is continuous -/
private theorem HD_continuous : Continuous (HD : Cb X Y → ℝ) :=
  LipschitzWith.continuous (LipschitzWith.of_le_add HD_lipschitz_aux3)

end Constructions

section Consequences

variable(X : Type u)(Y : Type v)[MetricSpace X][CompactSpace X][Nonempty X][MetricSpace Y][CompactSpace Y][Nonempty Y]

private theorem exists_minimizer : ∃ (f : _)(_ : f ∈ candidates_b X Y), ∀ g _ : g ∈ candidates_b X Y, HD f ≤ HD g :=
  compact_candidates_b.exists_forall_le candidates_b_nonempty HD_continuous.ContinuousOn

private def optimal_GH_dist : Cb X Y :=
  Classical.some (exists_minimizer X Y)

private theorem optimal_GH_dist_mem_candidates_b : optimal_GH_dist X Y ∈ candidates_b X Y :=
  by 
    cases Classical.some_spec (exists_minimizer X Y) <;> assumption

private theorem HD_optimal_GH_dist_le (g : Cb X Y) (hg : g ∈ candidates_b X Y) : HD (optimal_GH_dist X Y) ≤ HD g :=
  let ⟨Z1, Z2⟩ := Classical.some_spec (exists_minimizer X Y)
  Z2 g hg

/-- With the optimal candidate, construct a premetric space structure on `X ⊕ Y`, on which the
predistance is given by the candidate. Then, we will identify points at `0` predistance
to obtain a genuine metric space -/
def premetric_optimal_GH_dist : PseudoMetricSpace (Sum X Y) :=
  { dist := fun p q => optimal_GH_dist X Y (p, q),
    dist_self := fun x => candidates_refl (optimal_GH_dist_mem_candidates_b X Y),
    dist_comm := fun x y => candidates_symm (optimal_GH_dist_mem_candidates_b X Y),
    dist_triangle := fun x y z => candidates_triangle (optimal_GH_dist_mem_candidates_b X Y) }

attribute [local instance] premetric_optimal_GH_dist PseudoMetric.distSetoid

-- error in Topology.MetricSpace.GromovHausdorffRealized: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler metric_space
/-- A metric space which realizes the optimal coupling between `X` and `Y` -/
@[derive #[expr metric_space], nolint #[ident has_inhabited_instance]]
def optimal_GH_coupling : Type* :=
pseudo_metric_quot «expr ⊕ »(X, Y)

/-- Injection of `X` in the optimal coupling between `X` and `Y` -/
def optimal_GH_injl (x : X) : optimal_GH_coupling X Y :=
  «expr⟦ ⟧» (inl x)

/-- The injection of `X` in the optimal coupling between `X` and `Y` is an isometry. -/
theorem isometry_optimal_GH_injl : Isometry (optimal_GH_injl X Y) :=
  by 
    refine' isometry_emetric_iff_metric.2 fun x y => _ 
    change dist («expr⟦ ⟧» (inl x)) («expr⟦ ⟧» (inl y)) = dist x y 
    exact candidates_dist_inl (optimal_GH_dist_mem_candidates_b X Y) _ _

/-- Injection of `Y` in the optimal coupling between `X` and `Y` -/
def optimal_GH_injr (y : Y) : optimal_GH_coupling X Y :=
  «expr⟦ ⟧» (inr y)

/-- The injection of `Y` in the optimal coupling between `X` and `Y` is an isometry. -/
theorem isometry_optimal_GH_injr : Isometry (optimal_GH_injr X Y) :=
  by 
    refine' isometry_emetric_iff_metric.2 fun x y => _ 
    change dist («expr⟦ ⟧» (inr x)) («expr⟦ ⟧» (inr y)) = dist x y 
    exact candidates_dist_inr (optimal_GH_dist_mem_candidates_b X Y) _ _

-- error in Topology.MetricSpace.GromovHausdorffRealized: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The optimal coupling between two compact spaces `X` and `Y` is still a compact space -/
instance compact_space_optimal_GH_coupling : compact_space (optimal_GH_coupling X Y) :=
⟨begin
   have [] [":", expr «expr = »((univ : set (optimal_GH_coupling X Y)), «expr ∪ »(«expr '' »(optimal_GH_injl X Y, univ), «expr '' »(optimal_GH_injr X Y, univ)))] [],
   { refine [expr subset.antisymm (λ xc hxc, _) (subset_univ _)],
     rcases [expr quotient.exists_rep xc, "with", "⟨", ident x, ",", ident hx, "⟩"],
     cases [expr x] []; rw ["<-", expr hx] [],
     { have [] [":", expr «expr = »(«expr⟦ ⟧»(inl x), optimal_GH_injl X Y x)] [":=", expr rfl],
       rw [expr this] [],
       exact [expr mem_union_left _ (mem_image_of_mem _ (mem_univ _))] },
     { have [] [":", expr «expr = »(«expr⟦ ⟧»(inr x), optimal_GH_injr X Y x)] [":=", expr rfl],
       rw [expr this] [],
       exact [expr mem_union_right _ (mem_image_of_mem _ (mem_univ _))] } },
   rw [expr this] [],
   exact [expr (compact_univ.image (isometry_optimal_GH_injl X Y).continuous).union (compact_univ.image (isometry_optimal_GH_injr X Y).continuous)]
 end⟩

-- error in Topology.MetricSpace.GromovHausdorffRealized: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For any candidate `f`, `HD(f)` is larger than or equal to the Hausdorff distance in the
optimal coupling. This follows from the fact that HD of the optimal candidate is exactly
the Hausdorff distance in the optimal coupling, although we only prove here the inequality
we need. -/
theorem Hausdorff_dist_optimal_le_HD
{f}
(h : «expr ∈ »(f, candidates_b X Y)) : «expr ≤ »(Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)), HD f) :=
begin
  refine [expr le_trans (le_of_forall_le_of_dense (λ r hr, _)) (HD_optimal_GH_dist_le X Y f h)],
  have [ident A] [":", expr ∀
   x «expr ∈ » range (optimal_GH_injl X Y), «expr∃ , »((y «expr ∈ » range (optimal_GH_injr X Y)), «expr ≤ »(dist x y, r))] [],
  { assume [binders (x hx)],
    rcases [expr mem_range.1 hx, "with", "⟨", ident z, ",", ident hz, "⟩"],
    rw ["<-", expr hz] [],
    have [ident I1] [":", expr «expr < »(«expr⨆ , »((x), «expr⨅ , »((y), optimal_GH_dist X Y (inl x, inr y))), r)] [":=", expr lt_of_le_of_lt (le_max_left _ _) hr],
    have [ident I2] [":", expr «expr ≤ »(«expr⨅ , »((y), optimal_GH_dist X Y (inl z, inr y)), «expr⨆ , »((x), «expr⨅ , »((y), optimal_GH_dist X Y (inl x, inr y))))] [":=", expr le_cSup (by simpa [] [] [] [] [] ["using", expr HD_bound_aux1 _ 0]) (mem_range_self _)],
    have [ident I] [":", expr «expr < »(«expr⨅ , »((y), optimal_GH_dist X Y (inl z, inr y)), r)] [":=", expr lt_of_le_of_lt I2 I1],
    rcases [expr exists_lt_of_cInf_lt (range_nonempty _) I, "with", "⟨", ident r', ",", ident r'range, ",", ident hr', "⟩"],
    rcases [expr mem_range.1 r'range, "with", "⟨", ident z', ",", ident hz', "⟩"],
    existsi ["[", expr optimal_GH_injr X Y z', ",", expr mem_range_self _, "]"],
    have [] [":", expr «expr ≤ »(optimal_GH_dist X Y (inl z, inr z'), r)] [],
    by { rw [expr hz'] [],
      exact [expr le_of_lt hr'] },
    exact [expr this] },
  refine [expr Hausdorff_dist_le_of_mem_dist _ A _],
  { rcases [expr exists_mem_of_nonempty X, "with", "⟨", ident xX, ",", "_", "⟩"],
    have [] [":", expr «expr ∈ »(optimal_GH_injl X Y xX, range (optimal_GH_injl X Y))] [":=", expr mem_range_self _],
    rcases [expr A _ this, "with", "⟨", ident y, ",", ident yrange, ",", ident hy, "⟩"],
    exact [expr le_trans dist_nonneg hy] },
  { assume [binders (y hy)],
    rcases [expr mem_range.1 hy, "with", "⟨", ident z, ",", ident hz, "⟩"],
    rw ["<-", expr hz] [],
    have [ident I1] [":", expr «expr < »(«expr⨆ , »((y), «expr⨅ , »((x), optimal_GH_dist X Y (inl x, inr y))), r)] [":=", expr lt_of_le_of_lt (le_max_right _ _) hr],
    have [ident I2] [":", expr «expr ≤ »(«expr⨅ , »((x), optimal_GH_dist X Y (inl x, inr z)), «expr⨆ , »((y), «expr⨅ , »((x), optimal_GH_dist X Y (inl x, inr y))))] [":=", expr le_cSup (by simpa [] [] [] [] [] ["using", expr HD_bound_aux2 _ 0]) (mem_range_self _)],
    have [ident I] [":", expr «expr < »(«expr⨅ , »((x), optimal_GH_dist X Y (inl x, inr z)), r)] [":=", expr lt_of_le_of_lt I2 I1],
    rcases [expr exists_lt_of_cInf_lt (range_nonempty _) I, "with", "⟨", ident r', ",", ident r'range, ",", ident hr', "⟩"],
    rcases [expr mem_range.1 r'range, "with", "⟨", ident z', ",", ident hz', "⟩"],
    existsi ["[", expr optimal_GH_injl X Y z', ",", expr mem_range_self _, "]"],
    have [] [":", expr «expr ≤ »(optimal_GH_dist X Y (inl z', inr z), r)] [],
    by { rw [expr hz'] [],
      exact [expr le_of_lt hr'] },
    rw [expr dist_comm] [],
    exact [expr this] }
end

end Consequences

end GromovHausdorffRealized

end GromovHausdorff

