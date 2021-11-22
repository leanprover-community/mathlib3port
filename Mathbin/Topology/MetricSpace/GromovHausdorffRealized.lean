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
  { f : Cb X Y | (f : _ → ℝ) ∈ candidates X Y }

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

private theorem candidates_nonneg (fA : f ∈ candidates X Y) : 0 ≤ f (x, y) :=
  by 
    have  : 0 ≤ 2*f (x, y) :=
      calc 0 = f (x, x) := (candidates_refl fA).symm 
        _ ≤ f (x, y)+f (y, x) := candidates_triangle fA 
        _ = f (x, y)+f (x, y) :=
        by 
          rw [candidates_symm fA]
        _ = 2*f (x, y) :=
        by 
          ring
        
    ·
      linarith

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

-- error in Topology.MetricSpace.GromovHausdorffRealized: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- The distance on `X ⊕ Y` is a candidate -/
private
theorem dist_mem_candidates : «expr ∈ »(λ
 p : «expr × »(«expr ⊕ »(X, Y), «expr ⊕ »(X, Y)), dist p.1 p.2, candidates X Y) :=
begin
  simp [] [] ["only"] ["[", expr candidates, ",", expr dist_comm, ",", expr forall_const, ",", expr and_true, ",", expr add_comm, ",", expr eq_self_iff_true, ",", expr and_self, ",", expr sum.forall, ",", expr set.mem_set_of_eq, ",", expr dist_self, "]"] [] [],
  repeat { split <|> exact [expr λ
     a y z, dist_triangle_left _ _ _] <|> exact [expr λ x y, by refl] <|> exact [expr λ x y, max_var_bound] }
end

/-- The distance on `X ⊕ Y` as a candidate -/
def candidates_b_dist (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Inhabited X] [MetricSpace Y]
  [CompactSpace Y] [Inhabited Y] : Cb X Y :=
  candidates_b_of_candidates _ dist_mem_candidates

theorem candidates_b_dist_mem_candidates_b : candidates_b_dist X Y ∈ candidates_b X Y :=
  candidates_b_of_candidates_mem _ _

private theorem candidates_b_nonempty : (candidates_b X Y).Nonempty :=
  ⟨_, candidates_b_dist_mem_candidates_b⟩

-- error in Topology.MetricSpace.GromovHausdorffRealized: ././Mathport/Syntax/Translate/Basic.lean:340:40: in repeat: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
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

/-- Compactness of candidates (in bounded_continuous_functions) follows. -/
private theorem compact_candidates_b : IsCompact (candidates_b X Y) :=
  by 
    refine' arzela_ascoli₂ (Icc 0 (max_var X Y)) is_compact_Icc (candidates_b X Y) closed_candidates_b _ _
    ·
      rintro f ⟨x1, x2⟩ hf 
      simp only [Set.mem_Icc]
      exact ⟨candidates_nonneg hf, candidates_le_max_var hf⟩
    ·
      refine' equicontinuous_of_continuity_modulus (fun t => (2*max_var X Y)*t) _ _ _
      ·
        have  : tendsto (fun t : ℝ => (2*(max_var X Y : ℝ))*t) (𝓝 0) (𝓝 ((2*max_var X Y)*0)) :=
          tendsto_const_nhds.mul tendsto_id 
        simpa using this
      ·
        intro x y f hf 
        exact (candidates_lipschitz hf).dist_le_mul _ _

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

/-- Explicit bound on `HD (dist)`. This means that when looking for minimizers it will
be sufficient to look for functions with `HD(f)` bounded by this bound. -/
theorem HD_candidates_b_dist_le : HD (candidates_b_dist X Y) ≤ (diam (univ : Set X)+1)+diam (univ : Set Y) :=
  by 
    refine' max_leₓ (csupr_le fun x => _) (csupr_le fun y => _)
    ·
      have A : (⨅y, candidates_b_dist X Y (inl x, inr y)) ≤ candidates_b_dist X Y (inl x, inr (default Y)) :=
        cinfi_le
          (by 
            simpa using HD_below_aux1 0)
          (default Y)
      have B : dist (inl x) (inr (default Y)) ≤ (diam (univ : Set X)+1)+diam (univ : Set Y) :=
        calc dist (inl x) (inr (default Y)) = (dist x (default X)+1)+dist (default Y) (default Y) := rfl 
          _ ≤ (diam (univ : Set X)+1)+diam (univ : Set Y) :=
          by 
            apply add_le_add (add_le_add _ (le_reflₓ _))
            exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
            any_goals 
              exact OrderedAddCommMonoid.to_covariant_class_left ℝ 
            any_goals 
              exact OrderedAddCommMonoid.to_covariant_class_right ℝ 
            exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
          
      exact le_transₓ A B
    ·
      have A : (⨅x, candidates_b_dist X Y (inl x, inr y)) ≤ candidates_b_dist X Y (inl (default X), inr y) :=
        cinfi_le
          (by 
            simpa using HD_below_aux2 0)
          (default X)
      have B : dist (inl (default X)) (inr y) ≤ (diam (univ : Set X)+1)+diam (univ : Set Y) :=
        calc dist (inl (default X)) (inr y) = (dist (default X) (default X)+1)+dist (default Y) y := rfl 
          _ ≤ (diam (univ : Set X)+1)+diam (univ : Set Y) :=
          by 
            apply add_le_add (add_le_add _ (le_reflₓ _))
            exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
            any_goals 
              exact OrderedAddCommMonoid.to_covariant_class_left ℝ 
            any_goals 
              exact OrderedAddCommMonoid.to_covariant_class_right ℝ 
            exact dist_le_diam_of_mem bounded_of_compact_space (mem_univ _) (mem_univ _)
          
      exact le_transₓ A B

private theorem HD_lipschitz_aux1 (f g : Cb X Y) : (⨆x, ⨅y, f (inl x, inr y)) ≤ (⨆x, ⨅y, g (inl x, inr y))+dist f g :=
  by 
    rcases(Real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1 with ⟨cg, hcg⟩
    have Hcg : ∀ x, cg ≤ g x := fun x => hcg (mem_range_self x)
    rcases(Real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1 with ⟨cf, hcf⟩
    have Hcf : ∀ x, cf ≤ f x := fun x => hcf (mem_range_self x)
    have Z : (⨆x, ⨅y, f (inl x, inr y)) ≤ ⨆x, ⨅y, g (inl x, inr y)+dist f g :=
      csupr_le_csupr (HD_bound_aux1 _ (dist f g))
        fun x => cinfi_le_cinfi ⟨cf, forall_range_iff.2 fun i => Hcf _⟩ fun y => coe_le_coe_add_dist 
    have E1 : ∀ x, ((⨅y, g (inl x, inr y))+dist f g) = ⨅y, g (inl x, inr y)+dist f g
    ·
      intro x 
      refine' map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ _
      ·
        intro x y hx 
        simpa
      ·
        show BddBelow (range fun y : Y => g (inl x, inr y))
        exact ⟨cg, forall_range_iff.2 fun i => Hcg _⟩
    have E2 : ((⨆x, ⨅y, g (inl x, inr y))+dist f g) = ⨆x, (⨅y, g (inl x, inr y))+dist f g
    ·
      refine' map_csupr_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ _
      ·
        intro x y hx 
        simpa
      ·
        ·
          simpa using HD_bound_aux1 _ 0
    simpa [E2, E1, Function.comp]

private theorem HD_lipschitz_aux2 (f g : Cb X Y) : (⨆y, ⨅x, f (inl x, inr y)) ≤ (⨆y, ⨅x, g (inl x, inr y))+dist f g :=
  by 
    rcases(Real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1 with ⟨cg, hcg⟩
    have Hcg : ∀ x, cg ≤ g x := fun x => hcg (mem_range_self x)
    rcases(Real.bounded_iff_bdd_below_bdd_above.1 bounded_range).1 with ⟨cf, hcf⟩
    have Hcf : ∀ x, cf ≤ f x := fun x => hcf (mem_range_self x)
    have Z : (⨆y, ⨅x, f (inl x, inr y)) ≤ ⨆y, ⨅x, g (inl x, inr y)+dist f g :=
      csupr_le_csupr (HD_bound_aux2 _ (dist f g))
        fun y => cinfi_le_cinfi ⟨cf, forall_range_iff.2 fun i => Hcf _⟩ fun y => coe_le_coe_add_dist 
    have E1 : ∀ y, ((⨅x, g (inl x, inr y))+dist f g) = ⨅x, g (inl x, inr y)+dist f g
    ·
      intro y 
      refine' map_cinfi_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ _
      ·
        intro x y hx 
        simpa
      ·
        show BddBelow (range fun x : X => g (inl x, inr y))
        exact ⟨cg, forall_range_iff.2 fun i => Hcg _⟩
    have E2 : ((⨆y, ⨅x, g (inl x, inr y))+dist f g) = ⨆y, (⨅x, g (inl x, inr y))+dist f g
    ·
      refine' map_csupr_of_continuous_at_of_monotone (continuous_at_id.add continuous_at_const) _ _
      ·
        intro x y hx 
        simpa
      ·
        ·
          simpa using HD_bound_aux2 _ 0
    simpa [E2, E1]

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

-- error in Topology.MetricSpace.GromovHausdorffRealized: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler metric_space
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

/-- The optimal coupling between two compact spaces `X` and `Y` is still a compact space -/
instance compact_space_optimal_GH_coupling : CompactSpace (optimal_GH_coupling X Y) :=
  ⟨by 
      have  : (univ : Set (optimal_GH_coupling X Y)) = optimal_GH_injl X Y '' univ ∪ optimal_GH_injr X Y '' univ
      ·
        refine' subset.antisymm (fun xc hxc => _) (subset_univ _)
        rcases Quotientₓ.exists_rep xc with ⟨x, hx⟩
        cases x <;> rw [←hx]
        ·
          have  : «expr⟦ ⟧» (inl x) = optimal_GH_injl X Y x := rfl 
          rw [this]
          exact mem_union_left _ (mem_image_of_mem _ (mem_univ _))
        ·
          have  : «expr⟦ ⟧» (inr x) = optimal_GH_injr X Y x := rfl 
          rw [this]
          exact mem_union_right _ (mem_image_of_mem _ (mem_univ _))
      rw [this]
      exact
        (compact_univ.image (isometry_optimal_GH_injl X Y).Continuous).union
          (compact_univ.image (isometry_optimal_GH_injr X Y).Continuous)⟩

/-- For any candidate `f`, `HD(f)` is larger than or equal to the Hausdorff distance in the
optimal coupling. This follows from the fact that HD of the optimal candidate is exactly
the Hausdorff distance in the optimal coupling, although we only prove here the inequality
we need. -/
theorem Hausdorff_dist_optimal_le_HD {f} (h : f ∈ candidates_b X Y) :
  Hausdorff_dist (range (optimal_GH_injl X Y)) (range (optimal_GH_injr X Y)) ≤ HD f :=
  by 
    refine' le_transₓ (le_of_forall_le_of_dense fun r hr => _) (HD_optimal_GH_dist_le X Y f h)
    have A : ∀ x _ : x ∈ range (optimal_GH_injl X Y), ∃ (y : _)(_ : y ∈ range (optimal_GH_injr X Y)), dist x y ≤ r
    ·
      intro x hx 
      rcases mem_range.1 hx with ⟨z, hz⟩
      rw [←hz]
      have I1 : (⨆x, ⨅y, optimal_GH_dist X Y (inl x, inr y)) < r := lt_of_le_of_ltₓ (le_max_leftₓ _ _) hr 
      have I2 : (⨅y, optimal_GH_dist X Y (inl z, inr y)) ≤ ⨆x, ⨅y, optimal_GH_dist X Y (inl x, inr y) :=
        le_cSup
          (by 
            simpa using HD_bound_aux1 _ 0)
          (mem_range_self _)
      have I : (⨅y, optimal_GH_dist X Y (inl z, inr y)) < r := lt_of_le_of_ltₓ I2 I1 
      rcases exists_lt_of_cInf_lt (range_nonempty _) I with ⟨r', r'range, hr'⟩
      rcases mem_range.1 r'range with ⟨z', hz'⟩
      exists optimal_GH_injr X Y z', mem_range_self _ 
      have  : (optimal_GH_dist X Y) (inl z, inr z') ≤ r
      ·
        ·
          rw [hz']
          exact le_of_ltₓ hr' 
      exact this 
    refine' Hausdorff_dist_le_of_mem_dist _ A _
    ·
      rcases exists_mem_of_nonempty X with ⟨xX, _⟩
      have  : optimal_GH_injl X Y xX ∈ range (optimal_GH_injl X Y) := mem_range_self _ 
      rcases A _ this with ⟨y, yrange, hy⟩
      exact le_transₓ dist_nonneg hy
    ·
      intro y hy 
      rcases mem_range.1 hy with ⟨z, hz⟩
      rw [←hz]
      have I1 : (⨆y, ⨅x, optimal_GH_dist X Y (inl x, inr y)) < r := lt_of_le_of_ltₓ (le_max_rightₓ _ _) hr 
      have I2 : (⨅x, optimal_GH_dist X Y (inl x, inr z)) ≤ ⨆y, ⨅x, optimal_GH_dist X Y (inl x, inr y) :=
        le_cSup
          (by 
            simpa using HD_bound_aux2 _ 0)
          (mem_range_self _)
      have I : (⨅x, optimal_GH_dist X Y (inl x, inr z)) < r := lt_of_le_of_ltₓ I2 I1 
      rcases exists_lt_of_cInf_lt (range_nonempty _) I with ⟨r', r'range, hr'⟩
      rcases mem_range.1 r'range with ⟨z', hz'⟩
      exists optimal_GH_injl X Y z', mem_range_self _ 
      have  : (optimal_GH_dist X Y) (inl z', inr z) ≤ r
      ·
        ·
          rw [hz']
          exact le_of_ltₓ hr' 
      rw [dist_comm]
      exact this

end Consequences

end GromovHausdorffRealized

end GromovHausdorff

