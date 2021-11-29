import Mathbin.Analysis.SpecialFunctions.Bernstein 
import Mathbin.Topology.Algebra.Algebra

/-!
# The Weierstrass approximation theorem for continuous functions on `[a,b]`

We've already proved the Weierstrass approximation theorem
in the sense that we've shown that the Bernstein approximations
to a continuous function on `[0,1]` converge uniformly.

Here we rephrase this more abstractly as
`polynomial_functions_closure_eq_top' : (polynomial_functions I).topological_closure = ⊤`
and then, by precomposing with suitable affine functions,
`polynomial_functions_closure_eq_top : (polynomial_functions (set.Icc a b)).topological_closure = ⊤`
-/


open ContinuousMap Filter

open_locale UnitInterval

/--
The special case of the Weierstrass approximation theorem for the interval `[0,1]`.
This is just a matter of unravelling definitions and using the Bernstein approximations.
-/
theorem polynomial_functions_closure_eq_top' : (polynomialFunctions I).topologicalClosure = ⊤ :=
  by 
    apply eq_top_iff.mpr 
    rintro f -
    refine' Filter.Frequently.mem_closure _ 
    refine' Filter.Tendsto.frequently (bernstein_approximation_uniform f) _ 
    apply frequently_of_forall 
    intro n 
    simp only [SetLike.mem_coe]
    apply Subalgebra.sum_mem 
    rintro n -
    apply Subalgebra.smul_mem 
    dsimp [bernstein, polynomialFunctions]
    simp 

-- error in Topology.ContinuousFunction.Weierstrass: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The **Weierstrass Approximation Theorem**:
polynomials functions on `[a, b] ⊆ ℝ` are dense in `C([a,b],ℝ)`

(While we could deduce this as an application of the Stone-Weierstrass theorem,
our proof of that relies on the fact that `abs` is in the closure of polynomials on `[-M, M]`,
so we may as well get this done first.)
-/
theorem polynomial_functions_closure_eq_top
(a b : exprℝ()) : «expr = »((polynomial_functions (set.Icc a b)).topological_closure, «expr⊤»()) :=
begin
  by_cases [expr h, ":", expr «expr < »(a, b)],
  { let [ident W] [":", expr «expr →ₐ[ ] »(«exprC( , )»(set.Icc a b, exprℝ()), exprℝ(), «exprC( , )»(exprI(), exprℝ()))] [":=", expr comp_right_alg_hom exprℝ() (Icc_homeo_I a b h).symm.to_continuous_map],
    let [ident W'] [":", expr «expr ≃ₜ »(«exprC( , )»(set.Icc a b, exprℝ()), «exprC( , )»(exprI(), exprℝ()))] [":=", expr comp_right_homeomorph exprℝ() (Icc_homeo_I a b h).symm],
    have [ident w] [":", expr «expr = »((W : «exprC( , )»(set.Icc a b, exprℝ()) → «exprC( , )»(exprI(), exprℝ())), W')] [":=", expr rfl],
    have [ident p] [] [":=", expr polynomial_functions_closure_eq_top'],
    apply_fun [expr λ s, s.comap' W] ["at", ident p] [],
    simp [] [] ["only"] ["[", expr algebra.comap_top, "]"] [] ["at", ident p],
    rw [expr subalgebra.topological_closure_comap'_homeomorph _ W W' w] ["at", ident p],
    rw [expr polynomial_functions.comap'_comp_right_alg_hom_Icc_homeo_I] ["at", ident p],
    exact [expr p] },
  { haveI [] [":", expr subsingleton (set.Icc a b)] [":=", expr ⟨λ
      x y, le_antisymm ((x.2.2.trans (not_lt.mp h)).trans y.2.1) ((y.2.2.trans (not_lt.mp h)).trans x.2.1)⟩],
    haveI [] [] [":=", expr continuous_map.subsingleton_subalgebra (set.Icc a b) exprℝ()],
    apply [expr subsingleton.elim] }
end

/--
An alternative statement of Weierstrass' theorem.

Every real-valued continuous function on `[a,b]` is a uniform limit of polynomials.
-/
theorem continuous_map_mem_polynomial_functions_closure (a b : ℝ) (f : C(Set.Icc a b, ℝ)) :
  f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure :=
  by 
    rw [polynomial_functions_closure_eq_top _ _]
    simp 

-- error in Topology.ContinuousFunction.Weierstrass: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
An alternative statement of Weierstrass' theorem,
for those who like their epsilons.

Every real-valued continuous function on `[a,b]` is within any `ε > 0` of some polynomial.
-/
theorem exists_polynomial_near_continuous_map
(a b : exprℝ())
(f : «exprC( , )»(set.Icc a b, exprℝ()))
(ε : exprℝ())
(pos : «expr < »(0, ε)) : «expr∃ , »((p : polynomial exprℝ()), «expr < »(«expr∥ ∥»(«expr - »(p.to_continuous_map_on _, f)), ε)) :=
begin
  have [ident w] [] [":=", expr mem_closure_iff_frequently.mp (continuous_map_mem_polynomial_functions_closure _ _ f)],
  rw [expr metric.nhds_basis_ball.frequently_iff] ["at", ident w],
  obtain ["⟨", "-", ",", ident H, ",", "⟨", ident m, ",", "⟨", "-", ",", ident rfl, "⟩", "⟩", "⟩", ":=", expr w ε pos],
  rw ["[", expr metric.mem_ball, ",", expr dist_eq_norm, "]"] ["at", ident H],
  exact [expr ⟨m, H⟩]
end

/--
Another alternative statement of Weierstrass's theorem,
for those who like epsilons, but not bundled continuous functions.

Every real-valued function `ℝ → ℝ` which is continuous on `[a,b]`
can be approximated to within any `ε > 0` on `[a,b]` by some polynomial.
-/
theorem exists_polynomial_near_of_continuous_on (a b : ℝ) (f : ℝ → ℝ) (c : ContinuousOn f (Set.Icc a b)) (ε : ℝ)
  (pos : 0 < ε) : ∃ p : Polynomial ℝ, ∀ x (_ : x ∈ Set.Icc a b), |p.eval x - f x| < ε :=
  by 
    let f' : C(Set.Icc a b, ℝ) := ⟨fun x => f x, continuous_on_iff_continuous_restrict.mp c⟩
    obtain ⟨p, b⟩ := exists_polynomial_near_continuous_map a b f' ε Pos 
    use p 
    rw [norm_lt_iff _ Pos] at b 
    intro x m 
    exact b ⟨x, m⟩

