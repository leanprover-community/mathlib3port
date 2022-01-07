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

/-- The special case of the Weierstrass approximation theorem for the interval `[0,1]`.
This is just a matter of unravelling definitions and using the Bernstein approximations.
-/
theorem polynomial_functions_closure_eq_top' : (polynomialFunctions I).topologicalClosure = ⊤ := by
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

/-- The **Weierstrass Approximation Theorem**:
polynomials functions on `[a, b] ⊆ ℝ` are dense in `C([a,b],ℝ)`

(While we could deduce this as an application of the Stone-Weierstrass theorem,
our proof of that relies on the fact that `abs` is in the closure of polynomials on `[-M, M]`,
so we may as well get this done first.)
-/
theorem polynomial_functions_closure_eq_top (a b : ℝ) : (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ := by
  by_cases' h : a < b
  · let W : C(Set.Icc a b, ℝ) →ₐ[ℝ] C(I, ℝ) := comp_right_alg_hom ℝ (iccHomeoI a b h).symm.toContinuousMap
    let W' : C(Set.Icc a b, ℝ) ≃ₜ C(I, ℝ) := comp_right_homeomorph ℝ (iccHomeoI a b h).symm
    have w : (W : C(Set.Icc a b, ℝ) → C(I, ℝ)) = W' := rfl
    have p := polynomial_functions_closure_eq_top'
    apply_fun fun s => s.comap' W  at p
    simp only [Algebra.comap_top] at p
    rw [Subalgebra.topological_closure_comap'_homeomorph _ W W' w] at p
    rw [polynomialFunctions.comap'_comp_right_alg_hom_Icc_homeo_I] at p
    exact p
    
  · have : Subsingleton (Set.Icc a b) :=
      ⟨fun x y => le_antisymmₓ ((x.2.2.trans (not_lt.mp h)).trans y.2.1) ((y.2.2.trans (not_lt.mp h)).trans x.2.1)⟩
    have := ContinuousMap.subsingleton_subalgebra (Set.Icc a b) ℝ
    apply Subsingleton.elimₓ
    

/-- An alternative statement of Weierstrass' theorem.

Every real-valued continuous function on `[a,b]` is a uniform limit of polynomials.
-/
theorem continuous_map_mem_polynomial_functions_closure (a b : ℝ) (f : C(Set.Icc a b, ℝ)) :
    f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
  rw [polynomial_functions_closure_eq_top _ _]
  simp

/-- An alternative statement of Weierstrass' theorem,
for those who like their epsilons.

Every real-valued continuous function on `[a,b]` is within any `ε > 0` of some polynomial.
-/
theorem exists_polynomial_near_continuous_map (a b : ℝ) (f : C(Set.Icc a b, ℝ)) (ε : ℝ) (pos : 0 < ε) :
    ∃ p : Polynomial ℝ, ∥p.to_continuous_map_on _ - f∥ < ε := by
  have w := mem_closure_iff_frequently.mp (continuous_map_mem_polynomial_functions_closure _ _ f)
  rw [metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨-, H, ⟨m, ⟨-, rfl⟩⟩⟩ := w ε Pos
  rw [Metric.mem_ball, dist_eq_norm] at H
  exact ⟨m, H⟩

/-- Another alternative statement of Weierstrass's theorem,
for those who like epsilons, but not bundled continuous functions.

Every real-valued function `ℝ → ℝ` which is continuous on `[a,b]`
can be approximated to within any `ε > 0` on `[a,b]` by some polynomial.
-/
theorem exists_polynomial_near_of_continuous_on (a b : ℝ) (f : ℝ → ℝ) (c : ContinuousOn f (Set.Icc a b)) (ε : ℝ)
    (pos : 0 < ε) : ∃ p : Polynomial ℝ, ∀, ∀ x ∈ Set.Icc a b, ∀, |p.eval x - f x| < ε := by
  let f' : C(Set.Icc a b, ℝ) := ⟨fun x => f x, continuous_on_iff_continuous_restrict.mp c⟩
  obtain ⟨p, b⟩ := exists_polynomial_near_continuous_map a b f' ε Pos
  use p
  rw [norm_lt_iff _ Pos] at b
  intro x m
  exact b ⟨x, m⟩

