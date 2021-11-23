import Mathbin.Analysis.SpecificLimits

/-!
# Hofer's lemma

This is an elementary lemma about complete metric spaces. It is motivated by an
application to the bubbling-off analysis for holomorphic curves in symplectic topology.
We are *very* far away from having these applications, but the proof here is a nice
example of a proof needing to construct a sequence by induction in the middle of the proof.

## References:

* H. Hofer and C. Viterbo, *The Weinstein conjecture in the presence of holomorphic spheres*
-/


open_locale Classical TopologicalSpace BigOperators

open Filter Finset

local notation "d" => dist

-- error in Analysis.Hofer: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem hofer
{X : Type*}
[metric_space X]
[complete_space X]
(x : X)
(ε : exprℝ())
(ε_pos : «expr < »(0, ε))
{ϕ : X → exprℝ()}
(cont : continuous ϕ)
(nonneg : ∀
 y, «expr ≤ »(0, ϕ y)) : «expr∃ , »((ε' «expr > » 0)
 (x' : X), «expr ∧ »(«expr ≤ »(ε', ε), «expr ∧ »(«expr ≤ »(exprd() x' x, «expr * »(2, ε)), «expr ∧ »(«expr ≤ »(«expr * »(ε, ϕ x), «expr * »(ε', ϕ x')), ∀
    y, «expr ≤ »(exprd() x' y, ε') → «expr ≤ »(ϕ y, «expr * »(2, ϕ x')))))) :=
begin
  by_contradiction [ident H],
  have [ident reformulation] [":", expr ∀
   (x')
   (k : exprℕ()), «expr ↔ »(«expr ≤ »(«expr * »(ε, ϕ x), «expr * »(«expr / »(ε, «expr ^ »(2, k)), ϕ x')), «expr ≤ »(«expr * »(«expr ^ »(2, k), ϕ x), ϕ x'))] [],
  { intros [ident x', ident k],
    rw ["[", expr div_mul_eq_mul_div, ",", expr le_div_iff, ",", expr mul_assoc, ",", expr mul_le_mul_left ε_pos, ",", expr mul_comm, "]"] [],
    exact [expr pow_pos (by norm_num [] []) k] },
  replace [ident H] [":", expr ∀
   k : exprℕ(), ∀
   x', «expr ∧ »(«expr ≤ »(exprd() x' x, «expr * »(2, ε)), «expr ≤ »(«expr * »(«expr ^ »(2, k), ϕ x), ϕ x')) → «expr∃ , »((y), «expr ∧ »(«expr ≤ »(exprd() x' y, «expr / »(ε, «expr ^ »(2, k))), «expr < »(«expr * »(2, ϕ x'), ϕ y)))] [],
  { intros [ident k, ident x'],
    push_neg ["at", ident H],
    simpa [] [] [] ["[", expr reformulation, "]"] [] ["using", expr H «expr / »(ε, «expr ^ »(2, k)) (by simp [] [] [] ["[", expr ε_pos, ",", expr zero_lt_two, "]"] [] []) x' (by simp [] [] [] ["[", expr ε_pos, ",", expr zero_lt_two, ",", expr one_le_two, "]"] [] [])] },
  clear [ident reformulation],
  haveI [] [":", expr nonempty X] [":=", expr ⟨x⟩],
  choose ["!"] [ident F] [ident hF] ["using", expr H],
  let [ident u] [":", expr exprℕ() → X] [":=", expr λ n, nat.rec_on n x F],
  have [ident hu0] [":", expr «expr = »(u 0, x)] [":=", expr rfl],
  have [ident hu] [":", expr ∀
   n, «expr ∧ »(«expr ≤ »(exprd() (u n) x, «expr * »(2, ε)), «expr ≤ »(«expr * »(«expr ^ »(2, n), ϕ x), ϕ (u n))) → «expr ∧ »(«expr ≤ »(exprd() (u n) «expr $ »(u, «expr + »(n, 1)), «expr / »(ε, «expr ^ »(2, n))), «expr < »(«expr * »(2, ϕ (u n)), ϕ «expr $ »(u, «expr + »(n, 1))))] [],
  { intro [ident n],
    exact [expr hF n (u n)] },
  clear [ident hF],
  have [ident key] [":", expr ∀
   n, «expr ∧ »(«expr ≤ »(exprd() (u n) (u «expr + »(n, 1)), «expr / »(ε, «expr ^ »(2, n))), «expr < »(«expr * »(2, ϕ (u n)), ϕ (u «expr + »(n, 1))))] [],
  { intro [ident n],
    induction [expr n] ["using", ident nat.case_strong_induction_on] ["with", ident n, ident IH] [],
    { specialize [expr hu 0],
      simpa [] [] [] ["[", expr hu0, ",", expr mul_nonneg_iff, ",", expr zero_le_one, ",", expr ε_pos.le, ",", expr le_refl, "]"] [] ["using", expr hu] },
    have [ident A] [":", expr «expr ≤ »(exprd() (u «expr + »(n, 1)) x, «expr * »(2, ε))] [],
    { rw ["[", expr dist_comm, "]"] [],
      let [ident r] [] [":=", expr range «expr + »(n, 1)],
      calc
        «expr ≤ »(exprd() (u 0) (u «expr + »(n, 1)), «expr∑ in , »((i), r, exprd() (u i) «expr $ »(u, «expr + »(i, 1)))) : dist_le_range_sum_dist u «expr + »(n, 1)
        «expr ≤ »(..., «expr∑ in , »((i), r, «expr / »(ε, «expr ^ »(2, i)))) : sum_le_sum (λ
         i i_in, «expr $ »(IH i, «expr $ »(nat.lt_succ_iff.mp, finset.mem_range.mp i_in)).1)
        «expr = »(..., «expr∑ in , »((i), r, «expr * »(«expr ^ »(«expr / »(1, 2), i), ε))) : by { congr' [] ["with", ident i],
          field_simp [] [] [] [] }
        «expr = »(..., «expr * »(«expr∑ in , »((i), r, «expr ^ »(«expr / »(1, 2), i)), ε)) : finset.sum_mul.symm
        «expr ≤ »(..., «expr * »(2, ε)) : mul_le_mul_of_nonneg_right (sum_geometric_two_le _) (le_of_lt ε_pos) },
    have [ident B] [":", expr «expr ≤ »(«expr * »(«expr ^ »(2, «expr + »(n, 1)), ϕ x), ϕ (u «expr + »(n, 1)))] [],
    { refine [expr @geom_le «expr ∘ »(ϕ, u) _ zero_le_two «expr + »(n, 1) (λ m hm, _)],
      exact [expr «expr $ »(IH _, nat.lt_add_one_iff.1 hm).2.le] },
    exact [expr hu «expr + »(n, 1) ⟨A, B⟩] },
  cases [expr forall_and_distrib.mp key] ["with", ident key₁, ident key₂],
  clear [ident hu, ident key],
  have [ident cauchy_u] [":", expr cauchy_seq u] [],
  { refine [expr cauchy_seq_of_le_geometric _ ε one_half_lt_one (λ n, _)],
    simpa [] [] ["only"] ["[", expr one_div, ",", expr inv_pow₀, "]"] [] ["using", expr key₁ n] },
  obtain ["⟨", ident y, ",", ident limy, "⟩", ":", expr «expr∃ , »((y), tendsto u at_top (expr𝓝() y))],
  from [expr complete_space.complete cauchy_u],
  have [ident lim_top] [":", expr tendsto «expr ∘ »(ϕ, u) at_top at_top] [],
  { let [ident v] [] [":=", expr λ n, «expr ∘ »(ϕ, u) «expr + »(n, 1)],
    suffices [] [":", expr tendsto v at_top at_top],
    by rwa [expr tendsto_add_at_top_iff_nat] ["at", ident this],
    have [ident hv₀] [":", expr «expr < »(0, v 0)] [],
    { have [] [":", expr «expr ≤ »(0, ϕ (u 0))] [":=", expr nonneg x],
      calc
        «expr ≤ »(0, «expr * »(2, ϕ (u 0))) : by linarith [] [] []
        «expr < »(..., ϕ (u «expr + »(0, 1))) : key₂ 0 },
    apply [expr tendsto_at_top_of_geom_le hv₀ one_lt_two],
    exact [expr λ n, (key₂ «expr + »(n, 1)).le] },
  have [ident lim] [":", expr tendsto «expr ∘ »(ϕ, u) at_top (expr𝓝() (ϕ y))] [],
  from [expr tendsto.comp cont.continuous_at limy],
  exact [expr not_tendsto_at_top_of_tendsto_nhds lim lim_top]
end

