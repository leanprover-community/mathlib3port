import Mathbin.NumberTheory.Liouville.Basic 
import Mathbin.Topology.MetricSpace.Baire 
import Mathbin.Topology.Instances.Irrational

/-!
# Density of Liouville numbers

In this file we prove that the set of Liouville numbers form a dense `Gδ` set. We also prove a
similar statement about irrational numbers.
-/


open_locale Filter

open Filter Set Metric

theorem set_of_liouville_eq_Inter_Union :
  { x | Liouville x } = ⋂n : ℕ, ⋃(a b : ℤ)(hb : 1 < b), ball (a / b) (1 / (b^n)) \ {a / b} :=
  by 
    ext x 
    simp only [mem_Inter, mem_Union, Liouville, mem_set_of_eq, exists_prop, mem_diff, mem_singleton_iff, mem_ball,
      Real.dist_eq, and_comm]

theorem is_Gδ_set_of_liouville : IsGδ { x | Liouville x } :=
  by 
    rw [set_of_liouville_eq_Inter_Union]
    refine' is_Gδ_Inter fun n => IsOpen.is_Gδ _ 
    refine' is_open_Union fun a => is_open_Union$ fun b => is_open_Union$ fun hb => _ 
    exact is_open_ball.inter is_closed_singleton.is_open_compl

theorem set_of_liouville_eq_irrational_inter_Inter_Union :
  { x | Liouville x } = { x | Irrational x } ∩ ⋂n : ℕ, ⋃(a b : ℤ)(hb : 1 < b), ball (a / b) (1 / (b^n)) :=
  by 
    refine' subset.antisymm _ _
    ·
      refine' subset_inter (fun x hx => hx.irrational) _ 
      rw [set_of_liouville_eq_Inter_Union]
      exact
        Inter_subset_Inter
          fun n =>
            Union_subset_Union$ fun a => Union_subset_Union$ fun b => Union_subset_Union$ fun hb => diff_subset _ _
    ·
      simp only [inter_Inter, inter_Union, set_of_liouville_eq_Inter_Union]
      refine'
        Inter_subset_Inter
          fun n => Union_subset_Union$ fun a => Union_subset_Union$ fun b => Union_subset_Union$ fun hb => _ 
      rw [inter_comm]
      refine' diff_subset_diff subset.rfl (singleton_subset_iff.2 ⟨a / b, _⟩)
      normCast

-- error in NumberTheory.Liouville.Residual: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The set of Liouville numbers is a residual set. -/
theorem eventually_residual_liouville : «expr∀ᶠ in , »((x), residual exprℝ(), liouville x) :=
begin
  rw ["[", expr filter.eventually, ",", expr set_of_liouville_eq_irrational_inter_Inter_Union, "]"] [],
  refine [expr eventually_residual_irrational.and _],
  refine [expr eventually_residual.2 ⟨_, _, rat.dense_embedding_coe_real.dense.mono _, subset.rfl⟩],
  { exact [expr is_Gδ_Inter (λ
      n, «expr $ »(is_open.is_Gδ, «expr $ »(is_open_Union, λ
        a, «expr $ »(is_open_Union, λ b, «expr $ »(is_open_Union, λ hb, is_open_ball)))))] },
  { rintro ["_", "⟨", ident r, ",", ident rfl, "⟩"],
    simp [] [] ["only"] ["[", expr mem_Inter, ",", expr mem_Union, "]"] [] [],
    refine [expr λ n, ⟨«expr * »(r.num, 2), «expr * »(r.denom, 2), _, _⟩],
    { have [] [] [":=", expr int.coe_nat_le.2 r.pos],
      rw [expr int.coe_nat_one] ["at", ident this],
      linarith [] [] [] },
    { convert [] [expr mem_ball_self _] ["using", 2],
      { norm_cast [],
        field_simp [] [] [] [] },
      { refine [expr one_div_pos.2 (pow_pos (int.cast_pos.2 _) _)],
        exact [expr mul_pos (int.coe_nat_pos.2 r.pos) zero_lt_two] } } }
end

/-- The set of Liouville numbers in dense. -/
theorem dense_liouville : Dense { x | Liouville x } :=
  dense_of_mem_residual eventually_residual_liouville

