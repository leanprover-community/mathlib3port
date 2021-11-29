import Mathbin.Data.Real.Irrational 
import Mathbin.Topology.MetricSpace.Baire

/-!
# Topology of irrational numbers

In this file we prove the following theorems:

* `is_Gδ_irrational`, `dense_irrational`, `eventually_residual_irrational`: irrational numbers
  form a dense Gδ set;

* `irrational.eventually_forall_le_dist_cast_div`,
  `irrational.eventually_forall_le_dist_cast_div_of_denom_le`;
  `irrational.eventually_forall_le_dist_cast_rat_of_denom_le`: a sufficiently small neighborhood of
  an irrational number is disjoint with the set of rational numbers with bounded denominator.

We also provide `order_topology`, `no_bot_order`, `no_top_order`, and `densely_ordered`
instances for `{x // irrational x}`.

## Tags

irrational, residual
-/


open Set Filter Metric

open_locale Filter TopologicalSpace

theorem is_Gδ_irrational : IsGδ { x | Irrational x } :=
  (countable_range _).is_Gδ_compl

theorem dense_irrational : Dense { x:ℝ | Irrational x } :=
  by 
    refine' real.is_topological_basis_Ioo_rat.dense_iff.2 _ 
    simp only [mem_Union, mem_singleton_iff]
    rintro _ ⟨a, b, hlt, rfl⟩ hne 
    rw [inter_comm]
    exact exists_irrational_btwn (Rat.cast_lt.2 hlt)

theorem eventually_residual_irrational : ∀ᶠx in residual ℝ, Irrational x :=
  eventually_residual.2 ⟨_, is_Gδ_irrational, dense_irrational, fun _ => id⟩

namespace Irrational

variable {x : ℝ}

instance : OrderTopology { x // Irrational x } :=
  (induced_order_topology _ fun x y => Iff.rfl)$
    fun x y hlt =>
      let ⟨a, ha, hxa, hay⟩ := exists_irrational_btwn hlt
      ⟨⟨a, ha⟩, hxa, hay⟩

instance : NoTopOrder { x // Irrational x } :=
  ⟨fun ⟨x, hx⟩ =>
      ⟨⟨x+(1 : ℕ), hx.add_nat 1⟩,
        by 
          simp ⟩⟩

instance : NoBotOrder { x // Irrational x } :=
  ⟨fun ⟨x, hx⟩ =>
      ⟨⟨x - (1 : ℕ), hx.sub_nat 1⟩,
        by 
          simp ⟩⟩

instance : DenselyOrdered { x // Irrational x } :=
  ⟨fun x y hlt =>
      let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt
      ⟨⟨z, hz⟩, hxz, hzy⟩⟩

-- error in Topology.Instances.Irrational: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eventually_forall_le_dist_cast_div
(hx : irrational x)
(n : exprℕ()) : «expr∀ᶠ in , »((ε : exprℝ()), expr𝓝() 0, ∀ m : exprℤ(), «expr ≤ »(ε, dist x «expr / »(m, n))) :=
begin
  have [ident A] [":", expr is_closed (range (λ m, «expr * »(«expr ⁻¹»(n), m) : exprℤ() → exprℝ()))] [],
  from [expr ((is_closed_map_smul₀ («expr ⁻¹»(n) : exprℝ())).comp int.closed_embedding_coe_real.is_closed_map).closed_range],
  have [ident B] [":", expr «expr ∉ »(x, range (λ m, «expr * »(«expr ⁻¹»(n), m) : exprℤ() → exprℝ()))] [],
  { rintro ["⟨", ident m, ",", ident rfl, "⟩"],
    simpa [] [] [] [] [] ["using", expr hx] },
  rcases [expr metric.mem_nhds_iff.1 (A.is_open_compl.mem_nhds B), "with", "⟨", ident ε, ",", ident ε0, ",", ident hε, "⟩"],
  refine [expr (ge_mem_nhds ε0).mono (λ δ hδ m, «expr $ »(not_lt.1, λ hlt, _))],
  rw [expr dist_comm] ["at", ident hlt],
  refine [expr hε (ball_subset_ball hδ hlt) ⟨m, _⟩],
  simp [] [] [] ["[", expr div_eq_inv_mul, "]"] [] []
end

theorem eventually_forall_le_dist_cast_div_of_denom_le (hx : Irrational x) (n : ℕ) :
  ∀ᶠε : ℝ in 𝓝 0, ∀ k _ : k ≤ n m : ℤ, ε ≤ dist x (m / k) :=
  (finite_le_nat n).eventually_all.2$ fun k hk => hx.eventually_forall_le_dist_cast_div k

theorem eventually_forall_le_dist_cast_rat_of_denom_le (hx : Irrational x) (n : ℕ) :
  ∀ᶠε : ℝ in 𝓝 0, ∀ r : ℚ, r.denom ≤ n → ε ≤ dist x r :=
  (hx.eventually_forall_le_dist_cast_div_of_denom_le n).mono$ fun ε H r hr => H r.denom hr r.num

end Irrational

