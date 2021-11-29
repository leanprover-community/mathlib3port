import Mathbin.Analysis.Convex.Function 
import Mathbin.Topology.Algebra.Affine 
import Mathbin.Topology.LocalExtr 
import Mathbin.Topology.MetricSpace.Basic

/-!
# Minima and maxima of convex functions

We show that if a function `f : E → β` is convex, then a local minimum is also
a global minimum, and likewise for concave functions.
-/


variable {E β : Type _} [AddCommGroupₓ E] [TopologicalSpace E] [Module ℝ E] [TopologicalAddGroup E]
  [HasContinuousSmul ℝ E] [LinearOrderedAddCommGroup β] [Module ℝ β] [OrderedSmul ℝ β] {s : Set E}

open Set Filter

open_locale Classical

-- error in Analysis.Convex.Extrema: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Helper lemma for the more general case: `is_min_on.of_is_local_min_on_of_convex_on`.
-/
theorem is_min_on.of_is_local_min_on_of_convex_on_Icc
{f : exprℝ() → β}
{a b : exprℝ()}
(a_lt_b : «expr < »(a, b))
(h_local_min : is_local_min_on f (Icc a b) a)
(h_conv : convex_on exprℝ() (Icc a b) f) : ∀ x «expr ∈ » Icc a b, «expr ≤ »(f a, f x) :=
begin
  by_contradiction [ident H_cont],
  push_neg ["at", ident H_cont],
  rcases [expr H_cont, "with", "⟨", ident x, ",", "⟨", ident h_ax, ",", ident h_xb, "⟩", ",", ident fx_lt_fa, "⟩"],
  obtain ["⟨", ident z, ",", ident hz, ",", ident ge_on_nhd, "⟩", ":", expr «expr∃ , »((z «expr > » a), ∀
    y «expr ∈ » Icc a z, «expr ≥ »(f y, f a))],
  { rcases [expr eventually_iff_exists_mem.mp h_local_min, "with", "⟨", ident U, ",", ident U_in_nhds_within, ",", ident fy_ge_fa, "⟩"],
    rw ["[", expr nhds_within_Icc_eq_nhds_within_Ici a_lt_b, ",", expr mem_nhds_within_Ici_iff_exists_Icc_subset, "]"] ["at", ident U_in_nhds_within],
    rcases [expr U_in_nhds_within, "with", "⟨", ident ε, ",", ident ε_in_Ioi, ",", ident Ioc_in_U, "⟩"],
    exact [expr ⟨ε, mem_Ioi.mp ε_in_Ioi, λ y y_in_Ioc, «expr $ »(fy_ge_fa y, Ioc_in_U y_in_Ioc)⟩] },
  have [ident a_lt_x] [":", expr «expr < »(a, x)] [":=", expr lt_of_le_of_ne h_ax (λ
    H, by subst [expr H]; exact [expr lt_irrefl (f a) fx_lt_fa])],
  have [ident lt_on_nhd] [":", expr ∀ y «expr ∈ » Ioc a x, «expr < »(f y, f a)] [],
  { intros [ident y, ident y_in_Ioc],
    rcases [expr (convex.mem_Ioc a_lt_x).mp y_in_Ioc, "with", "⟨", ident ya, ",", ident yx, ",", ident ya_pos, ",", ident yx_pos, ",", ident yax, ",", ident y_combo, "⟩"],
    calc
      «expr = »(f y, f «expr + »(«expr * »(ya, a), «expr * »(yx, x))) : by rw ["[", expr y_combo, "]"] []
      «expr ≤ »(..., «expr + »(«expr • »(ya, f a), «expr • »(yx, f x))) : h_conv.2 (left_mem_Icc.mpr (le_of_lt a_lt_b)) ⟨h_ax, h_xb⟩ ya_pos (le_of_lt yx_pos) yax
      «expr < »(..., «expr + »(«expr • »(ya, f a), «expr • »(yx, f a))) : add_lt_add_left (smul_lt_smul_of_pos fx_lt_fa yx_pos) _
      «expr = »(..., f a) : by rw ["[", "<-", expr add_smul, ",", expr yax, ",", expr one_smul, "]"] [] },
  by_cases [expr h_xz, ":", expr «expr ≤ »(x, z)],
  { exact [expr not_lt_of_ge (ge_on_nhd x (show «expr ∈ »(x, Icc a z), by exact [expr ⟨h_ax, h_xz⟩])) fx_lt_fa] },
  { have [ident h₁] [":", expr «expr ∈ »(z, Ioc a x)] [":=", expr ⟨hz, le_of_not_ge h_xz⟩],
    have [ident h₂] [":", expr «expr ∈ »(z, Icc a z)] [":=", expr ⟨le_of_lt hz, le_refl z⟩],
    exact [expr not_lt_of_ge (ge_on_nhd z h₂) (lt_on_nhd z h₁)] }
end

-- error in Analysis.Convex.Extrema: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A local minimum of a convex function is a global minimum, restricted to a set `s`.
-/
theorem is_min_on.of_is_local_min_on_of_convex_on
{f : E → β}
{a : E}
(a_in_s : «expr ∈ »(a, s))
(h_localmin : is_local_min_on f s a)
(h_conv : convex_on exprℝ() s f) : ∀ x «expr ∈ » s, «expr ≤ »(f a, f x) :=
begin
  by_contradiction [ident H_cont],
  push_neg ["at", ident H_cont],
  rcases [expr H_cont, "with", "⟨", ident x, ",", "⟨", ident x_in_s, ",", ident fx_lt_fa, "⟩", "⟩"],
  let [ident g] [":", expr «expr →ᵃ[ ] »(exprℝ(), exprℝ(), E)] [":=", expr affine_map.line_map a x],
  have [ident hg0] [":", expr «expr = »(g 0, a)] [":=", expr affine_map.line_map_apply_zero a x],
  have [ident hg1] [":", expr «expr = »(g 1, x)] [":=", expr affine_map.line_map_apply_one a x],
  have [ident fg_local_min_on] [":", expr is_local_min_on «expr ∘ »(f, g) «expr ⁻¹' »(g, s) 0] [],
  { rw ["<-", expr hg0] ["at", ident h_localmin],
    refine [expr is_local_min_on.comp_continuous_on h_localmin subset.rfl (continuous.continuous_on affine_map.line_map_continuous) _],
    simp [] [] [] ["[", expr mem_preimage, ",", expr hg0, ",", expr a_in_s, "]"] [] [] },
  have [ident fg_min_on] [":", expr ∀
   x «expr ∈ » (Icc 0 1 : set exprℝ()), «expr ≤ »(«expr ∘ »(f, g) 0, «expr ∘ »(f, g) x)] [],
  { have [ident Icc_in_s'] [":", expr «expr ⊆ »(Icc 0 1, «expr ⁻¹' »(g, s))] [],
    { have [ident h0] [":", expr «expr ∈ »((0 : exprℝ()), «expr ⁻¹' »(g, s))] [":=", expr by simp [] [] [] ["[", expr mem_preimage, ",", expr a_in_s, "]"] [] []],
      have [ident h1] [":", expr «expr ∈ »((1 : exprℝ()), «expr ⁻¹' »(g, s))] [":=", expr by simp [] [] [] ["[", expr mem_preimage, ",", expr hg1, ",", expr x_in_s, "]"] [] []],
      rw ["<-", expr segment_eq_Icc (show «expr ≤ »((0 : exprℝ()), 1), by linarith [] [] [])] [],
      exact [expr (convex.affine_preimage g h_conv.1).segment_subset (by simp [] [] [] ["[", expr mem_preimage, ",", expr hg0, ",", expr a_in_s, "]"] [] []) (by simp [] [] [] ["[", expr mem_preimage, ",", expr hg1, ",", expr x_in_s, "]"] [] [])] },
    have [ident fg_local_min_on'] [":", expr is_local_min_on «expr ∘ »(f, g) (Icc 0 1) 0] [":=", expr is_local_min_on.on_subset fg_local_min_on Icc_in_s'],
    refine [expr is_min_on.of_is_local_min_on_of_convex_on_Icc (by linarith [] [] []) fg_local_min_on' _],
    exact [expr (convex_on.comp_affine_map g h_conv).subset Icc_in_s' (convex_Icc 0 1)] },
  have [ident gx_lt_ga] [":", expr «expr < »(«expr ∘ »(f, g) 1, «expr ∘ »(f, g) 0)] [":=", expr by simp [] [] [] ["[", expr hg1, ",", expr fx_lt_fa, ",", expr hg0, "]"] [] []],
  exact [expr not_lt_of_ge (fg_min_on 1 (mem_Icc.mpr ⟨zero_le_one, le_refl 1⟩)) gx_lt_ga]
end

/-- A local maximum of a concave function is a global maximum, restricted to a set `s`. -/
theorem IsMaxOn.of_is_local_max_on_of_concave_on {f : E → β} {a : E} (a_in_s : a ∈ s) (h_localmax : IsLocalMaxOn f s a)
  (h_conc : ConcaveOn ℝ s f) : ∀ x _ : x ∈ s, f x ≤ f a :=
  @IsMinOn.of_is_local_min_on_of_convex_on _ (OrderDual β) _ _ _ _ _ _ _ _ s f a a_in_s h_localmax h_conc

/-- A local minimum of a convex function is a global minimum. -/
theorem IsMinOn.of_is_local_min_of_convex_univ {f : E → β} {a : E} (h_local_min : IsLocalMin f a)
  (h_conv : ConvexOn ℝ univ f) : ∀ x, f a ≤ f x :=
  fun x => (IsMinOn.of_is_local_min_on_of_convex_on (mem_univ a) (IsLocalMin.on h_local_min univ) h_conv) x (mem_univ x)

/-- A local maximum of a concave function is a global maximum. -/
theorem IsMaxOn.of_is_local_max_of_convex_univ {f : E → β} {a : E} (h_local_max : IsLocalMax f a)
  (h_conc : ConcaveOn ℝ univ f) : ∀ x, f x ≤ f a :=
  @IsMinOn.of_is_local_min_of_convex_univ _ (OrderDual β) _ _ _ _ _ _ _ _ f a h_local_max h_conc

