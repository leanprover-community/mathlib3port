import Mathbin.Topology.UniformSpace.Completion 
import Mathbin.Topology.MetricSpace.Isometry 
import Mathbin.Topology.Instances.Real

/-!
# The completion of a metric space

Completion of uniform spaces are already defined in `topology.uniform_space.completion`. We show
here that the uniform space completion of a metric space inherits a metric space structure,
by extending the distance to the completion and checking that it is indeed a distance, and that
it defines the same uniformity as the already defined uniform structure on the completion
-/


open Set Filter UniformSpace UniformSpace.Completion

open_locale Filter

noncomputable theory

universe u

variable {α : Type u} [PseudoMetricSpace α]

namespace Metric

/-- The distance on the completion is obtained by extending the distance on the original space,
by uniform continuity. -/
instance : HasDist (completion α) :=
  ⟨completion.extension₂ dist⟩

/-- The new distance is uniformly continuous. -/
protected theorem completion.uniform_continuous_dist :
  UniformContinuous fun p : completion α × completion α => dist p.1 p.2 :=
  uniform_continuous_extension₂ dist

/-- The new distance is an extension of the original distance. -/
protected theorem completion.dist_eq (x y : α) : dist (x : completion α) y = dist x y :=
  completion.extension₂_coe_coe uniform_continuous_dist _ _

protected theorem completion.dist_self (x : completion α) : dist x x = 0 :=
  by 
    apply induction_on x
    ·
      refine' is_closed_eq _ continuous_const 
      exact
        (completion.uniform_continuous_dist.continuous.comp (Continuous.prod_mk continuous_id continuous_id : _) : _)
    ·
      intro a 
      rw [completion.dist_eq, dist_self]

protected theorem completion.dist_comm (x y : completion α) : dist x y = dist y x :=
  by 
    apply induction_on₂ x y
    ·
      refine' is_closed_eq completion.uniform_continuous_dist.continuous _ 
      exact completion.uniform_continuous_dist.continuous.comp (@continuous_swap (completion α) (completion α) _ _)
    ·
      intro a b 
      rw [completion.dist_eq, completion.dist_eq, dist_comm]

-- error in Topology.MetricSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem completion.dist_triangle (x y z : completion α) : «expr ≤ »(dist x z, «expr + »(dist x y, dist y z)) :=
begin
  apply [expr induction_on₃ x y z],
  { refine [expr is_closed_le _ (continuous.add _ _)],
    { have [] [":", expr continuous (λ
        p : «expr × »(completion α, «expr × »(completion α, completion α)), (p.1, p.2.2))] [":=", expr continuous.prod_mk continuous_fst (continuous.comp continuous_snd continuous_snd)],
      exact [expr (completion.uniform_continuous_dist.continuous.comp this : _)] },
    { have [] [":", expr continuous (λ
        p : «expr × »(completion α, «expr × »(completion α, completion α)), (p.1, p.2.1))] [":=", expr continuous.prod_mk continuous_fst (continuous_fst.comp continuous_snd)],
      exact [expr (completion.uniform_continuous_dist.continuous.comp this : _)] },
    { have [] [":", expr continuous (λ
        p : «expr × »(completion α, «expr × »(completion α, completion α)), (p.2.1, p.2.2))] [":=", expr continuous.prod_mk (continuous_fst.comp continuous_snd) (continuous.comp continuous_snd continuous_snd)],
      exact [expr (continuous.comp completion.uniform_continuous_dist.continuous this : _)] } },
  { assume [binders (a b c)],
    rw ["[", expr completion.dist_eq, ",", expr completion.dist_eq, ",", expr completion.dist_eq, "]"] [],
    exact [expr dist_triangle a b c] }
end

-- error in Topology.MetricSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Elements of the uniformity (defined generally for completions) can be characterized in terms
of the distance. -/
protected
theorem completion.mem_uniformity_dist
(s : set «expr × »(completion α, completion α)) : «expr ↔ »(«expr ∈ »(s, uniformity (completion α)), «expr∃ , »((ε «expr > » 0), ∀
  {a b}, «expr < »(dist a b, ε) → «expr ∈ »((a, b), s))) :=
begin
  split,
  { assume [binders (hs)],
    rcases [expr mem_uniformity_is_closed hs, "with", "⟨", ident t, ",", ident ht, ",", "⟨", ident tclosed, ",", ident ts, "⟩", "⟩"],
    have [ident A] [":", expr «expr ∈ »({x : «expr × »(α, α) | «expr ∈ »((coe x.1, coe x.2), t)}, uniformity α)] [":=", expr uniform_continuous_def.1 (uniform_continuous_coe α) t ht],
    rcases [expr mem_uniformity_dist.1 A, "with", "⟨", ident ε, ",", ident εpos, ",", ident hε, "⟩"],
    refine [expr ⟨ε, εpos, λ x y hxy, _⟩],
    have [] [":", expr «expr ∨ »(«expr ≤ »(ε, dist x y), «expr ∈ »((x, y), t))] [],
    { apply [expr induction_on₂ x y],
      { have [] [":", expr «expr = »({x : «expr × »(completion α, completion α) | «expr ∨ »(«expr ≤ »(ε, dist x.fst x.snd), «expr ∈ »((x.fst, x.snd), t))}, «expr ∪ »({p : «expr × »(completion α, completion α) | «expr ≤ »(ε, dist p.1 p.2)}, t))] [],
        by ext [] [] []; simp [] [] [] [] [] [],
        rw [expr this] [],
        apply [expr is_closed.union _ tclosed],
        exact [expr is_closed_le continuous_const completion.uniform_continuous_dist.continuous] },
      { assume [binders (x y)],
        rw [expr completion.dist_eq] [],
        by_cases [expr h, ":", expr «expr ≤ »(ε, dist x y)],
        { exact [expr or.inl h] },
        { have [ident Z] [] [":=", expr hε (not_le.1 h)],
          simp [] [] ["only"] ["[", expr set.mem_set_of_eq, "]"] [] ["at", ident Z],
          exact [expr or.inr Z] } } },
    simp [] [] ["only"] ["[", expr not_le.mpr hxy, ",", expr false_or, ",", expr not_le, "]"] [] ["at", ident this],
    exact [expr ts this] },
  { rintros ["⟨", ident ε, ",", ident εpos, ",", ident hε, "⟩"],
    let [ident r] [":", expr set «expr × »(exprℝ(), exprℝ())] [":=", expr {p | «expr < »(dist p.1 p.2, ε)}],
    have [] [":", expr «expr ∈ »(r, uniformity exprℝ())] [":=", expr metric.dist_mem_uniformity εpos],
    have [ident T] [] [":=", expr uniform_continuous_def.1 (@completion.uniform_continuous_dist α _) r this],
    simp [] [] ["only"] ["[", expr uniformity_prod_eq_prod, ",", expr mem_prod_iff, ",", expr exists_prop, ",", expr filter.mem_map, ",", expr set.mem_set_of_eq, "]"] [] ["at", ident T],
    rcases [expr T, "with", "⟨", ident t1, ",", ident ht1, ",", ident t2, ",", ident ht2, ",", ident ht, "⟩"],
    refine [expr mem_of_superset ht1 _],
    have [ident A] [":", expr ∀ a b : completion α, «expr ∈ »((a, b), t1) → «expr < »(dist a b, ε)] [],
    { assume [binders (a b hab)],
      have [] [":", expr «expr ∈ »(((a, b), (a, a)), set.prod t1 t2)] [":=", expr ⟨hab, refl_mem_uniformity ht2⟩],
      have [ident I] [] [":=", expr ht this],
      simp [] [] [] ["[", expr completion.dist_self, ",", expr real.dist_eq, ",", expr completion.dist_comm, "]"] [] ["at", ident I],
      exact [expr lt_of_le_of_lt (le_abs_self _) I] },
    show [expr «expr ⊆ »(t1, s)],
    { rintros ["⟨", ident a, ",", ident b, "⟩", ident hp],
      have [] [":", expr «expr < »(dist a b, ε)] [":=", expr A a b hp],
      exact [expr hε this] } }
end

-- error in Topology.MetricSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If two points are at distance 0, then they coincide. -/
protected
theorem completion.eq_of_dist_eq_zero (x y : completion α) (h : «expr = »(dist x y, 0)) : «expr = »(x, y) :=
begin
  have [] [":", expr separated_space (completion α)] [":=", expr by apply_instance],
  refine [expr separated_def.1 this x y (λ s hs, _)],
  rcases [expr (completion.mem_uniformity_dist s).1 hs, "with", "⟨", ident ε, ",", ident εpos, ",", ident hε, "⟩"],
  rw ["<-", expr h] ["at", ident εpos],
  exact [expr hε εpos]
end

-- error in Topology.MetricSpace.Completion: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Reformulate `completion.mem_uniformity_dist` in terms that are suitable for the definition
of the metric space structure. -/
protected
theorem completion.uniformity_dist' : «expr = »(uniformity (completion α), «expr⨅ , »((ε : {ε : exprℝ() // «expr < »(0, ε)}), expr𝓟() {p | «expr < »(dist p.1 p.2, ε.val)})) :=
begin
  ext [] [ident s] [],
  rw [expr mem_infi_of_directed] [],
  { simp [] [] [] ["[", expr completion.mem_uniformity_dist, ",", expr subset_def, "]"] [] [] },
  { rintro ["⟨", ident r, ",", ident hr, "⟩", "⟨", ident p, ",", ident hp, "⟩"],
    use [expr ⟨min r p, lt_min hr hp⟩],
    simp [] [] [] ["[", expr lt_min_iff, ",", expr («expr ≥ »), "]"] [] [] { contextual := tt } }
end

protected theorem completion.uniformity_dist :
  uniformity (completion α) = ⨅(ε : _)(_ : ε > 0), 𝓟 { p | dist p.1 p.2 < ε } :=
  by 
    simpa [infi_subtype] using @completion.uniformity_dist' α _

/-- Metric space structure on the completion of a pseudo_metric space. -/
instance completion.metric_space : MetricSpace (completion α) :=
  { dist_self := completion.dist_self, eq_of_dist_eq_zero := completion.eq_of_dist_eq_zero,
    dist_comm := completion.dist_comm, dist_triangle := completion.dist_triangle,
    toUniformSpace :=
      by 
        infer_instance,
    uniformity_dist := completion.uniformity_dist }

/-- The embedding of a metric space in its completion is an isometry. -/
theorem completion.coe_isometry : Isometry (coeₓ : α → completion α) :=
  isometry_emetric_iff_metric.2 completion.dist_eq

end Metric

