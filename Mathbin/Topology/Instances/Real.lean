import Mathbin.Topology.MetricSpace.Basic 
import Mathbin.Topology.Algebra.UniformGroup 
import Mathbin.Topology.Algebra.Ring 
import Mathbin.RingTheory.Subring 
import Mathbin.GroupTheory.Archimedean 
import Mathbin.Algebra.Periodic

/-!
# Topological properties of ℝ
-/


noncomputable theory

open Classical Filter Int Metric Set TopologicalSpace

open_locale Classical TopologicalSpace Filter uniformity Interval

universe u v w

variable{α : Type u}{β : Type v}{γ : Type w}

instance  : MetricSpace ℚ :=
  MetricSpace.induced coeₓ Rat.cast_injective Real.metricSpace

namespace Rat

theorem dist_eq (x y : ℚ) : dist x y = |x - y| :=
  rfl

@[normCast, simp]
theorem dist_cast (x y : ℚ) : dist (x : ℝ) y = dist x y :=
  rfl

theorem uniform_continuous_coe_real : UniformContinuous (coeₓ : ℚ → ℝ) :=
  uniform_continuous_comap

theorem uniform_embedding_coe_real : UniformEmbedding (coeₓ : ℚ → ℝ) :=
  uniform_embedding_comap Rat.cast_injective

theorem dense_embedding_coe_real : DenseEmbedding (coeₓ : ℚ → ℝ) :=
  uniform_embedding_coe_real.DenseEmbedding$
    fun x =>
      mem_closure_iff_nhds.2$
        fun t ht =>
          let ⟨ε, ε0, hε⟩ := Metric.mem_nhds_iff.1 ht 
          let ⟨q, h⟩ := exists_rat_near x ε0
          ⟨_, hε (mem_ball'.2 h), q, rfl⟩

theorem embedding_coe_real : Embedding (coeₓ : ℚ → ℝ) :=
  dense_embedding_coe_real.toEmbedding

theorem continuous_coe_real : Continuous (coeₓ : ℚ → ℝ) :=
  uniform_continuous_coe_real.Continuous

end Rat

namespace Int

instance  : HasDist ℤ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℤ) : dist x y = |x - y| :=
  rfl

@[normCast, simp]
theorem dist_cast_real (x y : ℤ) : dist (x : ℝ) y = dist x y :=
  rfl

@[normCast, simp]
theorem dist_cast_rat (x y : ℤ) : dist (x : ℚ) y = dist x y :=
  by 
    rw [←Int.dist_cast_real, ←Rat.dist_cast] <;> congr 1 <;> normCast

theorem pairwise_one_le_dist : Pairwise fun m n : ℤ => 1 ≤ dist m n :=
  by 
    intro m n hne 
    rw [dist_eq]
    normCast 
    rwa [←zero_addₓ (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]

theorem uniform_embedding_coe_rat : UniformEmbedding (coeₓ : ℤ → ℚ) :=
  uniform_embedding_bot_of_pairwise_le_dist zero_lt_one$
    by 
      simpa using pairwise_one_le_dist

theorem closed_embedding_coe_rat : ClosedEmbedding (coeₓ : ℤ → ℚ) :=
  closed_embedding_of_pairwise_le_dist zero_lt_one$
    by 
      simpa using pairwise_one_le_dist

theorem uniform_embedding_coe_real : UniformEmbedding (coeₓ : ℤ → ℝ) :=
  uniform_embedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

theorem closed_embedding_coe_real : ClosedEmbedding (coeₓ : ℤ → ℝ) :=
  closed_embedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

instance  : MetricSpace ℤ :=
  Int.uniform_embedding_coe_real.comapMetricSpace _

theorem preimage_ball (x : ℤ) (r : ℝ) : coeₓ ⁻¹' ball (x : ℝ) r = ball x r :=
  rfl

theorem preimage_closed_ball (x : ℤ) (r : ℝ) : coeₓ ⁻¹' closed_ball (x : ℝ) r = closed_ball x r :=
  rfl

theorem ball_eq (x : ℤ) (r : ℝ) : ball x r = Ioo ⌊«expr↑ » x - r⌋ ⌈«expr↑ » x+r⌉ :=
  by 
    rw [←preimage_ball, Real.ball_eq, preimage_Ioo]

theorem closed_ball_eq (x : ℤ) (r : ℝ) : closed_ball x r = Icc ⌈«expr↑ » x - r⌉ ⌊«expr↑ » x+r⌋ :=
  by 
    rw [←preimage_closed_ball, Real.closed_ball_eq, preimage_Icc]

instance  : ProperSpace ℤ :=
  ⟨by 
      intro x r 
      rw [closed_ball_eq]
      exact (Set.finite_Icc _ _).IsCompact⟩

instance  : NoncompactSpace ℤ :=
  by 
    rw [←not_compact_space_iff, Metric.compact_space_iff_bounded_univ]
    rintro ⟨r, hr⟩
    refine' (hr (⌊r⌋+1) 0 trivialₓ trivialₓ).not_lt _ 
    simpa [dist_eq] using (lt_floor_add_one r).trans_le (le_abs_self _)

end Int

instance  : NoncompactSpace ℚ :=
  Int.closed_embedding_coe_rat.NoncompactSpace

instance  : NoncompactSpace ℝ :=
  Int.closed_embedding_coe_real.NoncompactSpace

theorem Real.uniform_continuous_add : UniformContinuous fun p : ℝ × ℝ => p.1+p.2 :=
  Metric.uniform_continuous_iff.2$
    fun ε ε0 =>
      let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0
      ⟨δ, δ0,
        fun a b h =>
          let ⟨h₁, h₂⟩ := max_lt_iff.1 h 
          Hδ h₁ h₂⟩

theorem Rat.uniform_continuous_add : UniformContinuous fun p : ℚ × ℚ => p.1+p.2 :=
  Rat.uniform_embedding_coe_real.to_uniform_inducing.uniform_continuous_iff.2$
    by 
      simp only [· ∘ ·, Rat.cast_add] <;>
        exact
          real.uniform_continuous_add.comp (rat.uniform_continuous_coe_real.prod_map Rat.uniform_continuous_coe_real)

theorem Real.uniform_continuous_neg : UniformContinuous (@Neg.neg ℝ _) :=
  Metric.uniform_continuous_iff.2$
    fun ε ε0 =>
      ⟨_, ε0,
        fun a b h =>
          by 
            rw [dist_comm] at h <;> simpa [Real.dist_eq] using h⟩

theorem Rat.uniform_continuous_neg : UniformContinuous (@Neg.neg ℚ _) :=
  Metric.uniform_continuous_iff.2$
    fun ε ε0 =>
      ⟨_, ε0,
        fun a b h =>
          by 
            rw [dist_comm] at h <;> simpa [Rat.dist_eq] using h⟩

instance  : UniformAddGroup ℝ :=
  UniformAddGroup.mk' Real.uniform_continuous_add Real.uniform_continuous_neg

instance  : UniformAddGroup ℚ :=
  UniformAddGroup.mk' Rat.uniform_continuous_add Rat.uniform_continuous_neg

instance  : TopologicalAddGroup ℝ :=
  by 
    infer_instance

instance  : TopologicalAddGroup ℚ :=
  by 
    infer_instance

instance  : OrderTopology ℚ :=
  induced_order_topology _ (fun x y => Rat.cast_lt) (@exists_rat_btwn _ _ _)

instance  : ProperSpace ℝ :=
  { is_compact_closed_ball :=
      fun x r =>
        by 
          rw [Real.closed_ball_eq]
          apply is_compact_Icc }

instance  : second_countable_topology ℝ :=
  second_countable_of_proper

-- error in Topology.Instances.Real: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem real.is_topological_basis_Ioo_rat : @is_topological_basis exprℝ() _ «expr⋃ , »((a b : exprℚ())
 (h : «expr < »(a, b)), {Ioo a b}) :=
is_topological_basis_of_open_of_nhds (by simp [] [] [] ["[", expr is_open_Ioo, "]"] [] [] { contextual := tt }) (assume
 a
 v
 hav
 hv, let ⟨l, u, ⟨hl, hu⟩, h⟩ := mem_nhds_iff_exists_Ioo_subset.mp (is_open.mem_nhds hv hav),
     ⟨q, hlq, hqa⟩ := exists_rat_btwn hl,
     ⟨p, hap, hpu⟩ := exists_rat_btwn hu in
 ⟨Ioo q p, by { simp [] [] ["only"] ["[", expr mem_Union, "]"] [] [],
    exact [expr ⟨q, p, «expr $ »(rat.cast_lt.1, hqa.trans hap), rfl⟩] }, ⟨hqa, hap⟩, assume
  (a')
  ⟨hqa', ha'p⟩, h ⟨hlq.trans hqa', ha'p.trans hpu⟩⟩)

theorem Real.mem_closure_iff {s : Set ℝ} {x : ℝ} : x ∈ Closure s ↔ ∀ ε _ : ε > 0, ∃ (y : _)(_ : y ∈ s), |y - x| < ε :=
  by 
    simp [mem_closure_iff_nhds_basis nhds_basis_ball, Real.dist_eq]

theorem Real.uniform_continuous_inv (s : Set ℝ) {r : ℝ} (r0 : 0 < r) (H : ∀ x _ : x ∈ s, r ≤ |x|) :
  UniformContinuous fun p : s => p.1⁻¹ :=
  Metric.uniform_continuous_iff.2$
    fun ε ε0 =>
      let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abs ε0 r0
      ⟨δ, δ0, fun a b h => Hδ (H _ a.2) (H _ b.2) h⟩

theorem Real.uniform_continuous_abs : UniformContinuous (abs : ℝ → ℝ) :=
  Metric.uniform_continuous_iff.2$ fun ε ε0 => ⟨ε, ε0, fun a b => lt_of_le_of_ltₓ (abs_abs_sub_abs_le_abs_sub _ _)⟩

theorem Rat.uniform_continuous_abs : UniformContinuous (abs : ℚ → ℚ) :=
  Metric.uniform_continuous_iff.2$
    fun ε ε0 =>
      ⟨ε, ε0,
        fun a b h =>
          lt_of_le_of_ltₓ
            (by 
              simpa [Rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _)
            h⟩

theorem Real.tendsto_inv {r : ℝ} (r0 : r ≠ 0) : tendsto (fun q => q⁻¹) (𝓝 r) (𝓝 (r⁻¹)) :=
  by 
    rw [←abs_pos] at r0 <;>
      exact
        tendsto_of_uniform_continuous_subtype
          (Real.uniform_continuous_inv { x | |r| / 2 < |x| } (half_pos r0) fun x h => le_of_ltₓ h)
          (IsOpen.mem_nhds ((is_open_lt' (|r| / 2)).Preimage continuous_abs) (half_lt_self r0))

theorem Real.continuous_inv : Continuous fun a : { r : ℝ // r ≠ 0 } => a.val⁻¹ :=
  continuous_iff_continuous_at.mpr$
    fun ⟨r, hr⟩ => tendsto.comp (Real.tendsto_inv hr) (continuous_iff_continuous_at.mp continuous_subtype_val _)

theorem Real.Continuous.inv [TopologicalSpace α] {f : α → ℝ} (h : ∀ a, f a ≠ 0) (hf : Continuous f) :
  Continuous fun a => f a⁻¹ :=
  show Continuous ((HasInv.inv ∘ @Subtype.val ℝ fun r => r ≠ 0) ∘ fun a => ⟨f a, h a⟩) from
    Real.continuous_inv.comp (continuous_subtype_mk _ hf)

-- error in Topology.Instances.Real: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem real.uniform_continuous_mul_const {x : exprℝ()} : uniform_continuous (((«expr * »)) x) :=
«expr $ »(metric.uniform_continuous_iff.2, λ ε ε0, begin
   cases [expr no_top «expr| |»(x)] ["with", ident y, ident xy],
   have [ident y0] [] [":=", expr lt_of_le_of_lt (abs_nonneg _) xy],
   refine [expr ⟨_, div_pos ε0 y0, λ a b h, _⟩],
   rw ["[", expr real.dist_eq, ",", "<-", expr mul_sub, ",", expr abs_mul, ",", "<-", expr mul_div_cancel' ε (ne_of_gt y0), "]"] [],
   exact [expr mul_lt_mul' (le_of_lt xy) h (abs_nonneg _) y0]
 end)

theorem Real.uniform_continuous_mul (s : Set (ℝ × ℝ)) {r₁ r₂ : ℝ}
  (H : ∀ x _ : x ∈ s, |(x : ℝ × ℝ).1| < r₁ ∧ |x.2| < r₂) : UniformContinuous fun p : s => p.1.1*p.1.2 :=
  Metric.uniform_continuous_iff.2$
    fun ε ε0 =>
      let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abs ε0
      ⟨δ, δ0,
        fun a b h =>
          let ⟨h₁, h₂⟩ := max_lt_iff.1 h 
          Hδ (H _ a.2).1 (H _ b.2).2 h₁ h₂⟩

protected theorem Real.continuous_mul : Continuous fun p : ℝ × ℝ => p.1*p.2 :=
  continuous_iff_continuous_at.2$
    fun ⟨a₁, a₂⟩ =>
      tendsto_of_uniform_continuous_subtype
        (Real.uniform_continuous_mul ({ x | |x| < |a₁|+1 }.Prod { x | |x| < |a₂|+1 }) fun x => id)
        (IsOpen.mem_nhds
          (((is_open_gt' (|a₁|+1)).Preimage continuous_abs).Prod ((is_open_gt' (|a₂|+1)).Preimage continuous_abs))
          ⟨lt_add_one |a₁|, lt_add_one |a₂|⟩)

instance  : TopologicalRing ℝ :=
  { Real.topological_add_group with continuous_mul := Real.continuous_mul }

theorem Rat.continuous_mul : Continuous fun p : ℚ × ℚ => p.1*p.2 :=
  Rat.embedding_coe_real.continuous_iff.2$
    by 
      simp [· ∘ ·] <;> exact real.continuous_mul.comp (rat.continuous_coe_real.prod_map Rat.continuous_coe_real)

instance  : TopologicalRing ℚ :=
  { Rat.topological_add_group with continuous_mul := Rat.continuous_mul }

theorem Real.ball_eq_Ioo (x ε : ℝ) : ball x ε = Ioo (x - ε) (x+ε) :=
  Set.ext$
    fun y =>
      by 
        rw [mem_ball, Real.dist_eq, abs_sub_lt_iff, sub_lt_iff_lt_add', and_comm, sub_lt] <;> rfl

theorem Real.Ioo_eq_ball (x y : ℝ) : Ioo x y = ball ((x+y) / 2) ((y - x) / 2) :=
  by 
    rw [Real.ball_eq_Ioo, ←sub_div, add_commₓ, ←sub_add, add_sub_cancel', add_self_div_two, ←add_div, add_assocₓ,
      add_sub_cancel'_right, add_self_div_two]

-- error in Topology.Instances.Real: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : complete_space exprℝ() :=
begin
  apply [expr complete_of_cauchy_seq_tendsto],
  intros [ident u, ident hu],
  let [ident c] [":", expr cau_seq exprℝ() abs] [":=", expr ⟨u, metric.cauchy_seq_iff'.1 hu⟩],
  refine [expr ⟨c.lim, λ s h, _⟩],
  rcases [expr metric.mem_nhds_iff.1 h, "with", "⟨", ident ε, ",", ident ε0, ",", ident hε, "⟩"],
  have [] [] [":=", expr c.equiv_lim ε ε0],
  simp [] [] ["only"] ["[", expr mem_map, ",", expr mem_at_top_sets, ",", expr mem_set_of_eq, "]"] [] [],
  refine [expr this.imp (λ N hN n hn, hε (hN n hn))]
end

theorem Real.totally_bounded_ball (x ε : ℝ) : TotallyBounded (ball x ε) :=
  by 
    rw [Real.ball_eq_Ioo] <;> apply totally_bounded_Ioo

-- error in Topology.Instances.Real: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem rat.totally_bounded_Icc (a b : exprℚ()) : totally_bounded (Icc a b) :=
begin
  have [] [] [":=", expr totally_bounded_preimage rat.uniform_embedding_coe_real (totally_bounded_Icc a b)],
  rwa [expr (set.ext (λ q, _) : «expr = »(Icc _ _, _))] [],
  simp [] [] [] [] [] []
end

section 

theorem closure_of_rat_image_lt {q : ℚ} : Closure ((coeₓ : ℚ → ℝ) '' { x | q < x }) = { r | «expr↑ » q ≤ r } :=
  subset.antisymm
      ((is_closed_ge' _).closure_subset_iff.2 (image_subset_iff.2$ fun p h => le_of_ltₓ$ (@Rat.cast_lt ℝ _ _ _).2 h))$
    fun x hx =>
      mem_closure_iff_nhds.2$
        fun t ht =>
          let ⟨ε, ε0, hε⟩ := Metric.mem_nhds_iff.1 ht 
          let ⟨p, h₁, h₂⟩ := exists_rat_btwn ((lt_add_iff_pos_right x).2 ε0)
          ⟨_,
            hε
              (show abs _ < _ by 
                rwa [abs_of_nonneg (le_of_ltₓ$ sub_pos.2 h₁), sub_lt_iff_lt_add']),
            p, Rat.cast_lt.1 (@lt_of_le_of_ltₓ ℝ _ _ _ _ hx h₁), rfl⟩

theorem Real.bounded_iff_bdd_below_bdd_above {s : Set ℝ} : Bounded s ↔ BddBelow s ∧ BddAbove s :=
  ⟨by 
      intro bdd 
      rcases(bounded_iff_subset_ball 0).1 bdd with ⟨r, hr⟩
      rw [Real.closed_ball_eq] at hr 
      exact ⟨bdd_below_Icc.mono hr, bdd_above_Icc.mono hr⟩,
    by 
      intro h 
      rcases bdd_below_bdd_above_iff_subset_Icc.1 h with ⟨m, M, I : s ⊆ Icc m M⟩
      exact (bounded_Icc m M).mono I⟩

theorem Real.subset_Icc_Inf_Sup_of_bounded {s : Set ℝ} (h : Bounded s) : s ⊆ Icc (Inf s) (Sup s) :=
  subset_Icc_cInf_cSup (Real.bounded_iff_bdd_below_bdd_above.1 h).1 (Real.bounded_iff_bdd_below_bdd_above.1 h).2

end 

section Periodic

namespace Function

theorem periodic.compact_of_continuous' [TopologicalSpace α] {f : ℝ → α} {c : ℝ} (hp : periodic f c) (hc : 0 < c)
  (hf : Continuous f) : IsCompact (range f) :=
  by 
    convert is_compact_Icc.image hf 
    ext x 
    refine' ⟨_, mem_range_of_mem_image f (Icc 0 c)⟩
    rintro ⟨y, h1⟩
    obtain ⟨z, hz, h2⟩ := hp.exists_mem_Ico₀ hc y 
    exact ⟨z, mem_Icc_of_Ico hz, h2.symm.trans h1⟩

/-- A continuous, periodic function has compact range. -/
theorem periodic.compact_of_continuous [TopologicalSpace α] {f : ℝ → α} {c : ℝ} (hp : periodic f c) (hc : c ≠ 0)
  (hf : Continuous f) : IsCompact (range f) :=
  by 
    cases' lt_or_gt_of_neₓ hc with hneg hpos 
    exacts[hp.neg.compact_of_continuous' (neg_pos.mpr hneg) hf, hp.compact_of_continuous' hpos hf]

/-- A continuous, periodic function is bounded. -/
theorem periodic.bounded_of_continuous [PseudoMetricSpace α] {f : ℝ → α} {c : ℝ} (hp : periodic f c) (hc : c ≠ 0)
  (hf : Continuous f) : Bounded (range f) :=
  (hp.compact_of_continuous hc hf).Bounded

end Function

end Periodic

section Subgroups

-- error in Topology.Instances.Real: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a nontrivial subgroup `G ⊆ ℝ`, if `G ∩ ℝ_{>0}` has no minimum then `G` is dense. -/
theorem real.subgroup_dense_of_no_min
{G : add_subgroup exprℝ()}
{g₀ : exprℝ()}
(g₀_in : «expr ∈ »(g₀, G))
(g₀_ne : «expr ≠ »(g₀, 0))
(H' : «expr¬ »(«expr∃ , »((a : exprℝ()), is_least {g : exprℝ() | «expr ∧ »(«expr ∈ »(g, G), «expr < »(0, g))} a))) : dense (G : set exprℝ()) :=
begin
  let [ident G_pos] [] [":=", expr {g : exprℝ() | «expr ∧ »(«expr ∈ »(g, G), «expr < »(0, g))}],
  push_neg ["at", ident H'],
  intros [ident x],
  suffices [] [":", expr ∀
   ε «expr > » (0 : exprℝ()), «expr∃ , »((g «expr ∈ » G), «expr < »(«expr| |»(«expr - »(x, g)), ε))],
  by simpa [] [] ["only"] ["[", expr real.mem_closure_iff, ",", expr abs_sub_comm, "]"] [] [],
  intros [ident ε, ident ε_pos],
  obtain ["⟨", ident g₁, ",", ident g₁_in, ",", ident g₁_pos, "⟩", ":", expr «expr∃ , »((g₁ : exprℝ()), «expr ∧ »(«expr ∈ »(g₁, G), «expr < »(0, g₁)))],
  { cases [expr lt_or_gt_of_ne g₀_ne] ["with", ident Hg₀, ident Hg₀],
    { exact [expr ⟨«expr- »(g₀), G.neg_mem g₀_in, neg_pos.mpr Hg₀⟩] },
    { exact [expr ⟨g₀, g₀_in, Hg₀⟩] } },
  obtain ["⟨", ident a, ",", ident ha, "⟩", ":", expr «expr∃ , »((a), is_glb G_pos a), ":=", expr ⟨Inf G_pos, is_glb_cInf ⟨g₁, g₁_in, g₁_pos⟩ ⟨0, λ
     _ hx, le_of_lt hx.2⟩⟩],
  have [ident a_notin] [":", expr «expr ∉ »(a, G_pos)] [],
  { intros [ident H],
    exact [expr H' a ⟨H, ha.1⟩] },
  obtain ["⟨", ident g₂, ",", ident g₂_in, ",", ident g₂_pos, ",", ident g₂_lt, "⟩", ":", expr «expr∃ , »((g₂ : exprℝ()), «expr ∧ »(«expr ∈ »(g₂, G), «expr ∧ »(«expr < »(0, g₂), «expr < »(g₂, ε))))],
  { obtain ["⟨", ident b, ",", ident hb, ",", ident hb', ",", ident hb'', "⟩", ":=", expr ha.exists_between_self_add' a_notin ε_pos],
    obtain ["⟨", ident c, ",", ident hc, ",", ident hc', ",", ident hc'', "⟩", ":=", expr ha.exists_between_self_add' a_notin (sub_pos.2 hb')],
    refine [expr ⟨«expr - »(b, c), G.sub_mem hb.1 hc.1, _, _⟩]; linarith [] [] [] },
  refine [expr ⟨«expr * »(floor «expr / »(x, g₂), g₂), _, _⟩],
  { exact [expr add_subgroup.int_mul_mem _ g₂_in] },
  { rw [expr abs_of_nonneg (sub_floor_div_mul_nonneg x g₂_pos)] [],
    linarith [] [] ["[", expr sub_floor_div_mul_lt x g₂_pos, "]"] }
end

/-- Subgroups of `ℝ` are either dense or cyclic. See `real.subgroup_dense_of_no_min` and
`subgroup_cyclic_of_min` for more precise statements. -/
theorem Real.subgroup_dense_or_cyclic (G : AddSubgroup ℝ) : Dense (G : Set ℝ) ∨ ∃ a : ℝ, G = AddSubgroup.closure {a} :=
  by 
    cases' AddSubgroup.bot_or_exists_ne_zero G with H H
    ·
      right 
      use 0
      rw [H, AddSubgroup.closure_singleton_zero]
    ·
      let G_pos := { g:ℝ | g ∈ G ∧ 0 < g }
      byCases' H' : ∃ a, IsLeast G_pos a
      ·
        right 
        rcases H' with ⟨a, ha⟩
        exact ⟨a, AddSubgroup.cyclic_of_min ha⟩
      ·
        left 
        rcases H with ⟨g₀, g₀_in, g₀_ne⟩
        exact Real.subgroup_dense_of_no_min g₀_in g₀_ne H'

end Subgroups

