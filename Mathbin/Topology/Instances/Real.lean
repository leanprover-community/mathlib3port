/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Topology.MetricSpace.Basic
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.Algebra.Ring
import Mathbin.RingTheory.Subring.Basic
import Mathbin.GroupTheory.Archimedean
import Mathbin.Algebra.Periodic
import Mathbin.Order.Filter.Archimedean

/-!
# Topological properties of ℝ
-/


noncomputable section

open Classical Filter Int Metric Set TopologicalSpace

open_locale Classical TopologicalSpace Filter uniformity Interval

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

instance : MetricSpace ℚ :=
  MetricSpace.induced coe Rat.cast_injective Real.metricSpace

namespace Rat

theorem dist_eq (x y : ℚ) : dist x y = abs (x - y) :=
  rfl

@[norm_cast, simp]
theorem dist_cast (x y : ℚ) : dist (x : ℝ) y = dist x y :=
  rfl

theorem uniform_continuous_coe_real : UniformContinuous (coe : ℚ → ℝ) :=
  uniform_continuous_comap

theorem uniform_embedding_coe_real : UniformEmbedding (coe : ℚ → ℝ) :=
  uniform_embedding_comap Rat.cast_injective

theorem dense_embedding_coe_real : DenseEmbedding (coe : ℚ → ℝ) :=
  uniform_embedding_coe_real.DenseEmbedding fun x =>
    mem_closure_iff_nhds.2 fun t ht =>
      let ⟨ε, ε0, hε⟩ := Metric.mem_nhds_iff.1 ht
      let ⟨q, h⟩ := exists_rat_near x ε0
      ⟨_, hε (mem_ball'.2 h), q, rfl⟩

theorem embedding_coe_real : Embedding (coe : ℚ → ℝ) :=
  dense_embedding_coe_real.toEmbedding

theorem continuous_coe_real : Continuous (coe : ℚ → ℝ) :=
  uniform_continuous_coe_real.Continuous

end Rat

namespace Int

instance : HasDist ℤ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℤ) : dist x y = abs (x - y) :=
  rfl

@[norm_cast, simp]
theorem dist_cast_real (x y : ℤ) : dist (x : ℝ) y = dist x y :=
  rfl

@[norm_cast, simp]
theorem dist_cast_rat (x y : ℤ) : dist (x : ℚ) y = dist x y := by
  rw [← Int.dist_cast_real, ← Rat.dist_cast] <;> congr 1 <;> norm_cast

theorem pairwise_one_le_dist : Pairwise fun m n : ℤ => 1 ≤ dist m n := by
  intro m n hne
  rw [dist_eq]
  norm_cast
  rwa [← zero_addₓ (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]

theorem uniform_embedding_coe_rat : UniformEmbedding (coe : ℤ → ℚ) :=
  uniform_embedding_bot_of_pairwise_le_dist zero_lt_one <| by
    simpa using pairwise_one_le_dist

theorem closed_embedding_coe_rat : ClosedEmbedding (coe : ℤ → ℚ) :=
  closed_embedding_of_pairwise_le_dist zero_lt_one <| by
    simpa using pairwise_one_le_dist

theorem uniform_embedding_coe_real : UniformEmbedding (coe : ℤ → ℝ) :=
  uniform_embedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

theorem closed_embedding_coe_real : ClosedEmbedding (coe : ℤ → ℝ) :=
  closed_embedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

instance : MetricSpace ℤ :=
  Int.uniform_embedding_coe_real.comapMetricSpace _

theorem preimage_ball (x : ℤ) (r : ℝ) : coe ⁻¹' Ball (x : ℝ) r = Ball x r :=
  rfl

theorem preimage_closed_ball (x : ℤ) (r : ℝ) : coe ⁻¹' ClosedBall (x : ℝ) r = ClosedBall x r :=
  rfl

theorem ball_eq_Ioo (x : ℤ) (r : ℝ) : Ball x r = Ioo ⌊↑x - r⌋ ⌈↑x + r⌉ := by
  rw [← preimage_ball, Real.ball_eq_Ioo, preimage_Ioo]

theorem closed_ball_eq_Icc (x : ℤ) (r : ℝ) : ClosedBall x r = Icc ⌈↑x - r⌉ ⌊↑x + r⌋ := by
  rw [← preimage_closed_ball, Real.closed_ball_eq_Icc, preimage_Icc]

instance : ProperSpace ℤ :=
  ⟨by
    intro x r
    rw [closed_ball_eq_Icc]
    exact (Set.finite_Icc _ _).IsCompact⟩

@[simp]
theorem cocompact_eq : cocompact ℤ = at_bot⊔at_top := by
  simp only [← comap_dist_right_at_top_eq_cocompact (0 : ℤ), dist_eq, sub_zero, cast_zero, ← cast_abs, ←
    @comap_comap _ _ _ _ abs, Int.comap_coe_at_top, comap_abs_at_top]

@[simp]
theorem cofinite_eq : (cofinite : Filter ℤ) = at_bot⊔at_top := by
  rw [← cocompact_eq_cofinite, cocompact_eq]

end Int

namespace Nat

instance : HasDist ℕ :=
  ⟨fun x y => dist (x : ℝ) y⟩

theorem dist_eq (x y : ℕ) : dist x y = abs (x - y) :=
  rfl

theorem dist_coe_int (x y : ℕ) : dist (x : ℤ) (y : ℤ) = dist x y :=
  rfl

@[norm_cast, simp]
theorem dist_cast_real (x y : ℕ) : dist (x : ℝ) y = dist x y :=
  rfl

@[norm_cast, simp]
theorem dist_cast_rat (x y : ℕ) : dist (x : ℚ) y = dist x y := by
  rw [← Nat.dist_cast_real, ← Rat.dist_cast] <;> congr 1 <;> norm_cast

theorem pairwise_one_le_dist : Pairwise fun m n : ℕ => 1 ≤ dist m n := by
  intro m n hne
  rw [← dist_coe_int]
  apply Int.pairwise_one_le_dist
  exact_mod_cast hne

theorem uniform_embedding_coe_rat : UniformEmbedding (coe : ℕ → ℚ) :=
  uniform_embedding_bot_of_pairwise_le_dist zero_lt_one <| by
    simpa using pairwise_one_le_dist

theorem closed_embedding_coe_rat : ClosedEmbedding (coe : ℕ → ℚ) :=
  closed_embedding_of_pairwise_le_dist zero_lt_one <| by
    simpa using pairwise_one_le_dist

theorem uniform_embedding_coe_real : UniformEmbedding (coe : ℕ → ℝ) :=
  uniform_embedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

theorem closed_embedding_coe_real : ClosedEmbedding (coe : ℕ → ℝ) :=
  closed_embedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist

instance : MetricSpace ℕ :=
  Nat.uniform_embedding_coe_real.comapMetricSpace _

theorem preimage_ball (x : ℕ) (r : ℝ) : coe ⁻¹' Ball (x : ℝ) r = Ball x r :=
  rfl

theorem preimage_closed_ball (x : ℕ) (r : ℝ) : coe ⁻¹' ClosedBall (x : ℝ) r = ClosedBall x r :=
  rfl

theorem closed_ball_eq_Icc (x : ℕ) (r : ℝ) : ClosedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊ := by
  rcases le_or_ltₓ 0 r with (hr | hr)
  · rw [← preimage_closed_ball, Real.closed_ball_eq_Icc, preimage_Icc]
    exact add_nonneg (cast_nonneg x) hr
    
  · rw [closed_ball_eq_empty.2 hr]
    apply (Icc_eq_empty _).symm
    rw [not_leₓ]
    calc ⌊(x : ℝ) + r⌋₊ ≤ ⌊(x : ℝ)⌋₊ := by
        apply floor_mono
        linarith _ < ⌈↑x - r⌉₊ := by
        rw [floor_coe, Nat.lt_ceil]
        linarith
    

instance : ProperSpace ℕ :=
  ⟨by
    intro x r
    rw [closed_ball_eq_Icc]
    exact (Set.finite_Icc _ _).IsCompact⟩

instance : NoncompactSpace ℕ :=
  noncompact_space_of_ne_bot <| by
    simp [at_top_ne_bot]

end Nat

instance : NoncompactSpace ℚ :=
  Int.closed_embedding_coe_rat.NoncompactSpace

instance : NoncompactSpace ℝ :=
  Int.closed_embedding_coe_real.NoncompactSpace

theorem Real.uniform_continuous_add : UniformContinuous fun p : ℝ × ℝ => p.1 + p.2 :=
  Metric.uniform_continuous_iff.2 fun ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0
    ⟨δ, δ0, fun a b h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ h₁ h₂⟩

-- TODO(Mario): Find a way to use rat_add_continuous_lemma
theorem Rat.uniform_continuous_add : UniformContinuous fun p : ℚ × ℚ => p.1 + p.2 :=
  Rat.uniform_embedding_coe_real.to_uniform_inducing.uniform_continuous_iff.2 <| by
    simp only [(· ∘ ·), Rat.cast_add] <;>
      exact real.uniform_continuous_add.comp (rat.uniform_continuous_coe_real.prod_map Rat.uniform_continuous_coe_real)

theorem Real.uniform_continuous_neg : UniformContinuous (@Neg.neg ℝ _) :=
  Metric.uniform_continuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun a b h => by
      rw [dist_comm] at h <;> simpa [Real.dist_eq] using h⟩

theorem Rat.uniform_continuous_neg : UniformContinuous (@Neg.neg ℚ _) :=
  Metric.uniform_continuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun a b h => by
      rw [dist_comm] at h <;> simpa [Rat.dist_eq] using h⟩

instance : UniformAddGroup ℝ :=
  UniformAddGroup.mk' Real.uniform_continuous_add Real.uniform_continuous_neg

instance : UniformAddGroup ℚ :=
  UniformAddGroup.mk' Rat.uniform_continuous_add Rat.uniform_continuous_neg

-- short-circuit type class inference
instance : TopologicalAddGroup ℝ := by
  infer_instance

instance : TopologicalAddGroup ℚ := by
  infer_instance

instance : OrderTopology ℚ :=
  induced_order_topology _ (fun x y => Rat.cast_lt) (@exists_rat_btwn _ _ _)

instance : ProperSpace ℝ where
  is_compact_closed_ball := fun x r => by
    rw [Real.closed_ball_eq_Icc]
    apply is_compact_Icc

instance : SecondCountableTopology ℝ :=
  second_countable_of_proper

-- ././Mathport/Syntax/Translate/Basic.lean:746:6: warning: expanding binder group (a b)
theorem Real.is_topological_basis_Ioo_rat : @IsTopologicalBasis ℝ _ (⋃ (a : ℚ) (b : ℚ) (h : a < b), {Ioo a b}) :=
  is_topological_basis_of_open_of_nhds
    (by
      simp (config := { contextual := true })[is_open_Ioo])
    fun a v hav hv =>
    let ⟨l, u, ⟨hl, hu⟩, h⟩ := mem_nhds_iff_exists_Ioo_subset.mp (IsOpen.mem_nhds hv hav)
    let ⟨q, hlq, hqa⟩ := exists_rat_btwn hl
    let ⟨p, hap, hpu⟩ := exists_rat_btwn hu
    ⟨Ioo q p, by
      simp only [mem_Union]
      exact ⟨q, p, Rat.cast_lt.1 <| hqa.trans hap, rfl⟩, ⟨hqa, hap⟩, fun a' ⟨hqa', ha'p⟩ =>
      h ⟨hlq.trans hqa', ha'p.trans hpu⟩⟩

@[simp]
theorem Real.cocompact_eq : cocompact ℝ = at_bot⊔at_top := by
  simp only [← comap_dist_right_at_top_eq_cocompact (0 : ℝ), Real.dist_eq, sub_zero, comap_abs_at_top]

/- TODO(Mario): Prove that these are uniform isomorphisms instead of uniform embeddings
lemma uniform_embedding_add_rat {r : ℚ} : uniform_embedding (λp:ℚ, p + r) :=
_

lemma uniform_embedding_mul_rat {q : ℚ} (hq : q ≠ 0) : uniform_embedding ((*) q) :=
_ -/
theorem Real.mem_closure_iff {s : Set ℝ} {x : ℝ} : x ∈ Closure s ↔ ∀, ∀ ε > 0, ∀, ∃ y ∈ s, abs (y - x) < ε := by
  simp [mem_closure_iff_nhds_basis nhds_basis_ball, Real.dist_eq]

theorem Real.uniform_continuous_inv (s : Set ℝ) {r : ℝ} (r0 : 0 < r) (H : ∀, ∀ x ∈ s, ∀, r ≤ abs x) :
    UniformContinuous fun p : s => p.1⁻¹ :=
  Metric.uniform_continuous_iff.2 fun ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_inv_continuous_lemma abs ε0 r0
    ⟨δ, δ0, fun a b h => Hδ (H _ a.2) (H _ b.2) h⟩

theorem Real.uniform_continuous_abs : UniformContinuous (abs : ℝ → ℝ) :=
  Metric.uniform_continuous_iff.2 fun ε ε0 => ⟨ε, ε0, fun a b => lt_of_le_of_ltₓ (abs_abs_sub_abs_le_abs_sub _ _)⟩

theorem Rat.uniform_continuous_abs : UniformContinuous (abs : ℚ → ℚ) :=
  Metric.uniform_continuous_iff.2 fun ε ε0 =>
    ⟨ε, ε0, fun a b h =>
      lt_of_le_of_ltₓ
        (by
          simpa [Rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _)
        h⟩

theorem Real.tendsto_inv {r : ℝ} (r0 : r ≠ 0) : Tendsto (fun q => q⁻¹) (𝓝 r) (𝓝 r⁻¹) := by
  rw [← abs_pos] at r0 <;>
    exact
      tendsto_of_uniform_continuous_subtype
        (Real.uniform_continuous_inv { x | abs r / 2 < abs x } (half_pos r0) fun x h => le_of_ltₓ h)
        (IsOpen.mem_nhds ((is_open_lt' (abs r / 2)).Preimage continuous_abs) (half_lt_self r0))

theorem Real.continuous_inv : Continuous fun a : { r : ℝ // r ≠ 0 } => a.val⁻¹ :=
  continuous_iff_continuous_at.mpr fun ⟨r, hr⟩ =>
    Tendsto.comp (Real.tendsto_inv hr) (continuous_iff_continuous_at.mp continuous_subtype_val _)

theorem Real.Continuous.inv [TopologicalSpace α] {f : α → ℝ} (h : ∀ a, f a ≠ 0) (hf : Continuous f) :
    Continuous fun a => (f a)⁻¹ :=
  show Continuous ((Inv.inv ∘ @Subtype.val ℝ fun r => r ≠ 0) ∘ fun a => ⟨f a, h a⟩) from
    Real.continuous_inv.comp (continuous_subtype_mk _ hf)

theorem Real.uniform_continuous_mul_const {x : ℝ} : UniformContinuous ((· * ·) x) :=
  Metric.uniform_continuous_iff.2 fun ε ε0 => by
    cases' exists_gt (abs x) with y xy
    have y0 := lt_of_le_of_ltₓ (abs_nonneg _) xy
    refine' ⟨_, div_pos ε0 y0, fun a b h => _⟩
    rw [Real.dist_eq, ← mul_sub, abs_mul, ← mul_div_cancel' ε (ne_of_gtₓ y0)]
    exact mul_lt_mul' (le_of_ltₓ xy) h (abs_nonneg _) y0

theorem Real.uniform_continuous_mul (s : Set (ℝ × ℝ)) {r₁ r₂ : ℝ}
    (H : ∀, ∀ x ∈ s, ∀, abs (x : ℝ × ℝ).1 < r₁ ∧ abs x.2 < r₂) : UniformContinuous fun p : s => p.1.1 * p.1.2 :=
  Metric.uniform_continuous_iff.2 fun ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_mul_continuous_lemma abs ε0
    ⟨δ, δ0, fun a b h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ (H _ a.2).1 (H _ b.2).2 h₁ h₂⟩

protected theorem Real.continuous_mul : Continuous fun p : ℝ × ℝ => p.1 * p.2 :=
  continuous_iff_continuous_at.2 fun ⟨a₁, a₂⟩ =>
    tendsto_of_uniform_continuous_subtype
      (Real.uniform_continuous_mul ({ x | abs x < abs a₁ + 1 } ×ˢ { x | abs x < abs a₂ + 1 }) fun x => id)
      (IsOpen.mem_nhds
        (((is_open_gt' (abs a₁ + 1)).Preimage continuous_abs).Prod ((is_open_gt' (abs a₂ + 1)).Preimage continuous_abs))
        ⟨lt_add_one (abs a₁), lt_add_one (abs a₂)⟩)

instance : TopologicalRing ℝ :=
  { Real.topological_add_group with continuous_mul := Real.continuous_mul }

theorem Rat.continuous_mul : Continuous fun p : ℚ × ℚ => p.1 * p.2 :=
  Rat.embedding_coe_real.continuous_iff.2 <| by
    simp [(· ∘ ·)] <;> exact real.continuous_mul.comp (rat.continuous_coe_real.prod_map Rat.continuous_coe_real)

instance : TopologicalRing ℚ :=
  { Rat.topological_add_group with continuous_mul := Rat.continuous_mul }

instance : CompleteSpace ℝ := by
  apply complete_of_cauchy_seq_tendsto
  intro u hu
  let c : CauSeq ℝ abs := ⟨u, Metric.cauchy_seq_iff'.1 hu⟩
  refine' ⟨c.lim, fun s h => _⟩
  rcases Metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩
  have := c.equiv_lim ε ε0
  simp only [mem_map, mem_at_top_sets, mem_set_of_eq]
  refine' this.imp fun N hN n hn => hε (hN n hn)

theorem Real.totally_bounded_ball (x ε : ℝ) : TotallyBounded (Ball x ε) := by
  rw [Real.ball_eq_Ioo] <;> apply totally_bounded_Ioo

theorem Rat.totally_bounded_Icc (a b : ℚ) : TotallyBounded (Icc a b) := by
  have := totally_bounded_preimage Rat.uniform_embedding_coe_real (totally_bounded_Icc a b)
  rwa [(Set.ext fun q => _ : Icc _ _ = _)]
  simp

section

theorem closure_of_rat_image_lt {q : ℚ} : Closure ((coe : ℚ → ℝ) '' { x | q < x }) = { r | ↑q ≤ r } :=
  (Subset.antisymm
      ((is_closed_ge' _).closure_subset_iff.2 (image_subset_iff.2 fun p h => le_of_ltₓ <| (@Rat.cast_lt ℝ _ _ _).2 h)))
    fun x hx =>
    mem_closure_iff_nhds.2 fun t ht =>
      let ⟨ε, ε0, hε⟩ := Metric.mem_nhds_iff.1 ht
      let ⟨p, h₁, h₂⟩ := exists_rat_btwn ((lt_add_iff_pos_right x).2 ε0)
      ⟨_,
        hε
          (show abs _ < _ by
            rwa [abs_of_nonneg (le_of_ltₓ <| sub_pos.2 h₁), sub_lt_iff_lt_add']),
        p, Rat.cast_lt.1 (@lt_of_le_of_ltₓ ℝ _ _ _ _ hx h₁), rfl⟩

/- TODO(Mario): Put these back only if needed later
lemma closure_of_rat_image_le_eq {q : ℚ} : closure ((coe:ℚ → ℝ) '' {x | q ≤ x}) = {r | ↑q ≤ r} :=
_

lemma closure_of_rat_image_le_le_eq {a b : ℚ} (hab : a ≤ b) :
  closure (of_rat '' {q:ℚ | a ≤ q ∧ q ≤ b}) = {r:ℝ | of_rat a ≤ r ∧ r ≤ of_rat b} :=
_-/
theorem Real.bounded_iff_bdd_below_bdd_above {s : Set ℝ} : Bounded s ↔ BddBelow s ∧ BddAbove s :=
  ⟨by
    intro bdd
    rcases(bounded_iff_subset_ball 0).1 bdd with ⟨r, hr⟩
    -- hr : s ⊆ closed_ball 0 r
    rw [Real.closed_ball_eq_Icc] at hr
    -- hr : s ⊆ Icc (0 - r) (0 + r)
    exact ⟨bdd_below_Icc.mono hr, bdd_above_Icc.mono hr⟩,
    fun h => bounded_of_bdd_above_of_bdd_below h.2 h.1⟩

theorem Real.subset_Icc_Inf_Sup_of_bounded {s : Set ℝ} (h : Bounded s) : s ⊆ Icc (inf s) (sup s) :=
  subset_Icc_cInf_cSup (Real.bounded_iff_bdd_below_bdd_above.1 h).1 (Real.bounded_iff_bdd_below_bdd_above.1 h).2

end

section Periodic

namespace Function

theorem Periodic.compact_of_continuous' [TopologicalSpace α] {f : ℝ → α} {c : ℝ} (hp : Periodic f c) (hc : 0 < c)
    (hf : Continuous f) : IsCompact (Range f) := by
  convert is_compact_Icc.image hf
  ext x
  refine' ⟨_, mem_range_of_mem_image f (Icc 0 c)⟩
  rintro ⟨y, h1⟩
  obtain ⟨z, hz, h2⟩ := hp.exists_mem_Ico₀ hc y
  exact ⟨z, mem_Icc_of_Ico hz, h2.symm.trans h1⟩

/-- A continuous, periodic function has compact range. -/
theorem Periodic.compact_of_continuous [TopologicalSpace α] {f : ℝ → α} {c : ℝ} (hp : Periodic f c) (hc : c ≠ 0)
    (hf : Continuous f) : IsCompact (Range f) := by
  cases' lt_or_gt_of_neₓ hc with hneg hpos
  exacts[hp.neg.compact_of_continuous' (neg_pos.mpr hneg) hf, hp.compact_of_continuous' hpos hf]

/-- A continuous, periodic function is bounded. -/
theorem Periodic.bounded_of_continuous [PseudoMetricSpace α] {f : ℝ → α} {c : ℝ} (hp : Periodic f c) (hc : c ≠ 0)
    (hf : Continuous f) : Bounded (Range f) :=
  (hp.compact_of_continuous hc hf).Bounded

end Function

end Periodic

section Subgroups

/-- Given a nontrivial subgroup `G ⊆ ℝ`, if `G ∩ ℝ_{>0}` has no minimum then `G` is dense. -/
theorem Real.subgroup_dense_of_no_min {G : AddSubgroup ℝ} {g₀ : ℝ} (g₀_in : g₀ ∈ G) (g₀_ne : g₀ ≠ 0)
    (H' : ¬∃ a : ℝ, IsLeast { g : ℝ | g ∈ G ∧ 0 < g } a) : Dense (G : Set ℝ) := by
  let G_pos := { g : ℝ | g ∈ G ∧ 0 < g }
  push_neg  at H'
  intro x
  suffices ∀, ∀ ε > (0 : ℝ), ∀, ∃ g ∈ G, abs (x - g) < ε by
    simpa only [Real.mem_closure_iff, abs_sub_comm]
  intro ε ε_pos
  obtain ⟨g₁, g₁_in, g₁_pos⟩ : ∃ g₁ : ℝ, g₁ ∈ G ∧ 0 < g₁ := by
    cases' lt_or_gt_of_neₓ g₀_ne with Hg₀ Hg₀
    · exact ⟨-g₀, G.neg_mem g₀_in, neg_pos.mpr Hg₀⟩
      
    · exact ⟨g₀, g₀_in, Hg₀⟩
      
  obtain ⟨a, ha⟩ : ∃ a, IsGlb G_pos a := ⟨Inf G_pos, is_glb_cInf ⟨g₁, g₁_in, g₁_pos⟩ ⟨0, fun _ hx => le_of_ltₓ hx.2⟩⟩
  have a_notin : a ∉ G_pos := by
    intro H
    exact H' a ⟨H, ha.1⟩
  obtain ⟨g₂, g₂_in, g₂_pos, g₂_lt⟩ : ∃ g₂ : ℝ, g₂ ∈ G ∧ 0 < g₂ ∧ g₂ < ε := by
    obtain ⟨b, hb, hb', hb''⟩ := ha.exists_between_self_add' a_notin ε_pos
    obtain ⟨c, hc, hc', hc''⟩ := ha.exists_between_self_add' a_notin (sub_pos.2 hb')
    refine' ⟨b - c, G.sub_mem hb.1 hc.1, _, _⟩ <;> linarith
  refine' ⟨floor (x / g₂) * g₂, _, _⟩
  · exact AddSubgroup.int_mul_mem _ g₂_in
    
  · rw [abs_of_nonneg (sub_floor_div_mul_nonneg x g₂_pos)]
    linarith [sub_floor_div_mul_lt x g₂_pos]
    

/-- Subgroups of `ℝ` are either dense or cyclic. See `real.subgroup_dense_of_no_min` and
`subgroup_cyclic_of_min` for more precise statements. -/
theorem Real.subgroup_dense_or_cyclic (G : AddSubgroup ℝ) : Dense (G : Set ℝ) ∨ ∃ a : ℝ, G = AddSubgroup.closure {a} :=
  by
  cases' AddSubgroup.bot_or_exists_ne_zero G with H H
  · right
    use 0
    rw [H, AddSubgroup.closure_singleton_zero]
    
  · let G_pos := { g : ℝ | g ∈ G ∧ 0 < g }
    by_cases' H' : ∃ a, IsLeast G_pos a
    · right
      rcases H' with ⟨a, ha⟩
      exact ⟨a, AddSubgroup.cyclic_of_min ha⟩
      
    · left
      rcases H with ⟨g₀, g₀_in, g₀_ne⟩
      exact Real.subgroup_dense_of_no_min g₀_in g₀_ne H'
      
    

end Subgroups

