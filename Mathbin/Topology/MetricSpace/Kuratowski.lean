import Mathbin.Topology.MetricSpace.Isometry
import Mathbin.Topology.ContinuousFunction.Bounded
import Mathbin.Topology.Compacts

/-!
# The Kuratowski embedding

Any separable metric space can be embedded isometrically in `ℓ^∞(ℝ)`.
-/


noncomputable section

open Set

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/--  The space of bounded sequences, with its sup norm -/
@[reducible]
def ℓInftyℝ : Type :=
  BoundedContinuousFunction ℕ ℝ

open BoundedContinuousFunction Metric TopologicalSpace

namespace kuratowskiEmbedding

/-! ### Any separable metric space can be embedded isometrically in ℓ^∞(ℝ) -/


variable {f g : ℓInftyℝ} {n : ℕ} {C : ℝ} [MetricSpace α] (x : ℕ → α) (a b : α)

/--  A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
a fixed countable set, if this set is dense. This map is given in `Kuratowski_embedding`,
without density assumptions. -/
def embedding_of_subset : ℓInftyℝ :=
  of_normed_group_discrete (fun n => dist a (x n) - dist (x 0) (x n)) (dist a (x 0)) fun _ => abs_dist_sub_le _ _ _

theorem embedding_of_subset_coe : embedding_of_subset x a n = dist a (x n) - dist (x 0) (x n) :=
  rfl

/--  The embedding map is always a semi-contraction. -/
theorem embedding_of_subset_dist_le (a b : α) : dist (embedding_of_subset x a) (embedding_of_subset x b) ≤ dist a b :=
  by
  refine' (dist_le dist_nonneg).2 fun n => _
  simp only [embedding_of_subset_coe, Real.dist_eq]
  convert abs_dist_sub_le a b (x n) using 2
  ring

/--  When the reference set is dense, the embedding map is an isometry on its image. -/
theorem embedding_of_subset_isometry (H : DenseRange x) : Isometry (embedding_of_subset x) := by
  refine' isometry_emetric_iff_metric.2 fun a b => _
  refine' (embedding_of_subset_dist_le x a b).antisymm (le_of_forall_pos_le_add fun e epos => _)
  rcases Metric.mem_closure_range_iff.1 (H a) (e / 2) (half_pos epos) with ⟨n, hn⟩
  have C : dist b (x n) - dist a (x n) = embedding_of_subset x b n - embedding_of_subset x a n := by
    simp only [embedding_of_subset_coe, sub_sub_sub_cancel_right]
  have :=
    calc dist a b ≤ dist a (x n)+dist (x n) b := dist_triangle _ _ _
      _ = (2*dist a (x n))+dist b (x n) - dist a (x n) := by
      simp [dist_comm]
      ring
      _ ≤ (2*dist a (x n))+|dist b (x n) - dist a (x n)| := by
      apply_rules [add_le_add_left, le_abs_self]
      _ ≤ (2*e / 2)+|embedding_of_subset x b n - embedding_of_subset x a n| := by
      rw [C]
      apply_rules [add_le_add, mul_le_mul_of_nonneg_left, hn.le, le_reflₓ]
      norm_num
      _ ≤ (2*e / 2)+dist (embedding_of_subset x b) (embedding_of_subset x a) := by
      simp [← Real.dist_eq, dist_coe_le_dist]
      _ = dist (embedding_of_subset x b) (embedding_of_subset x a)+e := by
      ring
      
  simpa [dist_comm] using this

/--  Every separable metric space embeds isometrically in `ℓ_infty_ℝ`. -/
theorem exists_isometric_embedding (α : Type u) [MetricSpace α] [separable_space α] : ∃ f : α → ℓInftyℝ, Isometry f :=
  by
  cases' (univ : Set α).eq_empty_or_nonempty with h h
  ·
    use fun _ => 0
    intro x
    exact absurd h (nonempty.ne_empty ⟨x, mem_univ x⟩)
  ·
    rcases h with ⟨basepoint⟩
    have : Inhabited α := ⟨basepoint⟩
    have : ∃ s : Set α, countable s ∧ Dense s := exists_countable_dense α
    rcases this with ⟨S, ⟨S_countable, S_dense⟩⟩
    rcases countable_iff_exists_surjective.1 S_countable with ⟨x, x_range⟩
    exact ⟨embedding_of_subset x, embedding_of_subset_isometry x (S_dense.mono x_range)⟩

end kuratowskiEmbedding

open TopologicalSpace kuratowskiEmbedding

/--  The Kuratowski embedding is an isometric embedding of a separable metric space in `ℓ^∞(ℝ)`. -/
def kuratowskiEmbedding (α : Type u) [MetricSpace α] [separable_space α] : α → ℓInftyℝ :=
  Classical.some (KuratowskiEmbedding.exists_isometric_embedding α)

/--  The Kuratowski embedding is an isometry. -/
protected theorem kuratowskiEmbedding.isometry (α : Type u) [MetricSpace α] [separable_space α] :
    Isometry (kuratowskiEmbedding α) :=
  Classical.some_spec (exists_isometric_embedding α)

/--  Version of the Kuratowski embedding for nonempty compacts -/
def NonemptyCompacts.kuratowskiEmbedding (α : Type u) [MetricSpace α] [CompactSpace α] [Nonempty α] :
    nonempty_compacts ℓInftyℝ :=
  ⟨range (kuratowskiEmbedding α), range_nonempty _, is_compact_range (kuratowskiEmbedding.isometry α).Continuous⟩

