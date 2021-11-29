import Mathbin.Topology.MetricSpace.Isometry 
import Mathbin.Topology.ContinuousFunction.Bounded 
import Mathbin.Topology.Compacts

/-!
# The Kuratowski embedding

Any separable metric space can be embedded isometrically in `ℓ^∞(ℝ)`.
-/


noncomputable theory

open Set

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The space of bounded sequences, with its sup norm -/
@[reducible]
def ℓInftyℝ : Type :=
  BoundedContinuousFunction ℕ ℝ

open BoundedContinuousFunction Metric TopologicalSpace

namespace kuratowskiEmbedding

/-! ### Any separable metric space can be embedded isometrically in ℓ^∞(ℝ) -/


variable {f g : ℓInftyℝ} {n : ℕ} {C : ℝ} [MetricSpace α] (x : ℕ → α) (a b : α)

/-- A metric space can be embedded in `l^∞(ℝ)` via the distances to points in
a fixed countable set, if this set is dense. This map is given in `Kuratowski_embedding`,
without density assumptions. -/
def embedding_of_subset : ℓInftyℝ :=
  of_normed_group_discrete (fun n => dist a (x n) - dist (x 0) (x n)) (dist a (x 0)) fun _ => abs_dist_sub_le _ _ _

theorem embedding_of_subset_coe : embedding_of_subset x a n = dist a (x n) - dist (x 0) (x n) :=
  rfl

/-- The embedding map is always a semi-contraction. -/
theorem embedding_of_subset_dist_le (a b : α) : dist (embedding_of_subset x a) (embedding_of_subset x b) ≤ dist a b :=
  by 
    refine' (dist_le dist_nonneg).2 fun n => _ 
    simp only [embedding_of_subset_coe, Real.dist_eq]
    convert abs_dist_sub_le a b (x n) using 2
    ring

-- error in Topology.MetricSpace.Kuratowski: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- When the reference set is dense, the embedding map is an isometry on its image. -/
theorem embedding_of_subset_isometry (H : dense_range x) : isometry (embedding_of_subset x) :=
begin
  refine [expr isometry_emetric_iff_metric.2 (λ a b, _)],
  refine [expr (embedding_of_subset_dist_le x a b).antisymm (le_of_forall_pos_le_add (λ e epos, _))],
  rcases [expr metric.mem_closure_range_iff.1 (H a) «expr / »(e, 2) (half_pos epos), "with", "⟨", ident n, ",", ident hn, "⟩"],
  have [ident C] [":", expr «expr = »(«expr - »(dist b (x n), dist a (x n)), «expr - »(embedding_of_subset x b n, embedding_of_subset x a n))] [":=", expr by { simp [] [] ["only"] ["[", expr embedding_of_subset_coe, ",", expr sub_sub_sub_cancel_right, "]"] [] [] }],
  have [] [] [":=", expr calc
     «expr ≤ »(dist a b, «expr + »(dist a (x n), dist (x n) b)) : dist_triangle _ _ _
     «expr = »(..., «expr + »(«expr * »(2, dist a (x n)), «expr - »(dist b (x n), dist a (x n)))) : by { simp [] [] [] ["[", expr dist_comm, "]"] [] [],
       ring [] }
     «expr ≤ »(..., «expr + »(«expr * »(2, dist a (x n)), «expr| |»(«expr - »(dist b (x n), dist a (x n))))) : by apply_rules ["[", expr add_le_add_left, ",", expr le_abs_self, "]"]
     «expr ≤ »(..., «expr + »(«expr * »(2, «expr / »(e, 2)), «expr| |»(«expr - »(embedding_of_subset x b n, embedding_of_subset x a n)))) : begin
       rw [expr C] [],
       apply_rules ["[", expr add_le_add, ",", expr mul_le_mul_of_nonneg_left, ",", expr hn.le, ",", expr le_refl, "]"],
       norm_num [] []
     end
     «expr ≤ »(..., «expr + »(«expr * »(2, «expr / »(e, 2)), dist (embedding_of_subset x b) (embedding_of_subset x a))) : by simp [] [] [] ["[", "<-", expr real.dist_eq, ",", expr dist_coe_le_dist, "]"] [] []
     «expr = »(..., «expr + »(dist (embedding_of_subset x b) (embedding_of_subset x a), e)) : by ring []],
  simpa [] [] [] ["[", expr dist_comm, "]"] [] ["using", expr this]
end

-- error in Topology.MetricSpace.Kuratowski: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Every separable metric space embeds isometrically in `ℓ_infty_ℝ`. -/
theorem exists_isometric_embedding
(α : Type u)
[metric_space α]
[separable_space α] : «expr∃ , »((f : α → ℓ_infty_ℝ), isometry f) :=
begin
  cases [expr (univ : set α).eq_empty_or_nonempty] ["with", ident h, ident h],
  { use [expr λ _, 0],
    assume [binders (x)],
    exact [expr absurd h (nonempty.ne_empty ⟨x, mem_univ x⟩)] },
  { rcases [expr h, "with", "⟨", ident basepoint, "⟩"],
    haveI [] [":", expr inhabited α] [":=", expr ⟨basepoint⟩],
    have [] [":", expr «expr∃ , »((s : set α), «expr ∧ »(countable s, dense s))] [":=", expr exists_countable_dense α],
    rcases [expr this, "with", "⟨", ident S, ",", "⟨", ident S_countable, ",", ident S_dense, "⟩", "⟩"],
    rcases [expr countable_iff_exists_surjective.1 S_countable, "with", "⟨", ident x, ",", ident x_range, "⟩"],
    exact [expr ⟨embedding_of_subset x, embedding_of_subset_isometry x (S_dense.mono x_range)⟩] }
end

end kuratowskiEmbedding

open TopologicalSpace kuratowskiEmbedding

/-- The Kuratowski embedding is an isometric embedding of a separable metric space in `ℓ^∞(ℝ)`. -/
def kuratowskiEmbedding (α : Type u) [MetricSpace α] [separable_space α] : α → ℓInftyℝ :=
  Classical.some (KuratowskiEmbedding.exists_isometric_embedding α)

/-- The Kuratowski embedding is an isometry. -/
protected theorem kuratowskiEmbedding.isometry (α : Type u) [MetricSpace α] [separable_space α] :
  Isometry (kuratowskiEmbedding α) :=
  Classical.some_spec (exists_isometric_embedding α)

/-- Version of the Kuratowski embedding for nonempty compacts -/
def NonemptyCompacts.kuratowskiEmbedding (α : Type u) [MetricSpace α] [CompactSpace α] [Nonempty α] :
  nonempty_compacts ℓInftyℝ :=
  ⟨range (kuratowskiEmbedding α), range_nonempty _, is_compact_range (kuratowskiEmbedding.isometry α).Continuous⟩

