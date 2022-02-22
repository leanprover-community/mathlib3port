/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot
-/
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.MetricSpace.Basic

/-!
# Sequences in topological spaces

In this file we define sequences in topological spaces and show how they are related to
filters and the topology. In particular, we
* define the sequential closure of a set and prove that it's contained in the closure,
* define a type class "sequential_space" in which closure and sequential closure agree,
* define sequential continuity and show that it coincides with continuity in sequential spaces,
* provide an instance that shows that every first-countable (and in particular metric) space is
  a sequential space.
* define sequential compactness, prove that compactness implies sequential compactness in first
  countable spaces, and prove they are equivalent for uniform spaces having a countable uniformity
  basis (in particular metric spaces).
-/


open Set Filter

open_locale TopologicalSpace

variable {α : Type _} {β : Type _}

-- mathport name: «expr ⟶ »
local notation f " ⟶ " limit => Tendsto f atTop (𝓝 limit)

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/


section TopologicalSpace

variable [TopologicalSpace α] [TopologicalSpace β]

/-- A sequence converges in the sence of topological spaces iff the associated statement for filter
holds. -/
theorem TopologicalSpace.seq_tendsto_iff {x : ℕ → α} {limit : α} :
    Tendsto x atTop (𝓝 limit) ↔ ∀ U : Set α, limit ∈ U → IsOpen U → ∃ N, ∀, ∀ n ≥ N, ∀, x n ∈ U :=
  (at_top_basis.tendsto_iff (nhds_basis_opens limit)).trans <| by
    simp only [and_imp, exists_prop, true_andₓ, Set.mem_Ici, ge_iff_le, id]

/-- The sequential closure of a subset M ⊆ α of a topological space α is
the set of all p ∈ α which arise as limit of sequences in M. -/
def SequentialClosure (M : Set α) : Set α :=
  { p | ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ M) ∧ x ⟶ p }

theorem subset_sequential_closure (M : Set α) : M ⊆ SequentialClosure M := fun _ : p ∈ M =>
  show p ∈ SequentialClosure M from ⟨fun n => p, fun n => ‹p ∈ M›, tendsto_const_nhds⟩

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`,
the limit belongs to `s` as well. -/
def IsSeqClosed (s : Set α) : Prop :=
  s = SequentialClosure s

/-- A convenience lemma for showing that a set is sequentially closed. -/
theorem is_seq_closed_of_def {A : Set α} (h : ∀ x : ℕ → α p : α, (∀ n : ℕ, x n ∈ A) → (x ⟶ p) → p ∈ A) :
    IsSeqClosed A :=
  show A = SequentialClosure A from
    Subset.antisymm (subset_sequential_closure A)
      (show ∀ p, p ∈ SequentialClosure A → p ∈ A from fun p ⟨x, _, _⟩ =>
        show p ∈ A from h x p ‹∀ n : ℕ, x n ∈ A› ‹x ⟶ p›)

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
theorem sequential_closure_subset_closure (M : Set α) : SequentialClosure M ⊆ Closure M := fun p ⟨x, xM, xp⟩ =>
  mem_closure_of_tendsto xp (univ_mem' xM)

/-- A set is sequentially closed if it is closed. -/
theorem is_seq_closed_of_is_closed (M : Set α) (_ : IsClosed M) : IsSeqClosed M :=
  suffices SequentialClosure M ⊆ M from Set.eq_of_subset_of_subset (subset_sequential_closure M) this
  calc
    SequentialClosure M ⊆ Closure M := sequential_closure_subset_closure M
    _ = M := IsClosed.closure_eq ‹IsClosed M›
    

/-- The limit of a convergent sequence in a sequentially closed set is in that set.-/
theorem mem_of_is_seq_closed {A : Set α} (_ : IsSeqClosed A) {x : ℕ → α} (_ : ∀ n, x n ∈ A) {limit : α}
    (_ : x ⟶ limit) : limit ∈ A :=
  have : limit ∈ SequentialClosure A :=
    show ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ A) ∧ x ⟶ limit from ⟨x, ‹∀ n, x n ∈ A›, ‹x ⟶ limit›⟩
  Eq.subst (Eq.symm ‹IsSeqClosed A›) ‹limit ∈ SequentialClosure A›

/-- The limit of a convergent sequence in a closed set is in that set.-/
theorem mem_of_is_closed_sequential {A : Set α} (_ : IsClosed A) {x : ℕ → α} (_ : ∀ n, x n ∈ A) {limit : α}
    (_ : x ⟶ limit) : limit ∈ A :=
  mem_of_is_seq_closed (is_seq_closed_of_is_closed A ‹IsClosed A›) ‹∀ n, x n ∈ A› ‹x ⟶ limit›

/-- A sequential space is a space in which 'sequences are enough to probe the topology'. This can be
 formalised by demanding that the sequential closure and the closure coincide. The following
 statements show that other topological properties can be deduced from sequences in sequential
 spaces. -/
class SequentialSpace (α : Type _) [TopologicalSpace α] : Prop where
  sequential_closure_eq_closure : ∀ M : Set α, SequentialClosure M = Closure M

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
theorem is_seq_closed_iff_is_closed [SequentialSpace α] {M : Set α} : IsSeqClosed M ↔ IsClosed M :=
  Iff.intro
    (fun _ =>
      closure_eq_iff_is_closed.mp
        (Eq.symm
          (calc
            M = SequentialClosure M := by
              assumption
            _ = Closure M := SequentialSpace.sequential_closure_eq_closure M
            )))
    (is_seq_closed_of_is_closed M)

/-- In a sequential space, a point belongs to the closure of a set iff it is a limit of a sequence
taking values in this set. -/
theorem mem_closure_iff_seq_limit [SequentialSpace α] {s : Set α} {a : α} :
    a ∈ Closure s ↔ ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ s) ∧ x ⟶ a := by
  rw [← SequentialSpace.sequential_closure_eq_closure]
  exact Iff.rfl

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def SequentiallyContinuous (f : α → β) : Prop :=
  ∀ x : ℕ → α, ∀ {limit : α}, (x ⟶ limit) → (f ∘ x) ⟶ f limit

-- A continuous function is sequentially continuous.
theorem Continuous.to_sequentially_continuous {f : α → β} (_ : Continuous f) : SequentiallyContinuous f :=
  fun _ : x ⟶ limit =>
  have : Tendsto f (𝓝 limit) (𝓝 (f limit)) := Continuous.tendsto ‹Continuous f› limit
  show (f ∘ x) ⟶ f limit from Tendsto.comp this ‹x ⟶ limit›

/-- In a sequential space, continuity and sequential continuity coincide. -/
theorem continuous_iff_sequentially_continuous {f : α → β} [SequentialSpace α] :
    Continuous f ↔ SequentiallyContinuous f :=
  Iff.intro (fun _ => ‹Continuous f›.to_sequentially_continuous) fun this : SequentiallyContinuous f =>
    show Continuous f from
      suffices h : ∀ {A : Set β}, IsClosed A → IsSeqClosed (f ⁻¹' A) from
        continuous_iff_is_closed.mpr fun A _ => is_seq_closed_iff_is_closed.mp <| h ‹IsClosed A›
      fun _ : IsClosed A =>
      is_seq_closed_of_def fun _ : x ⟶ p =>
        have : (f ∘ x) ⟶ f p := ‹SequentiallyContinuous f› x ‹x ⟶ p›
        show f p ∈ A from mem_of_is_closed_sequential ‹IsClosed A› ‹∀ n, f (x n) ∈ A› ‹(f ∘ x) ⟶ f p›

end TopologicalSpace

namespace TopologicalSpace

namespace FirstCountableTopology

variable [TopologicalSpace α] [FirstCountableTopology α]

/-- Every first-countable space is sequential. -/
-- see Note [lower instance priority]
instance (priority := 100) : SequentialSpace α :=
  ⟨show ∀ M, SequentialClosure M = Closure M from fun M =>
      suffices Closure M ⊆ SequentialClosure M from Set.Subset.antisymm (sequential_closure_subset_closure M) this
      -- For every p ∈ closure M, we need to construct a sequence x in M that converges to p:
    fun hp : p ∈ Closure M =>
      -- Since we are in a first-countable space, the neighborhood filter around `p` has a decreasing
    -- basis `U` indexed by `ℕ`.
    by
      let ⟨U, hU⟩ := (𝓝 p).exists_antitone_basis
      -- Since `p ∈ closure M`, there is an element in each `M ∩ U i`
      have hp : ∀ i : ℕ, ∃ y : α, y ∈ M ∧ y ∈ U i := by
        simpa using (mem_closure_iff_nhds_basis hU.1).mp hp
      -- The axiom of (countable) choice builds our sequence from the later fact
      choose u hu using hp
      rw [forall_and_distrib] at hu
      -- It clearly takes values in `M`
      use u, hu.1
      -- and converges to `p` because the basis is decreasing.
      apply hU.tendsto hu.2⟩

end FirstCountableTopology

end TopologicalSpace

section SeqCompact

open TopologicalSpace TopologicalSpace.FirstCountableTopology

variable [TopologicalSpace α]

/-- A set `s` is sequentially compact if every sequence taking values in `s` has a
converging subsequence. -/
def IsSeqCompact (s : Set α) :=
  ∀ ⦃u : ℕ → α⦄, (∀ n, u n ∈ s) → ∃ x ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x)

/-- A space `α` is sequentially compact if every sequence in `α` has a
converging subsequence. -/
class SeqCompactSpace (α : Type _) [TopologicalSpace α] : Prop where
  seq_compact_univ : IsSeqCompact (Univ : Set α)

theorem IsSeqCompact.subseq_of_frequently_in {s : Set α} (hs : IsSeqCompact s) {u : ℕ → α}
    (hu : ∃ᶠ n in at_top, u n ∈ s) : ∃ x ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) :=
  let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_at_top hu
  let ⟨x, x_in, φ, hφ, h⟩ := hs huψ
  ⟨x, x_in, ψ ∘ φ, hψ.comp hφ, h⟩

theorem SeqCompactSpace.tendsto_subseq [SeqCompactSpace α] (u : ℕ → α) :
    ∃ (x : _)(φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) :=
  let ⟨x, _, φ, mono, h⟩ :=
    SeqCompactSpace.seq_compact_univ
      (by
        simp : ∀ n, u n ∈ univ)
  ⟨x, φ, mono, h⟩

section FirstCountableTopology

variable [FirstCountableTopology α]

open TopologicalSpace.FirstCountableTopology

theorem IsCompact.is_seq_compact {s : Set α} (hs : IsCompact s) : IsSeqCompact s := fun u u_in =>
  let ⟨x, x_in, hx⟩ := @hs (map u atTop) _ (le_principal_iff.mpr (univ_mem' u_in : _))
  ⟨x, x_in, tendsto_subseq hx⟩

theorem IsCompact.tendsto_subseq' {s : Set α} {u : ℕ → α} (hs : IsCompact s) (hu : ∃ᶠ n in at_top, u n ∈ s) :
    ∃ x ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) :=
  hs.IsSeqCompact.subseq_of_frequently_in hu

theorem IsCompact.tendsto_subseq {s : Set α} {u : ℕ → α} (hs : IsCompact s) (hu : ∀ n, u n ∈ s) :
    ∃ x ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) :=
  hs.IsSeqCompact hu

-- see Note [lower instance priority]
instance (priority := 100) FirstCountableTopology.seq_compact_of_compact [CompactSpace α] : SeqCompactSpace α :=
  ⟨compact_univ.IsSeqCompact⟩

theorem CompactSpace.tendsto_subseq [CompactSpace α] (u : ℕ → α) :
    ∃ (x : _)(φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) :=
  SeqCompactSpace.tendsto_subseq u

end FirstCountableTopology

end SeqCompact

section UniformSpaceSeqCompact

open_locale uniformity

open UniformSpace Prod

variable [UniformSpace β] {s : Set β}

theorem lebesgue_number_lemma_seq {ι : Type _} [IsCountablyGenerated (𝓤 β)] {c : ι → Set β} (hs : IsSeqCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ V ∈ 𝓤 β, SymmetricRel V ∧ ∀, ∀ x ∈ s, ∀, ∃ i, Ball x V ⊆ c i :=
  by
  classical
  obtain ⟨V, hV, Vsymm⟩ : ∃ V : ℕ → Set (β × β), (𝓤 β).HasAntitoneBasis V ∧ ∀ n, swap ⁻¹' V n = V n
  exact UniformSpace.has_seq_basis β
  suffices ∃ n, ∀, ∀ x ∈ s, ∀, ∃ i, ball x (V n) ⊆ c i by
    cases' this with n hn
    exact ⟨V n, hV.to_has_basis.mem_of_mem trivialₓ, Vsymm n, hn⟩
  by_contra H
  obtain ⟨x, x_in, hx⟩ : ∃ x : ℕ → β, (∀ n, x n ∈ s) ∧ ∀ n i, ¬ball (x n) (V n) ⊆ c i := by
    push_neg  at H
    choose x hx using H
    exact ⟨x, forall_and_distrib.mp hx⟩
  clear H
  obtain ⟨x₀, x₀_in, φ, φ_mono, hlim⟩ : ∃ x₀ ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (x ∘ φ) ⟶ x₀
  exact hs x_in
  clear hs
  obtain ⟨i₀, x₀_in⟩ : ∃ i₀, x₀ ∈ c i₀ := by
    rcases hc₂ x₀_in with ⟨_, ⟨i₀, rfl⟩, x₀_in_c⟩
    exact ⟨i₀, x₀_in_c⟩
  clear hc₂
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ball x₀ (V n₀) ⊆ c i₀ := by
    rcases(nhds_basis_uniformity hV.to_has_basis).mem_iff.mp (is_open_iff_mem_nhds.mp (hc₁ i₀) _ x₀_in) with ⟨n₀, _, h⟩
    use n₀
    rwa [← ball_eq_of_symmetry (Vsymm n₀)] at h
  clear hc₁
  obtain ⟨W, W_in, hWW⟩ : ∃ W ∈ 𝓤 β, W ○ W ⊆ V n₀
  exact comp_mem_uniformity_sets (hV.to_has_basis.mem_of_mem trivialₓ)
  obtain ⟨N, x_φ_N_in, hVNW⟩ : ∃ N, x (φ N) ∈ ball x₀ W ∧ V (φ N) ⊆ W := by
    obtain ⟨N₁, h₁⟩ : ∃ N₁, ∀, ∀ n ≥ N₁, ∀, x (φ n) ∈ ball x₀ W
    exact tendsto_at_top'.mp hlim _ (mem_nhds_left x₀ W_in)
    obtain ⟨N₂, h₂⟩ : ∃ N₂, V (φ N₂) ⊆ W := by
      rcases hV.to_has_basis.mem_iff.mp W_in with ⟨N, _, hN⟩
      use N
      exact subset.trans (hV.antitone <| φ_mono.id_le _) hN
    have : φ N₂ ≤ φ (max N₁ N₂) := φ_mono.le_iff_le.mpr (le_max_rightₓ _ _)
    exact ⟨max N₁ N₂, h₁ _ (le_max_leftₓ _ _), trans (hV.antitone this) h₂⟩
  suffices : ball (x (φ N)) (V (φ N)) ⊆ c i₀
  exact hx (φ N) i₀ this
  calc ball (x <| φ N) (V <| φ N) ⊆ ball (x <| φ N) W := preimage_mono hVNW _ ⊆ ball x₀ (V n₀) :=
      ball_subset_of_comp_subset x_φ_N_in hWW _ ⊆ c i₀ := hn₀

theorem IsSeqCompact.totally_bounded (h : IsSeqCompact s) : TotallyBounded s := by
  classical
  apply totally_bounded_of_forall_symm
  unfold IsSeqCompact  at h
  contrapose! h
  rcases h with ⟨V, V_in, V_symm, h⟩
  simp_rw [not_subset]  at h
  have : ∀ t : Set β, finite t → ∃ a, a ∈ s ∧ a ∉ ⋃ y ∈ t, ball y V := by
    intro t ht
    obtain ⟨a, a_in, H⟩ : ∃ a ∈ s, ∀ x : β, x ∈ t → (x, a) ∉ V := by
      simpa [ht] using h t
    use a, a_in
    intro H'
    obtain ⟨x, x_in, hx⟩ := mem_Union₂.mp H'
    exact H x x_in hx
  cases' seq_of_forall_finite_exists this with u hu
  clear h this
  simp [forall_and_distrib] at hu
  cases' hu with u_in hu
  use u, u_in
  clear u_in
  intro x x_in φ
  intro hφ huφ
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V
  exact huφ.cauchy_seq.mem_entourage V_in
  specialize hN N (N + 1) (le_reflₓ N) (Nat.le_succₓ N)
  specialize hu (φ <| N + 1) (φ N) (hφ <| lt_add_one N)
  exact hu hN

protected theorem IsSeqCompact.is_compact [is_countably_generated <| 𝓤 β] (hs : IsSeqCompact s) : IsCompact s := by
  classical
  rw [is_compact_iff_finite_subcover]
  intro ι U Uop s_sub
  rcases lebesgue_number_lemma_seq hs Uop s_sub with ⟨V, V_in, Vsymm, H⟩
  rcases totally_bounded_iff_subset.mp hs.totally_bounded V V_in with ⟨t, t_sub, tfin, ht⟩
  have : ∀ x : t, ∃ i : ι, ball x.val V ⊆ U i := by
    rintro ⟨x, x_in⟩
    exact H x (t_sub x_in)
  choose i hi using this
  have : Fintype t := tfin.fintype
  use Finset.image i Finset.univ
  trans ⋃ y ∈ t, ball y V
  · intro x x_in
    specialize ht x_in
    rw [mem_Union₂] at *
    simp_rw [ball_eq_of_symmetry Vsymm]
    exact ht
    
  · refine' Union₂_mono' fun x x_in => _
    exact ⟨i ⟨x, x_in⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hi ⟨x, x_in⟩⟩
    

/-- A version of Bolzano-Weistrass: in a uniform space with countably generated uniformity filter
(e.g., in a metric space), a set is compact if and only if it is sequentially compact. -/
protected theorem UniformSpace.compact_iff_seq_compact [is_countably_generated <| 𝓤 β] : IsCompact s ↔ IsSeqCompact s :=
  ⟨fun H => H.IsSeqCompact, fun H => H.IsCompact⟩

theorem UniformSpace.compact_space_iff_seq_compact_space [is_countably_generated <| 𝓤 β] :
    CompactSpace β ↔ SeqCompactSpace β :=
  have key : IsCompact (Univ : Set β) ↔ IsSeqCompact Univ := UniformSpace.compact_iff_seq_compact
  ⟨fun ⟨h⟩ => ⟨key.mp h⟩, fun ⟨h⟩ => ⟨key.mpr h⟩⟩

end UniformSpaceSeqCompact

section MetricSeqCompact

variable [MetricSpace β] {s : Set β}

open Metric

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set. -/
theorem tendsto_subseq_of_frequently_bounded [ProperSpace β] (hs : Bounded s) {u : ℕ → β}
    (hu : ∃ᶠ n in at_top, u n ∈ s) : ∃ b ∈ Closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 b) := by
  have hcs : IsCompact (Closure s) := compact_iff_closed_bounded.mpr ⟨is_closed_closure, bounded_closure_of_bounded hs⟩
  replace hcs : IsSeqCompact (Closure s)
  exact uniform_space.compact_iff_seq_compact.mp hcs
  have hu' : ∃ᶠ n in at_top, u n ∈ Closure s := by
    apply frequently.mono hu
    intro n
    apply subset_closure
  exact hcs.subseq_of_frequently_in hu'

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. -/
theorem tendsto_subseq_of_bounded [ProperSpace β] (hs : Bounded s) {u : ℕ → β} (hu : ∀ n, u n ∈ s) :
    ∃ b ∈ Closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 b) :=
  tendsto_subseq_of_frequently_bounded hs <| frequently_of_forall hu

theorem SeqCompact.lebesgue_number_lemma_of_metric {ι : Type _} {c : ι → Set β} (hs : IsSeqCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ δ > 0, ∀, ∀ x ∈ s, ∀, ∃ i, Ball x δ ⊆ c i := by
  rcases lebesgue_number_lemma_seq hs hc₁ hc₂ with ⟨V, V_in, _, hV⟩
  rcases uniformity_basis_dist.mem_iff.mp V_in with ⟨δ, δ_pos, h⟩
  use δ, δ_pos
  intro x x_in
  rcases hV x x_in with ⟨i, hi⟩
  use i
  have := ball_mono h x
  rw [ball_eq_ball'] at this
  exact subset.trans this hi

end MetricSeqCompact

