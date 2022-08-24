/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot, Yury Kudryashov
-/
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.MetricSpace.Basic

/-!
# Sequences in topological spaces

In this file we define sequences in topological spaces and show how they are related to
filters and the topology.

## Main definitions

### Set operation
* `seq_closure s`: sequential closure of a set, the set of limits of sequences of points of `s`;

### Predicates

* `is_seq_closed s`: predicate saying that a set is sequentially closed, i.e., `seq_closure s ⊆ s`;
* `seq_continuous f`: predicate saying that a function is sequentially continuous, i.e.,
  for any sequence `u : ℕ → X` that converges to a point `x`, the sequence `f ∘ u` converges to
  `f x`;
* `is_seq_compact s`: predicate saying that a set is sequentially compact, i.e., every sequence
  taking values in `s` has a converging subsequence.

### Type classes

* `frechet_urysohn_space X`: a typeclass saying that a topological space is a *Fréchet-Urysohn
  space*, i.e., the sequential closure of any set is equal to its closure.
* `sequential_space X`: a typeclass saying that a topological space is a *sequential space*, i.e.,
  any sequentially closed set in this space is closed. This condition is weaker than being a
  Fréchet-Urysohn space.
* `seq_compact_space X`: a typeclass saying that a topological space is sequentially compact, i.e.,
  every sequence in `X` has a converging subsequence.

## Main results

* `seq_closure_subset_closure`: closure of a set includes its sequential closure;
* `is_closed.is_seq_closed`: a closed set is sequentially closed;
* `is_seq_closed.seq_closure_eq`: sequential closure of a sequentially closed set `s` is equal
  to `s`;
* `seq_closure_eq_closure`: in a Fréchet-Urysohn space, the sequential closure of a set is equal to
  its closure;
* `tendsto_nhds_iff_seq_tendsto`, `frechet_urysohn_space.of_seq_tendsto_imp_tendsto`: a topological
  space is a Fréchet-Urysohn space if and only if sequential convergence implies convergence;
* `topological_space.first_countable_topology.frechet_urysohn_space`: every topological space with
  first countable topology is a Fréchet-Urysohn space;
* `frechet_urysohn_space.to_sequential_space`: every Fréchet-Urysohn space is a sequential space;
* `is_seq_compact.is_compact`: a sequentially compact set in a uniform space with countably
  generated uniformity is compact.

## Tags

sequentially closed, sequentially compact, sequential space
-/


open Set Function Filter TopologicalSpace

open TopologicalSpace

variable {X Y : Type _}

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/


section TopologicalSpace

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- The sequential closure of a set `s : set X` in a topological space `X` is the set of all `a : X`
which arise as limit of sequences in `s`. Note that the sequential closure of a set is not
guaranteed to be sequentially closed. -/
def SeqClosure (s : Set X) : Set X :=
  { a | ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ Tendsto x atTop (𝓝 a) }

theorem subset_seq_closure {s : Set X} : s ⊆ SeqClosure s := fun p hp => ⟨const ℕ p, fun _ => hp, tendsto_const_nhds⟩

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
theorem seq_closure_subset_closure {s : Set X} : SeqClosure s ⊆ Closure s := fun p ⟨x, xM, xp⟩ =>
  mem_closure_of_tendsto xp (univ_mem' xM)

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`, the
limit belongs to `s` as well. Note that the sequential closure of a set is not guaranteed to be
sequentially closed. -/
def IsSeqClosed (s : Set X) : Prop :=
  ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ s) → Tendsto x atTop (𝓝 p) → p ∈ s

/-- The sequential closure of a sequentially closed set is the set itself. -/
theorem IsSeqClosed.seq_closure_eq {s : Set X} (hs : IsSeqClosed s) : SeqClosure s = s :=
  Subset.antisymm (fun p ⟨x, hx, hp⟩ => hs hx hp) subset_seq_closure

/-- If a set is equal to its sequential closure, then it is sequentially closed. -/
theorem is_seq_closed_of_seq_closure_eq {s : Set X} (hs : SeqClosure s = s) : IsSeqClosed s := fun x p hxs hxp =>
  hs ▸ ⟨x, hxs, hxp⟩

/-- A set is sequentially closed iff it is equal to its sequential closure. -/
theorem is_seq_closed_iff {s : Set X} : IsSeqClosed s ↔ SeqClosure s = s :=
  ⟨IsSeqClosed.seq_closure_eq, is_seq_closed_of_seq_closure_eq⟩

/-- A set is sequentially closed if it is closed. -/
protected theorem IsClosed.is_seq_closed {s : Set X} (hc : IsClosed s) : IsSeqClosed s := fun u x hu hx =>
  hc.mem_of_tendsto hx (eventually_of_forall hu)

/-- A topological space is called a *Fréchet-Urysohn space*, if the sequential closure of any set
is equal to its closure. Since one of the inclusions is trivial, we require only the non-trivial one
in the definition. -/
class FrechetUrysohnSpace (X : Type _) [TopologicalSpace X] : Prop where
  closure_subset_seq_closure : ∀ s : Set X, Closure s ⊆ SeqClosure s

theorem seq_closure_eq_closure [FrechetUrysohnSpace X] (s : Set X) : SeqClosure s = Closure s :=
  seq_closure_subset_closure.antisymm <| FrechetUrysohnSpace.closure_subset_seq_closure s

/-- In a Fréchet-Urysohn space, a point belongs to the closure of a set iff it is a limit
of a sequence taking values in this set. -/
theorem mem_closure_iff_seq_limit [FrechetUrysohnSpace X] {s : Set X} {a : X} :
    a ∈ Closure s ↔ ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ Tendsto x atTop (𝓝 a) := by
  rw [← seq_closure_eq_closure]
  rfl

/-- If the domain of a function `f : α → β` is a Fréchet-Urysohn space, then convergence
is equivalent to sequential convergence. See also `filter.tendsto_iff_seq_tendsto` for a version
that works for any pair of filters assuming that the filter in the domain is countably generated.

This property is equivalent to the definition of `frechet_urysohn_space`, see
`frechet_urysohn_space.of_seq_tendsto_imp_tendsto`. -/
theorem tendsto_nhds_iff_seq_tendsto [FrechetUrysohnSpace X] {f : X → Y} {a : X} {b : Y} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ u : ℕ → X, Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 b) := by
  refine' ⟨fun hf u hu => hf.comp hu, fun h => ((nhds_basis_closeds _).tendsto_iff (nhds_basis_closeds _)).2 _⟩
  rintro s ⟨hbs, hsc⟩
  refine' ⟨Closure (f ⁻¹' s), ⟨mt _ hbs, is_closed_closure⟩, fun x => mt fun hx => subset_closure hx⟩
  rw [← seq_closure_eq_closure]
  rintro ⟨u, hus, hu⟩
  exact hsc.mem_of_tendsto (h u hu) (eventually_of_forall hus)

/-- An alternative construction for `frechet_urysohn_space`: if sequential convergence implies
convergence, then the space is a Fréchet-Urysohn space. -/
theorem FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto
    (h :
      ∀ (f : X → Prop) (a : X),
        (∀ u : ℕ → X, Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 (f a))) → ContinuousAt f a) :
    FrechetUrysohnSpace X := by
  refine' ⟨fun s x hcx => _⟩
  specialize h (· ∉ s) x
  by_cases' hx : x ∈ s
  · exact subset_seq_closure hx
    
  simp_rw [(· ∘ ·), ContinuousAt, hx, not_false_iff, nhds_true, tendsto_pure, eq_trueₓ, ← mem_compl_iff,
    eventually_mem_set, ← mem_interior_iff_mem_nhds, interior_compl] at h
  rw [mem_compl_iff, imp_not_comm] at h
  simp only [not_forall, not_eventually, mem_compl_iff, not_not] at h
  rcases h hcx with ⟨u, hux, hus⟩
  rcases extraction_of_frequently_at_top hus with ⟨φ, φ_mono, hφ⟩
  exact ⟨u ∘ φ, hφ, hux.comp φ_mono.tendsto_at_top⟩

-- see Note [lower instance priority]
/-- Every first-countable space is a Fréchet-Urysohn space. -/
instance (priority := 100) TopologicalSpace.FirstCountableTopology.frechet_urysohn_space [FirstCountableTopology X] :
    FrechetUrysohnSpace X :=
  FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto fun f a => tendsto_iff_seq_tendsto.2

/-- A topological space is said to be a *sequential space* if any sequentially closed set in this
space is closed. This condition is weaker than being a Fréchet-Urysohn space. -/
class SequentialSpace (X : Type _) [TopologicalSpace X] : Prop where
  is_closed_of_seq : ∀ s : Set X, IsSeqClosed s → IsClosed s

-- see Note [lower instance priority]
/-- Every Fréchet-Urysohn space is a sequential space. -/
instance (priority := 100) FrechetUrysohnSpace.to_sequential_space [FrechetUrysohnSpace X] : SequentialSpace X :=
  ⟨fun s hs => by
    rw [← closure_eq_iff_is_closed, ← seq_closure_eq_closure, hs.seq_closure_eq]⟩

/-- In a sequential space, a sequentially closed set is closed. -/
protected theorem IsSeqClosed.is_closed [SequentialSpace X] {s : Set X} (hs : IsSeqClosed s) : IsClosed s :=
  SequentialSpace.is_closed_of_seq s hs

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
theorem is_seq_closed_iff_is_closed [SequentialSpace X] {M : Set X} : IsSeqClosed M ↔ IsClosed M :=
  ⟨IsSeqClosed.is_closed, IsClosed.is_seq_closed⟩

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def SeqContinuous (f : X → Y) : Prop :=
  ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, Tendsto x atTop (𝓝 p) → Tendsto (f ∘ x) atTop (𝓝 (f p))

/-- The preimage of a sequentially closed set under a sequentially continuous map is sequentially
closed. -/
theorem IsSeqClosed.preimage {f : X → Y} {s : Set Y} (hs : IsSeqClosed s) (hf : SeqContinuous f) :
    IsSeqClosed (f ⁻¹' s) := fun x p hx hp => hs hx (hf hp)

-- A continuous function is sequentially continuous.
protected theorem Continuous.seq_continuous {f : X → Y} (hf : Continuous f) : SeqContinuous f := fun x p hx =>
  (hf.Tendsto p).comp hx

/-- A sequentially continuous function defined on a sequential space is continuous. -/
protected theorem SeqContinuous.continuous [SequentialSpace X] {f : X → Y} (hf : SeqContinuous f) : Continuous f :=
  continuous_iff_is_closed.mpr fun s hs => (hs.IsSeqClosed.Preimage hf).IsClosed

/-- If the domain of a function is a sequential space, then continuity of this function is
equivalent to its sequential continuity. -/
theorem continuous_iff_seq_continuous [SequentialSpace X] {f : X → Y} : Continuous f ↔ SeqContinuous f :=
  ⟨Continuous.seq_continuous, SeqContinuous.continuous⟩

theorem QuotientMap.sequential_space [SequentialSpace X] {f : X → Y} (hf : QuotientMap f) : SequentialSpace Y :=
  ⟨fun s hs => hf.is_closed_preimage.mp <| (hs.Preimage <| hf.Continuous.SeqContinuous).IsClosed⟩

/-- The quotient of a sequential space is a sequential space. -/
instance [SequentialSpace X] {s : Setoidₓ X} : SequentialSpace (Quotientₓ s) :=
  quotient_map_quot_mk.SequentialSpace

end TopologicalSpace

section SeqCompact

open TopologicalSpace TopologicalSpace.FirstCountableTopology

variable [TopologicalSpace X]

/-- A set `s` is sequentially compact if every sequence taking values in `s` has a
converging subsequence. -/
def IsSeqCompact (s : Set X) :=
  ∀ ⦃x : ℕ → X⦄, (∀ n, x n ∈ s) → ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)

/-- A space `X` is sequentially compact if every sequence in `X` has a
converging subsequence. -/
class SeqCompactSpace (X : Type _) [TopologicalSpace X] : Prop where
  seq_compact_univ : IsSeqCompact (Univ : Set X)

theorem IsSeqCompact.subseq_of_frequently_in {s : Set X} (hs : IsSeqCompact s) {x : ℕ → X}
    (hx : ∃ᶠ n in at_top, x n ∈ s) : ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_at_top hx
  let ⟨a, a_in, φ, hφ, h⟩ := hs huψ
  ⟨a, a_in, ψ ∘ φ, hψ.comp hφ, h⟩

theorem SeqCompactSpace.tendsto_subseq [SeqCompactSpace X] (x : ℕ → X) :
    ∃ (a : _)(φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  let ⟨a, _, φ, mono, h⟩ := SeqCompactSpace.seq_compact_univ fun n => mem_univ (x n)
  ⟨a, φ, mono, h⟩

section FirstCountableTopology

variable [FirstCountableTopology X]

open TopologicalSpace.FirstCountableTopology

theorem IsCompact.is_seq_compact {s : Set X} (hs : IsCompact s) : IsSeqCompact s := fun x x_in =>
  let ⟨a, a_in, ha⟩ := @hs (map x atTop) _ (le_principal_iff.mpr (univ_mem' x_in : _))
  ⟨a, a_in, tendsto_subseq ha⟩

theorem IsCompact.tendsto_subseq' {s : Set X} {x : ℕ → X} (hs : IsCompact s) (hx : ∃ᶠ n in at_top, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  hs.IsSeqCompact.subseq_of_frequently_in hx

theorem IsCompact.tendsto_subseq {s : Set X} {x : ℕ → X} (hs : IsCompact s) (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  hs.IsSeqCompact hx

-- see Note [lower instance priority]
instance (priority := 100) FirstCountableTopology.seq_compact_of_compact [CompactSpace X] : SeqCompactSpace X :=
  ⟨compact_univ.IsSeqCompact⟩

theorem CompactSpace.tendsto_subseq [CompactSpace X] (x : ℕ → X) :
    ∃ (a : _)(φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  SeqCompactSpace.tendsto_subseq x

end FirstCountableTopology

end SeqCompact

section UniformSpaceSeqCompact

open uniformity

open UniformSpace Prod

variable [UniformSpace X] {s : Set X}

-- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `rsuffices #[["⟨", ident n, ",", ident hn, "⟩", ":", expr «expr∃ , »((n), ∀
    x «expr ∈ » s, «expr∃ , »((i), «expr ⊆ »(ball x (V n), c i)))]]
theorem lebesgue_number_lemma_seq {ι : Type _} [IsCountablyGenerated (𝓤 X)] {c : ι → Set X} (hs : IsSeqCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ V ∈ 𝓤 X, SymmetricRel V ∧ ∀ x ∈ s, ∃ i, Ball x V ⊆ c i := by
  classical
  obtain ⟨V, hV, Vsymm⟩ : ∃ V : ℕ → Set (X × X), (𝓤 X).HasAntitoneBasis V ∧ ∀ n, swap ⁻¹' V n = V n
  exact UniformSpace.has_seq_basis X
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:64:14: unsupported tactic `rsuffices #[[\"⟨\", ident n, \",\", ident hn, \"⟩\", \":\", expr «expr∃ , »((n), ∀\n    x «expr ∈ » s, «expr∃ , »((i), «expr ⊆ »(ball x (V n), c i)))]]"
  · exact ⟨V n, hV.to_has_basis.mem_of_mem trivialₓ, Vsymm n, hn⟩
    
  by_contra H
  obtain ⟨x, x_in, hx⟩ : ∃ x : ℕ → X, (∀ n, x n ∈ s) ∧ ∀ n i, ¬ball (x n) (V n) ⊆ c i := by
    push_neg  at H
    choose x hx using H
    exact ⟨x, forall_and_distrib.mp hx⟩
  clear H
  obtain ⟨x₀, x₀_in, φ, φ_mono, hlim⟩ : ∃ x₀ ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ tendsto (x ∘ φ) at_top (𝓝 x₀)
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
  obtain ⟨W, W_in, hWW⟩ : ∃ W ∈ 𝓤 X, W ○ W ⊆ V n₀
  exact comp_mem_uniformity_sets (hV.to_has_basis.mem_of_mem trivialₓ)
  obtain ⟨N, x_φ_N_in, hVNW⟩ : ∃ N, x (φ N) ∈ ball x₀ W ∧ V (φ N) ⊆ W := by
    obtain ⟨N₁, h₁⟩ : ∃ N₁, ∀ n ≥ N₁, x (φ n) ∈ ball x₀ W
    exact tendsto_at_top'.mp hlim _ (mem_nhds_left x₀ W_in)
    obtain ⟨N₂, h₂⟩ : ∃ N₂, V (φ N₂) ⊆ W := by
      rcases hV.to_has_basis.mem_iff.mp W_in with ⟨N, _, hN⟩
      use N
      exact subset.trans (hV.antitone <| φ_mono.id_le _) hN
    have : φ N₂ ≤ φ (max N₁ N₂) := φ_mono.le_iff_le.mpr (le_max_rightₓ _ _)
    exact ⟨max N₁ N₂, h₁ _ (le_max_leftₓ _ _), trans (hV.antitone this) h₂⟩
  suffices : ball (x (φ N)) (V (φ N)) ⊆ c i₀
  exact hx (φ N) i₀ this
  calc
    ball (x <| φ N) (V <| φ N) ⊆ ball (x <| φ N) W := preimage_mono hVNW
    _ ⊆ ball x₀ (V n₀) := ball_subset_of_comp_subset x_φ_N_in hWW
    _ ⊆ c i₀ := hn₀
    

theorem IsSeqCompact.totally_bounded (h : IsSeqCompact s) : TotallyBounded s := by
  classical
  apply totally_bounded_of_forall_symm
  unfold IsSeqCompact  at h
  contrapose! h
  rcases h with ⟨V, V_in, V_symm, h⟩
  simp_rw [not_subset] at h
  have : ∀ t : Set X, t.Finite → ∃ a, a ∈ s ∧ a ∉ ⋃ y ∈ t, ball y V := by
    intro t ht
    obtain ⟨a, a_in, H⟩ : ∃ a ∈ s, ∀ x ∈ t, (x, a) ∉ V := by
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

protected theorem IsSeqCompact.is_compact [is_countably_generated <| 𝓤 X] (hs : IsSeqCompact s) : IsCompact s := by
  classical
  rw [is_compact_iff_finite_subcover]
  intro ι U Uop s_sub
  rcases lebesgue_number_lemma_seq hs Uop s_sub with ⟨V, V_in, Vsymm, H⟩
  rcases totally_bounded_iff_subset.mp hs.totally_bounded V V_in with ⟨t, t_sub, tfin, ht⟩
  have : ∀ x : t, ∃ i : ι, ball x.val V ⊆ U i := by
    rintro ⟨x, x_in⟩
    exact H x (t_sub x_in)
  choose i hi using this
  haveI : Fintype t := tfin.fintype
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
protected theorem UniformSpace.compact_iff_seq_compact [is_countably_generated <| 𝓤 X] : IsCompact s ↔ IsSeqCompact s :=
  ⟨fun H => H.IsSeqCompact, fun H => H.IsCompact⟩

theorem UniformSpace.compact_space_iff_seq_compact_space [is_countably_generated <| 𝓤 X] :
    CompactSpace X ↔ SeqCompactSpace X :=
  have key : IsCompact (Univ : Set X) ↔ IsSeqCompact Univ := UniformSpace.compact_iff_seq_compact
  ⟨fun ⟨h⟩ => ⟨key.mp h⟩, fun ⟨h⟩ => ⟨key.mpr h⟩⟩

end UniformSpaceSeqCompact

section MetricSeqCompact

variable [PseudoMetricSpace X]

open Metric

theorem SeqCompact.lebesgue_number_lemma_of_metric {ι : Sort _} {c : ι → Set X} {s : Set X} (hs : IsSeqCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ δ > 0, ∀ a ∈ s, ∃ i, Ball a δ ⊆ c i :=
  lebesgue_number_lemma_of_metric hs.IsCompact hc₁ hc₂

variable [ProperSpace X] {s : Set X}

/-- A version of **Bolzano-Weistrass**: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set. -/
theorem tendsto_subseq_of_frequently_bounded (hs : Bounded s) {x : ℕ → X} (hx : ∃ᶠ n in at_top, x n ∈ s) :
    ∃ a ∈ Closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  have hcs : IsSeqCompact (Closure s) := hs.is_compact_closure.IsSeqCompact
  have hu' : ∃ᶠ n in at_top, x n ∈ Closure s := hx.mono fun n hn => subset_closure hn
  hcs.subseq_of_frequently_in hu'

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. -/
theorem tendsto_subseq_of_bounded (hs : Bounded s) {x : ℕ → X} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ Closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  tendsto_subseq_of_frequently_bounded hs <| frequently_of_forall hx

end MetricSeqCompact

