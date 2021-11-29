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

local notation f " ⟶ " limit => tendsto f at_top (𝓝 limit)

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/


section TopologicalSpace

variable [TopologicalSpace α] [TopologicalSpace β]

/-- A sequence converges in the sence of topological spaces iff the associated statement for filter
holds. -/
theorem TopologicalSpace.seq_tendsto_iff {x : ℕ → α} {limit : α} :
  tendsto x at_top (𝓝 limit) ↔ ∀ U : Set α, limit ∈ U → IsOpen U → ∃ N, ∀ n _ : n ≥ N, x n ∈ U :=
  (at_top_basis.tendsto_iff (nhds_basis_opens limit)).trans$
    by 
      simp only [and_imp, exists_prop, true_andₓ, Set.mem_Ici, ge_iff_le, id]

/-- The sequential closure of a subset M ⊆ α of a topological space α is
the set of all p ∈ α which arise as limit of sequences in M. -/
def SequentialClosure (M : Set α) : Set α :=
  { p | ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ M) ∧ x ⟶ p }

theorem subset_sequential_closure (M : Set α) : M ⊆ SequentialClosure M :=
  fun p _ : p ∈ M => show p ∈ SequentialClosure M from ⟨fun n => p, fun n => ‹p ∈ M›, tendsto_const_nhds⟩

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`,
the limit belongs to `s` as well. -/
def IsSeqClosed (s : Set α) : Prop :=
  s = SequentialClosure s

/-- A convenience lemma for showing that a set is sequentially closed. -/
theorem is_seq_closed_of_def {A : Set α} (h : ∀ x : ℕ → α p : α, (∀ n : ℕ, x n ∈ A) → (x ⟶ p) → p ∈ A) :
  IsSeqClosed A :=
  show A = SequentialClosure A from
    subset.antisymm (subset_sequential_closure A)
      (show ∀ p, p ∈ SequentialClosure A → p ∈ A from
        fun p ⟨x, _, _⟩ => show p ∈ A from h x p ‹∀ n : ℕ, x n ∈ A› ‹x ⟶ p›)

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
theorem sequential_closure_subset_closure (M : Set α) : SequentialClosure M ⊆ Closure M :=
  fun p ⟨x, xM, xp⟩ => mem_closure_of_tendsto xp (univ_mem' xM)

/-- A set is sequentially closed if it is closed. -/
theorem is_seq_closed_of_is_closed (M : Set α) (_ : IsClosed M) : IsSeqClosed M :=
  suffices SequentialClosure M ⊆ M from Set.eq_of_subset_of_subset (subset_sequential_closure M) this 
  calc SequentialClosure M ⊆ Closure M := sequential_closure_subset_closure M 
    _ = M := IsClosed.closure_eq ‹IsClosed M›
    

/-- The limit of a convergent sequence in a sequentially closed set is in that set.-/
theorem mem_of_is_seq_closed {A : Set α} (_ : IsSeqClosed A) {x : ℕ → α} (_ : ∀ n, x n ∈ A) {limit : α}
  (_ : x ⟶ limit) : limit ∈ A :=
  have  : limit ∈ SequentialClosure A :=
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
          (calc M = SequentialClosure M :=
            by 
              assumption 
            _ = Closure M := SequentialSpace.sequential_closure_eq_closure M
            )))
    (is_seq_closed_of_is_closed M)

/-- In a sequential space, a point belongs to the closure of a set iff it is a limit of a sequence
taking values in this set. -/
theorem mem_closure_iff_seq_limit [SequentialSpace α] {s : Set α} {a : α} :
  a ∈ Closure s ↔ ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ s) ∧ x ⟶ a :=
  by 
    rw [←SequentialSpace.sequential_closure_eq_closure]
    exact Iff.rfl

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def SequentiallyContinuous (f : α → β) : Prop :=
  ∀ x : ℕ → α, ∀ {limit : α}, (x ⟶ limit) → (f ∘ x) ⟶ f limit

theorem Continuous.to_sequentially_continuous {f : α → β} (_ : Continuous f) : SequentiallyContinuous f :=
  fun x limit _ : x ⟶ limit =>
    have  : tendsto f (𝓝 limit) (𝓝 (f limit)) := Continuous.tendsto ‹Continuous f› limit 
    show (f ∘ x) ⟶ f limit from tendsto.comp this ‹x ⟶ limit›

/-- In a sequential space, continuity and sequential continuity coincide. -/
theorem continuous_iff_sequentially_continuous {f : α → β} [SequentialSpace α] :
  Continuous f ↔ SequentiallyContinuous f :=
  Iff.intro (fun _ => ‹Continuous f›.to_sequentially_continuous)
    fun this : SequentiallyContinuous f =>
      show Continuous f from
        suffices h : ∀ {A : Set β}, IsClosed A → IsSeqClosed (f ⁻¹' A) from
          continuous_iff_is_closed.mpr fun A _ => is_seq_closed_iff_is_closed.mp$ h ‹IsClosed A›
        fun A _ : IsClosed A =>
          is_seq_closed_of_def$
            fun x : ℕ → α p _ : ∀ n, f (x n) ∈ A _ : x ⟶ p =>
              have  : (f ∘ x) ⟶ f p := ‹SequentiallyContinuous f› x ‹x ⟶ p›
              show f p ∈ A from mem_of_is_closed_sequential ‹IsClosed A› ‹∀ n, f (x n) ∈ A› ‹(f ∘ x) ⟶ f p›

end TopologicalSpace

namespace TopologicalSpace

namespace FirstCountableTopology

variable [TopologicalSpace α] [first_countable_topology α]

/-- Every first-countable space is sequential. -/
instance (priority := 100) : SequentialSpace α :=
  ⟨show ∀ M, SequentialClosure M = Closure M from
      fun M =>
        suffices Closure M ⊆ SequentialClosure M from Set.Subset.antisymm (sequential_closure_subset_closure M) this 
        fun p : α hp : p ∈ Closure M =>
          let ⟨U, hU⟩ := (𝓝 p).exists_antitone_basis 
          have hp : ∀ i : ℕ, ∃ y : α, y ∈ M ∧ y ∈ U i :=
            by 
              simpa using (mem_closure_iff_nhds_basis hU.1).mp hp 
          by 
            choose u hu using hp 
            rw [forall_and_distrib] at hu 
            use u, hu.1
            apply hU.tendsto hu.2⟩

end FirstCountableTopology

end TopologicalSpace

section SeqCompact

open TopologicalSpace TopologicalSpace.FirstCountableTopology

variable [TopologicalSpace α]

/-- A set `s` is sequentially compact if every sequence taking values in `s` has a
converging subsequence. -/
def IsSeqCompact (s : Set α) :=
  ∀ ⦃u : ℕ → α⦄, (∀ n, u n ∈ s) → ∃ (x : _)(_ : x ∈ s)(φ : ℕ → ℕ), StrictMono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x)

/-- A space `α` is sequentially compact if every sequence in `α` has a
converging subsequence. -/
class SeqCompactSpace (α : Type _) [TopologicalSpace α] : Prop where 
  seq_compact_univ : IsSeqCompact (univ : Set α)

theorem IsSeqCompact.subseq_of_frequently_in {s : Set α} (hs : IsSeqCompact s) {u : ℕ → α}
  (hu : ∃ᶠn in at_top, u n ∈ s) : ∃ (x : _)(_ : x ∈ s)(φ : ℕ → ℕ), StrictMono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
  let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_at_top hu 
  let ⟨x, x_in, φ, hφ, h⟩ := hs huψ
  ⟨x, x_in, ψ ∘ φ, hψ.comp hφ, h⟩

theorem SeqCompactSpace.tendsto_subseq [SeqCompactSpace α] (u : ℕ → α) :
  ∃ (x : _)(φ : ℕ → ℕ), StrictMono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
  let ⟨x, _, φ, mono, h⟩ :=
    SeqCompactSpace.seq_compact_univ
      (by 
        simp  :
      ∀ n, u n ∈ univ)
  ⟨x, φ, mono, h⟩

section FirstCountableTopology

variable [first_countable_topology α]

open TopologicalSpace.FirstCountableTopology

theorem IsCompact.is_seq_compact {s : Set α} (hs : IsCompact s) : IsSeqCompact s :=
  fun u u_in =>
    let ⟨x, x_in, hx⟩ := @hs (map u at_top) _ (le_principal_iff.mpr (univ_mem' u_in : _))
    ⟨x, x_in, tendsto_subseq hx⟩

theorem IsCompact.tendsto_subseq' {s : Set α} {u : ℕ → α} (hs : IsCompact s) (hu : ∃ᶠn in at_top, u n ∈ s) :
  ∃ (x : _)(_ : x ∈ s)(φ : ℕ → ℕ), StrictMono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
  hs.is_seq_compact.subseq_of_frequently_in hu

theorem IsCompact.tendsto_subseq {s : Set α} {u : ℕ → α} (hs : IsCompact s) (hu : ∀ n, u n ∈ s) :
  ∃ (x : _)(_ : x ∈ s)(φ : ℕ → ℕ), StrictMono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
  hs.is_seq_compact hu

instance (priority := 100) FirstCountableTopology.seq_compact_of_compact [CompactSpace α] : SeqCompactSpace α :=
  ⟨compact_univ.IsSeqCompact⟩

theorem CompactSpace.tendsto_subseq [CompactSpace α] (u : ℕ → α) :
  ∃ (x : _)(φ : ℕ → ℕ), StrictMono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
  SeqCompactSpace.tendsto_subseq u

end FirstCountableTopology

end SeqCompact

section UniformSpaceSeqCompact

open_locale uniformity

open UniformSpace Prod

variable [UniformSpace β] {s : Set β}

-- error in Topology.Sequences: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lebesgue_number_lemma_seq
{ι : Type*}
[is_countably_generated (expr𝓤() β)]
{c : ι → set β}
(hs : is_seq_compact s)
(hc₁ : ∀ i, is_open (c i))
(hc₂ : «expr ⊆ »(s, «expr⋃ , »((i), c i))) : «expr∃ , »((V «expr ∈ » expr𝓤() β), «expr ∧ »(symmetric_rel V, ∀
  x «expr ∈ » s, «expr∃ , »((i), «expr ⊆ »(ball x V, c i)))) :=
begin
  classical,
  obtain ["⟨", ident V, ",", ident hV, ",", ident Vsymm, "⟩", ":", expr «expr∃ , »((V : exprℕ() → set «expr × »(β, β)), «expr ∧ »((expr𝓤() β).has_antitone_basis (λ
      _, true) V, ∀ n, «expr = »(«expr ⁻¹' »(swap, V n), V n)))],
  from [expr uniform_space.has_seq_basis β],
  suffices [] [":", expr «expr∃ , »((n), ∀ x «expr ∈ » s, «expr∃ , »((i), «expr ⊆ »(ball x (V n), c i)))],
  { cases [expr this] ["with", ident n, ident hn],
    exact [expr ⟨V n, hV.to_has_basis.mem_of_mem trivial, Vsymm n, hn⟩] },
  by_contradiction [ident H],
  obtain ["⟨", ident x, ",", ident x_in, ",", ident hx, "⟩", ":", expr «expr∃ , »((x : exprℕ() → β), «expr ∧ »(∀
     n, «expr ∈ »(x n, s), ∀ n i, «expr¬ »(«expr ⊆ »(ball (x n) (V n), c i))))],
  { push_neg ["at", ident H],
    choose [] [ident x] [ident hx] ["using", expr H],
    exact [expr ⟨x, forall_and_distrib.mp hx⟩] },
  clear [ident H],
  obtain ["⟨", ident x₀, ",", ident x₀_in, ",", ident φ, ",", ident φ_mono, ",", ident hlim, "⟩", ":", expr «expr∃ , »((x₀ «expr ∈ » s)
    (φ : exprℕ() → exprℕ()), «expr ∧ »(strict_mono φ, «expr ⟶ »(«expr ∘ »(x, φ), x₀)))],
  from [expr hs x_in],
  clear [ident hs],
  obtain ["⟨", ident i₀, ",", ident x₀_in, "⟩", ":", expr «expr∃ , »((i₀), «expr ∈ »(x₀, c i₀))],
  { rcases [expr hc₂ x₀_in, "with", "⟨", "_", ",", "⟨", ident i₀, ",", ident rfl, "⟩", ",", ident x₀_in_c, "⟩"],
    exact [expr ⟨i₀, x₀_in_c⟩] },
  clear [ident hc₂],
  obtain ["⟨", ident n₀, ",", ident hn₀, "⟩", ":", expr «expr∃ , »((n₀), «expr ⊆ »(ball x₀ (V n₀), c i₀))],
  { rcases [expr (nhds_basis_uniformity hV.to_has_basis).mem_iff.mp (is_open_iff_mem_nhds.mp (hc₁ i₀) _ x₀_in), "with", "⟨", ident n₀, ",", "_", ",", ident h, "⟩"],
    use [expr n₀],
    rwa ["<-", expr ball_eq_of_symmetry (Vsymm n₀)] ["at", ident h] },
  clear [ident hc₁],
  obtain ["⟨", ident W, ",", ident W_in, ",", ident hWW, "⟩", ":", expr «expr∃ , »((W «expr ∈ » expr𝓤() β), «expr ⊆ »(«expr ○ »(W, W), V n₀))],
  from [expr comp_mem_uniformity_sets (hV.to_has_basis.mem_of_mem trivial)],
  obtain ["⟨", ident N, ",", ident x_φ_N_in, ",", ident hVNW, "⟩", ":", expr «expr∃ , »((N), «expr ∧ »(«expr ∈ »(x (φ N), ball x₀ W), «expr ⊆ »(V (φ N), W)))],
  { obtain ["⟨", ident N₁, ",", ident h₁, "⟩", ":", expr «expr∃ , »((N₁), ∀
      n «expr ≥ » N₁, «expr ∈ »(x (φ n), ball x₀ W))],
    from [expr tendsto_at_top'.mp hlim _ (mem_nhds_left x₀ W_in)],
    obtain ["⟨", ident N₂, ",", ident h₂, "⟩", ":", expr «expr∃ , »((N₂), «expr ⊆ »(V (φ N₂), W))],
    { rcases [expr hV.to_has_basis.mem_iff.mp W_in, "with", "⟨", ident N, ",", "_", ",", ident hN, "⟩"],
      use [expr N],
      exact [expr subset.trans «expr $ »(hV.decreasing trivial trivial, φ_mono.id_le _) hN] },
    have [] [":", expr «expr ≤ »(φ N₂, φ (max N₁ N₂))] [],
    from [expr φ_mono.le_iff_le.mpr (le_max_right _ _)],
    exact [expr ⟨max N₁ N₂, h₁ _ (le_max_left _ _), trans (hV.decreasing trivial trivial this) h₂⟩] },
  suffices [] [":", expr «expr ⊆ »(ball (x (φ N)) (V (φ N)), c i₀)],
  from [expr hx (φ N) i₀ this],
  calc
    «expr ⊆ »(ball «expr $ »(x, φ N) «expr $ »(V, φ N), ball «expr $ »(x, φ N) W) : preimage_mono hVNW
    «expr ⊆ »(..., ball x₀ (V n₀)) : ball_subset_of_comp_subset x_φ_N_in hWW
    «expr ⊆ »(..., c i₀) : hn₀
end

-- error in Topology.Sequences: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_seq_compact.totally_bounded (h : is_seq_compact s) : totally_bounded s :=
begin
  classical,
  apply [expr totally_bounded_of_forall_symm],
  unfold [ident is_seq_compact] ["at", ident h],
  contrapose ["!"] [ident h],
  rcases [expr h, "with", "⟨", ident V, ",", ident V_in, ",", ident V_symm, ",", ident h, "⟩"],
  simp_rw ["[", expr not_subset, "]"] ["at", ident h],
  have [] [":", expr ∀
   t : set β, finite t → «expr∃ , »((a), «expr ∧ »(«expr ∈ »(a, s), «expr ∉ »(a, «expr⋃ , »((y «expr ∈ » t), ball y V))))] [],
  { intros [ident t, ident ht],
    obtain ["⟨", ident a, ",", ident a_in, ",", ident H, "⟩", ":", expr «expr∃ , »((a «expr ∈ » s), ∀
      x : β, «expr ∈ »(x, t) → «expr ∉ »((x, a), V))],
    by simpa [] [] [] ["[", expr ht, "]"] [] ["using", expr h t],
    use ["[", expr a, ",", expr a_in, "]"],
    intro [ident H'],
    obtain ["⟨", ident x, ",", ident x_in, ",", ident hx, "⟩", ":=", expr mem_bUnion_iff.mp H'],
    exact [expr H x x_in hx] },
  cases [expr seq_of_forall_finite_exists this] ["with", ident u, ident hu],
  clear [ident h, ident this],
  simp [] [] [] ["[", expr forall_and_distrib, "]"] [] ["at", ident hu],
  cases [expr hu] ["with", ident u_in, ident hu],
  use ["[", expr u, ",", expr u_in, "]"],
  clear [ident u_in],
  intros [ident x, ident x_in, ident φ],
  intros [ident hφ, ident huφ],
  obtain ["⟨", ident N, ",", ident hN, "⟩", ":", expr «expr∃ , »((N), ∀
    p q, «expr ≥ »(p, N) → «expr ≥ »(q, N) → «expr ∈ »((u (φ p), u (φ q)), V))],
  from [expr huφ.cauchy_seq.mem_entourage V_in],
  specialize [expr hN N «expr + »(N, 1) (le_refl N) (nat.le_succ N)],
  specialize [expr hu «expr $ »(φ, «expr + »(N, 1)) (φ N) «expr $ »(hφ, lt_add_one N)],
  exact [expr hu hN]
end

-- error in Topology.Sequences: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
protected
theorem is_seq_compact.is_compact
[«expr $ »(is_countably_generated, expr𝓤() β)]
(hs : is_seq_compact s) : is_compact s :=
begin
  classical,
  rw [expr is_compact_iff_finite_subcover] [],
  intros [ident ι, ident U, ident Uop, ident s_sub],
  rcases [expr lebesgue_number_lemma_seq hs Uop s_sub, "with", "⟨", ident V, ",", ident V_in, ",", ident Vsymm, ",", ident H, "⟩"],
  rcases [expr totally_bounded_iff_subset.mp hs.totally_bounded V V_in, "with", "⟨", ident t, ",", ident t_sub, ",", ident tfin, ",", ident ht, "⟩"],
  have [] [":", expr ∀ x : t, «expr∃ , »((i : ι), «expr ⊆ »(ball x.val V, U i))] [],
  { rintros ["⟨", ident x, ",", ident x_in, "⟩"],
    exact [expr H x (t_sub x_in)] },
  choose [] [ident i] [ident hi] ["using", expr this],
  haveI [] [":", expr fintype t] [":=", expr tfin.fintype],
  use [expr finset.image i finset.univ],
  transitivity [expr «expr⋃ , »((y «expr ∈ » t), ball y V)],
  { intros [ident x, ident x_in],
    specialize [expr ht x_in],
    rw [expr mem_bUnion_iff] ["at", "*"],
    simp_rw [expr ball_eq_of_symmetry Vsymm] [],
    exact [expr ht] },
  { apply [expr bUnion_subset_bUnion],
    intros [ident x, ident x_in],
    exact [expr ⟨i ⟨x, x_in⟩, finset.mem_image_of_mem _ (finset.mem_univ _), hi ⟨x, x_in⟩⟩] }
end

/-- A version of Bolzano-Weistrass: in a uniform space with countably generated uniformity filter
(e.g., in a metric space), a set is compact if and only if it is sequentially compact. -/
protected theorem UniformSpace.compact_iff_seq_compact [is_countably_generated$ 𝓤 β] : IsCompact s ↔ IsSeqCompact s :=
  ⟨fun H => H.is_seq_compact, fun H => H.is_compact⟩

theorem UniformSpace.compact_space_iff_seq_compact_space [is_countably_generated$ 𝓤 β] :
  CompactSpace β ↔ SeqCompactSpace β :=
  have key : IsCompact (univ : Set β) ↔ IsSeqCompact univ := UniformSpace.compact_iff_seq_compact
  ⟨fun ⟨h⟩ => ⟨key.mp h⟩, fun ⟨h⟩ => ⟨key.mpr h⟩⟩

end UniformSpaceSeqCompact

section MetricSeqCompact

variable [MetricSpace β] {s : Set β}

open Metric

-- error in Topology.Sequences: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set. -/
theorem tendsto_subseq_of_frequently_bounded
[proper_space β]
(hs : bounded s)
{u : exprℕ() → β}
(hu : «expr∃ᶠ in , »((n), at_top, «expr ∈ »(u n, s))) : «expr∃ , »((b «expr ∈ » closure s), «expr∃ , »((φ : exprℕ() → exprℕ()), «expr ∧ »(strict_mono φ, tendsto «expr ∘ »(u, φ) at_top (expr𝓝() b)))) :=
begin
  have [ident hcs] [":", expr is_compact (closure s)] [":=", expr compact_iff_closed_bounded.mpr ⟨is_closed_closure, bounded_closure_of_bounded hs⟩],
  replace [ident hcs] [":", expr is_seq_compact (closure s)] [],
  from [expr uniform_space.compact_iff_seq_compact.mp hcs],
  have [ident hu'] [":", expr «expr∃ᶠ in , »((n), at_top, «expr ∈ »(u n, closure s))] [],
  { apply [expr frequently.mono hu],
    intro [ident n],
    apply [expr subset_closure] },
  exact [expr hcs.subseq_of_frequently_in hu']
end

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. -/
theorem tendsto_subseq_of_bounded [ProperSpace β] (hs : Bounded s) {u : ℕ → β} (hu : ∀ n, u n ∈ s) :
  ∃ (b : _)(_ : b ∈ Closure s), ∃ φ : ℕ → ℕ, StrictMono φ ∧ tendsto (u ∘ φ) at_top (𝓝 b) :=
  tendsto_subseq_of_frequently_bounded hs$ frequently_of_forall hu

-- error in Topology.Sequences: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem seq_compact.lebesgue_number_lemma_of_metric
{ι : Type*}
{c : ι → set β}
(hs : is_seq_compact s)
(hc₁ : ∀ i, is_open (c i))
(hc₂ : «expr ⊆ »(s, «expr⋃ , »((i), c i))) : «expr∃ , »((δ «expr > » 0), ∀
 x «expr ∈ » s, «expr∃ , »((i), «expr ⊆ »(ball x δ, c i))) :=
begin
  rcases [expr lebesgue_number_lemma_seq hs hc₁ hc₂, "with", "⟨", ident V, ",", ident V_in, ",", "_", ",", ident hV, "⟩"],
  rcases [expr uniformity_basis_dist.mem_iff.mp V_in, "with", "⟨", ident δ, ",", ident δ_pos, ",", ident h, "⟩"],
  use ["[", expr δ, ",", expr δ_pos, "]"],
  intros [ident x, ident x_in],
  rcases [expr hV x x_in, "with", "⟨", ident i, ",", ident hi, "⟩"],
  use [expr i],
  have [] [] [":=", expr ball_mono h x],
  rw [expr ball_eq_ball'] ["at", ident this],
  exact [expr subset.trans this hi]
end

end MetricSeqCompact

