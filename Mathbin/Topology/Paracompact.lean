/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Yury Kudryashov
-/
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.Separation
import Mathbin.Data.Option.Basic

/-!
# Paracompact topological spaces

A topological space `X` is said to be paracompact if every open covering of `X` admits a locally
finite refinement.

The definition requires that each set of the new covering is a subset of one of the sets of the
initial covering. However, one can ensure that each open covering `s : ι → set X` admits a *precise*
locally finite refinement, i.e., an open covering `t : ι → set X` with the same index set such that
`∀ i, t i ⊆ s i`, see lemma `precise_refinement`. We also provide a convenience lemma
`precise_refinement_set` that deals with open coverings of a closed subset of `X` instead of the
whole space.

We also prove the following facts.

* Every compact space is paracompact, see instance `paracompact_of_compact`.

* A locally compact sigma compact Hausdorff space is paracompact, see instance
  `paracompact_of_locally_compact_sigma_compact`. Moreover, we can choose a locally finite
  refinement with sets in a given collection of filter bases of `𝓝 x, `x : X`, see
  `refinement_of_locally_compact_sigma_compact_of_nhds_basis`. For example, in a proper metric space
  every open covering `⋃ i, s i` admits a refinement `⋃ i, metric.ball (c i) (r i)`.

* Every paracompact Hausdorff space is normal. This statement is not an instance to avoid loops in
  the instance graph.

* Every `emetric_space` is a paracompact space, see instance `emetric_space.paracompact_space` in
  `topology/metric_space/emetric_paracompact`.

## TODO

Prove (some of) [Michael's theorems](https://ncatlab.org/nlab/show/Michael%27s+theorem).

## Tags

compact space, paracompact space, locally finite covering
-/


open Set Filter Function

open Filter TopologicalSpace

universe u v

/-- A topological space is called paracompact, if every open covering of this space admits a locally
finite refinement. We use the same universe for all types in the definition to avoid creating a
class like `paracompact_space.{u v}`. Due to lemma `precise_refinement` below, every open covering
`s : α → set X` indexed on `α : Type v` has a *precise* locally finite refinement, i.e., a locally
finite refinement `t : α → set X` indexed on the same type such that each `∀ i, t i ⊆ s i`. -/
class ParacompactSpace (X : Type v) [TopologicalSpace X] : Prop where
  locally_finite_refinement :
    ∀ (α : Type v) (s : α → Set X) (ho : ∀ a, IsOpen (s a)) (hc : (⋃ a, s a) = univ),
      ∃ (β : Type v) (t : β → Set X) (ho : ∀ b, IsOpen (t b)) (hc : (⋃ b, t b) = univ),
        LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a
#align paracompact_space ParacompactSpace

variable {ι : Type u} {X : Type v} [TopologicalSpace X]

/-- Any open cover of a paracompact space has a locally finite *precise* refinement, that is,
one indexed on the same type with each open set contained in the corresponding original one. -/
theorem precise_refinement [ParacompactSpace X] (u : ι → Set X) (uo : ∀ a, IsOpen (u a)) (uc : (⋃ i, u i) = univ) :
    ∃ v : ι → Set X, (∀ a, IsOpen (v a)) ∧ (⋃ i, v i) = univ ∧ LocallyFinite v ∧ ∀ a, v a ⊆ u a := by
  -- Apply definition to `range u`, then turn existence quantifiers into functions using `choose`
  have :=
    ParacompactSpace.locally_finite_refinement (range u) coe (SetCoe.forall.2 $ forall_range_iff.2 uo)
      (by rwa [← sUnion_range, Subtype.range_coe])
  simp only [SetCoe.exists, Subtype.coe_mk, exists_range_iff', Union_eq_univ_iff, exists_prop] at this
  choose α t hto hXt htf ind hind
  choose t_inv ht_inv using hXt
  choose U hxU hU using htf
  -- Send each `i` to the union of `t a` over `a ∈ ind ⁻¹' {i}`
  refine' ⟨fun i => ⋃ (a : α) (ha : ind a = i), t a, _, _, _, _⟩
  · exact fun a => is_open_Union fun a => is_open_Union $ fun ha => hto a
    
  · simp only [eq_univ_iff_forall, mem_Union]
    exact fun x => ⟨ind (t_inv x), _, rfl, ht_inv _⟩
    
  · refine' fun x => ⟨U x, hxU x, ((hU x).image ind).Subset _⟩
    simp only [subset_def, mem_Union, mem_set_of_eq, Set.Nonempty, mem_inter_iff]
    rintro i ⟨y, ⟨a, rfl, hya⟩, hyU⟩
    exact mem_image_of_mem _ ⟨y, hya, hyU⟩
    
  · simp only [subset_def, mem_Union]
    rintro i x ⟨a, rfl, hxa⟩
    exact hind _ hxa
    
#align precise_refinement precise_refinement

/-- In a paracompact space, every open covering of a closed set admits a locally finite refinement
indexed by the same type. -/
theorem precise_refinement_set [ParacompactSpace X] {s : Set X} (hs : IsClosed s) (u : ι → Set X)
    (uo : ∀ i, IsOpen (u i)) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, (∀ i, IsOpen (v i)) ∧ (s ⊆ ⋃ i, v i) ∧ LocallyFinite v ∧ ∀ i, v i ⊆ u i := by
  rcases precise_refinement (Option.elim' (sᶜ) u) (Option.forall.2 ⟨is_open_compl_iff.2 hs, uo⟩) _ with
    ⟨v, vo, vc, vf, vu⟩
  refine' ⟨v ∘ some, fun i => vo _, _, vf.comp_injective (Option.some_injective _), fun i => vu _⟩
  · simp only [Union_option, ← compl_subset_iff_union] at vc
    exact subset.trans (subset_compl_comm.1 $ vu Option.none) vc
    
  · simpa only [Union_option, Option.elim', ← compl_subset_iff_union, compl_compl]
    
#align precise_refinement_set precise_refinement_set

-- See note [lower instance priority]
/-- A compact space is paracompact. -/
instance (priority := 100) paracompactOfCompact [CompactSpace X] : ParacompactSpace X := by
  -- the proof is trivial: we choose a finite subcover using compactness, and use it
  refine' ⟨fun ι s ho hu => _⟩
  rcases is_compact_univ.elim_finite_subcover _ ho hu.ge with ⟨T, hT⟩
  have := hT
  simp only [subset_def, mem_Union] at this
  choose i hiT hi using fun x => this x (mem_univ x)
  refine' ⟨(T : Set ι), fun t => s t, fun t => ho _, _, locally_finite_of_finite _, fun t => ⟨t, subset.rfl⟩⟩
  simpa only [Union_coe_set, ← univ_subset_iff]
#align paracompact_of_compact paracompactOfCompact

/-- Let `X` be a locally compact sigma compact Hausdorff topological space, let `s` be a closed set
in `X`. Suppose that for each `x ∈ s` the sets `B x : ι x → set X` with the predicate
`p x : ι x → Prop` form a basis of the filter `𝓝 x`. Then there exists a locally finite covering
`λ i, B (c i) (r i)` of `s` such that all “centers” `c i` belong to `s` and each `r i` satisfies
`p (c i)`.

The notation is inspired by the case `B x r = metric.ball x r` but the theorem applies to
`nhds_basis_opens` as well. If the covering must be subordinate to some open covering of `s`, then
the user should use a basis obtained by `filter.has_basis.restrict_subset` or a similar lemma, see
the proof of `paracompact_of_locally_compact_sigma_compact` for an example.

The formalization is based on two [ncatlab](https://ncatlab.org/) proofs:
* [locally compact and sigma compact spaces are paracompact](https://ncatlab.org/nlab/show/locally+compact+and+sigma-compact+spaces+are+paracompact);
* [open cover of smooth manifold admits locally finite refinement by closed balls](https://ncatlab.org/nlab/show/partition+of+unity#ExistenceOnSmoothManifolds).

See also `refinement_of_locally_compact_sigma_compact_of_nhds_basis` for a version of this lemma
dealing with a covering of the whole space.

In most cases (namely, if `B c r ∪ B c r'` is again a set of the form `B c r''`) it is possible
to choose `α = X`. This fact is not yet formalized in `mathlib`. -/
theorem refinement_of_locally_compact_sigma_compact_of_nhds_basis_set [LocallyCompactSpace X] [SigmaCompactSpace X]
    [T2Space X] {ι : X → Type u} {p : ∀ x, ι x → Prop} {B : ∀ x, ι x → Set X} {s : Set X} (hs : IsClosed s)
    (hB : ∀ x ∈ s, (𝓝 x).HasBasis (p x) (B x)) :
    ∃ (α : Type v) (c : α → X) (r : ∀ a, ι (c a)),
      (∀ a, c a ∈ s ∧ p (c a) (r a)) ∧ (s ⊆ ⋃ a, B (c a) (r a)) ∧ LocallyFinite fun a => B (c a) (r a) :=
  by classical
  -- For technical reasons we prepend two empty sets to the sequence `compact_exhaustion.choice X`
  set K' : CompactExhaustion X := CompactExhaustion.choice X
  set K : CompactExhaustion X := K'.shiftr.shiftr
  set Kdiff := fun n => K (n + 1) \ interior (K n)
  -- Now we restate some properties of `compact_exhaustion` for `K`/`Kdiff`
  have hKcov : ∀ x, x ∈ Kdiff (K'.find x + 1) := by
    intro x
    simpa only [K'.find_shiftr] using diff_subset_diff_right interior_subset (K'.shiftr.mem_diff_shiftr_find x)
  have Kdiffc : ∀ n, IsCompact (Kdiff n ∩ s) := fun n => ((K.is_compact _).diff is_open_interior).inter_right hs
  -- Next we choose a finite covering `B (c n i) (r n i)` of each
  -- `Kdiff (n + 1) ∩ s` such that `B (c n i) (r n i) ∩ s` is disjoint with `K n`
  have : ∀ (n) (x : Kdiff (n + 1) ∩ s), K nᶜ ∈ 𝓝 (x : X) := fun n x =>
    IsOpen.mem_nhds (K.is_closed n).is_open_compl fun hx' => x.2.1.2 $ K.subset_interior_succ _ hx'
  haveI : ∀ (n) (x : Kdiff n ∩ s), Nonempty (ι x) := fun n x => (hB x x.2.2).Nonempty
  choose! r hrp hr using fun n (x : Kdiff (n + 1) ∩ s) => (hB x x.2.2).mem_iff.1 (this n x)
  have hxr : ∀ (n x) (hx : x ∈ Kdiff (n + 1) ∩ s), B x (r n ⟨x, hx⟩) ∈ 𝓝 x := fun n x hx =>
    (hB x hx.2).mem_of_mem (hrp _ ⟨x, hx⟩)
  choose T hT using fun n => (Kdiffc (n + 1)).elim_nhds_subcover' _ (hxr n)
  set T' : ∀ n, Set ↥(Kdiff (n + 1) ∩ s) := fun n => T n
  -- Finally, we take the union of all these coverings
  refine' ⟨Σ n, T' n, fun a => a.2, fun a => r a.1 a.2, _, _, _⟩
  · rintro ⟨n, x, hx⟩
    exact ⟨x.2.2, hrp _ _⟩
    
  · refine' fun x hx => mem_Union.2 _
    rcases mem_Union₂.1 (hT _ ⟨hKcov x, hx⟩) with ⟨⟨c, hc⟩, hcT, hcx⟩
    exact ⟨⟨_, ⟨c, hc⟩, hcT⟩, hcx⟩
    
  · intro x
    refine' ⟨interior (K (K'.find x + 3)), IsOpen.mem_nhds is_open_interior (K.subset_interior_succ _ (hKcov x).1), _⟩
    have : (⋃ k ≤ K'.find x + 2, range $ Sigma.mk k : Set (Σ n, T' n)).Finite :=
      (finite_le_nat _).bUnion fun k hk => finite_range _
    apply this.subset
    rintro ⟨k, c, hc⟩
    simp only [mem_Union, mem_set_of_eq, mem_image, Subtype.coe_mk]
    rintro ⟨x, hxB : x ∈ B c (r k c), hxK⟩
    refine' ⟨k, _, ⟨c, hc⟩, rfl⟩
    have := (mem_compl_iff _ _).1 (hr k c hxB)
    contrapose! this with hnk
    exact K.subset hnk (interior_subset hxK)
    
#align
  refinement_of_locally_compact_sigma_compact_of_nhds_basis_set refinement_of_locally_compact_sigma_compact_of_nhds_basis_set

/-- Let `X` be a locally compact sigma compact Hausdorff topological space. Suppose that for each
`x` the sets `B x : ι x → set X` with the predicate `p x : ι x → Prop` form a basis of the filter
`𝓝 x`. Then there exists a locally finite covering `λ i, B (c i) (r i)` of `X` such that each `r i`
satisfies `p (c i)`

The notation is inspired by the case `B x r = metric.ball x r` but the theorem applies to
`nhds_basis_opens` as well. If the covering must be subordinate to some open covering of `s`, then
the user should use a basis obtained by `filter.has_basis.restrict_subset` or a similar lemma, see
the proof of `paracompact_of_locally_compact_sigma_compact` for an example.

The formalization is based on two [ncatlab](https://ncatlab.org/) proofs:
* [locally compact and sigma compact spaces are paracompact](https://ncatlab.org/nlab/show/locally+compact+and+sigma-compact+spaces+are+paracompact);
* [open cover of smooth manifold admits locally finite refinement by closed balls](https://ncatlab.org/nlab/show/partition+of+unity#ExistenceOnSmoothManifolds).

See also `refinement_of_locally_compact_sigma_compact_of_nhds_basis_set` for a version of this lemma
dealing with a covering of a closed set.

In most cases (namely, if `B c r ∪ B c r'` is again a set of the form `B c r''`) it is possible
to choose `α = X`. This fact is not yet formalized in `mathlib`. -/
theorem refinement_of_locally_compact_sigma_compact_of_nhds_basis [LocallyCompactSpace X] [SigmaCompactSpace X]
    [T2Space X] {ι : X → Type u} {p : ∀ x, ι x → Prop} {B : ∀ x, ι x → Set X} (hB : ∀ x, (𝓝 x).HasBasis (p x) (B x)) :
    ∃ (α : Type v) (c : α → X) (r : ∀ a, ι (c a)),
      (∀ a, p (c a) (r a)) ∧ (⋃ a, B (c a) (r a)) = univ ∧ LocallyFinite fun a => B (c a) (r a) :=
  let ⟨α, c, r, hp, hU, hfin⟩ :=
    refinement_of_locally_compact_sigma_compact_of_nhds_basis_set isClosedUniv fun x _ => hB x
  ⟨α, c, r, fun a => (hp a).2, univ_subset_iff.1 hU, hfin⟩
#align
  refinement_of_locally_compact_sigma_compact_of_nhds_basis refinement_of_locally_compact_sigma_compact_of_nhds_basis

-- See note [lower instance priority]
/-- A locally compact sigma compact Hausdorff space is paracompact. See also
`refinement_of_locally_compact_sigma_compact_of_nhds_basis` for a more precise statement. -/
instance (priority := 100) paracompactOfLocallyCompactSigmaCompact [LocallyCompactSpace X] [SigmaCompactSpace X]
    [T2Space X] : ParacompactSpace X := by
  refine' ⟨fun α s ho hc => _⟩
  choose i hi using Union_eq_univ_iff.1 hc
  have : ∀ x : X, (𝓝 x).HasBasis (fun t : Set X => (x ∈ t ∧ IsOpen t) ∧ t ⊆ s (i x)) id := fun x : X =>
    (nhds_basis_opens x).restrict_subset (IsOpen.mem_nhds (ho (i x)) (hi x))
  rcases refinement_of_locally_compact_sigma_compact_of_nhds_basis this with ⟨β, c, t, hto, htc, htf⟩
  exact ⟨β, t, fun x => (hto x).1.2, htc, htf, fun b => ⟨i $ c b, (hto b).2⟩⟩
#align paracompact_of_locally_compact_sigma_compact paracompactOfLocallyCompactSigmaCompact

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (u v) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (u v) -/
/- Dieudonné‘s theorem: a paracompact Hausdorff space is normal. Formalization is based on the proof
at [ncatlab](https://ncatlab.org/nlab/show/paracompact+Hausdorff+spaces+are+normal). -/
theorem normalOfParacompactT2 [T2Space X] [ParacompactSpace X] : NormalSpace X := by
  -- First we show how to go from points to a set on one side.
  have :
    ∀ s t : Set X,
      IsClosed s →
        IsClosed t →
          (∀ x ∈ s, ∃ (u) (v), IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ t ⊆ v ∧ Disjoint u v) →
            ∃ (u) (v), IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ Disjoint u v :=
    by
    /- For each `x ∈ s` we choose open disjoint `u x ∋ x` and `v x ⊇ t`. The sets `u x` form an
        open covering of `s`. We choose a locally finite refinement `u' : s → set X`, then `⋃ i, u' i`
        and `(closure (⋃ i, u' i))ᶜ` are disjoint open neighborhoods of `s` and `t`. -/
    intro s t hs ht H
    choose u v hu hv hxu htv huv using SetCoe.forall'.1 H
    rcases precise_refinement_set hs u hu fun x hx => mem_Union.2 ⟨⟨x, hx⟩, hxu _⟩ with ⟨u', hu'o, hcov', hu'fin, hsub⟩
    refine'
      ⟨⋃ i, u' i, closure (⋃ i, u' i)ᶜ, is_open_Union hu'o, is_closed_closure.is_open_compl, hcov', _,
        disjoint_compl_right.mono le_rfl (compl_le_compl subset_closure)⟩
    rw [hu'fin.closure_Union, compl_Union, subset_Inter_iff]
    refine' fun i x hxt hxu => absurd (htv i hxt) (closure_minimal _ (is_closed_compl_iff.2 $ hv _) hxu)
    exact fun y hyu hyv => (huv i).le_bot ⟨hsub _ hyu, hyv⟩
  -- Now we apply the lemma twice: first to `s` and `t`, then to `t` and each point of `s`.
  refine' ⟨fun s t hs ht hst => this s t hs ht fun x hx => _⟩
  rcases this t {x} ht isClosedSingleton fun y hy => _ with ⟨v, u, hv, hu, htv, hxu, huv⟩
  · exact ⟨u, v, hu, hv, singleton_subset_iff.1 hxu, htv, huv.symm⟩
    
  · simp_rw [singleton_subset_iff]
    exact t2_separation (hst.symm.ne_of_mem hy hx)
    
#align normal_of_paracompact_t2 normalOfParacompactT2

