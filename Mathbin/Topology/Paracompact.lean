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
  `topology/metric_space/emetric_space`.

## TODO

Prove (some of) [Michael's theorems](https://ncatlab.org/nlab/show/Michael%27s+theorem).

## Tags

compact space, paracompact space, locally finite covering
-/


open Set Filter Function

open_locale Filter TopologicalSpace

universe u v

/-- A topological space is called paracompact, if every open covering of this space admits a locally
finite refinement. We use the same universe for all types in the definition to avoid creating a
class like `paracompact_space.{u v}`. Due to lemma `precise_refinement` below, every open covering
`s : α → set X` indexed on `α : Type v` has a *precise* locally finite refinement, i.e., a locally
finite refinement `t : α → set X` indexed on the same type such that each `∀ i, t i ⊆ s i`. -/
class ParacompactSpace(X : Type v)[TopologicalSpace X] : Prop where 
  locally_finite_refinement :
  ∀ (α : Type v) (s : α → Set X) (ho : ∀ a, IsOpen (s a)) (hc : (⋃a, s a) = univ),
    ∃ (β : Type v)(t : β → Set X)(ho : ∀ b, IsOpen (t b))(hc : (⋃b, t b) = univ), LocallyFinite t ∧ ∀ b, ∃ a, t b ⊆ s a

variable{ι : Type u}{X : Type v}[TopologicalSpace X]

-- error in Topology.Paracompact: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any open cover of a paracompact space has a locally finite *precise* refinement, that is,
one indexed on the same type with each open set contained in the corresponding original one. -/
theorem precise_refinement
[paracompact_space X]
(u : ι → set X)
(uo : ∀ a, is_open (u a))
(uc : «expr = »(«expr⋃ , »((i), u i), univ)) : «expr∃ , »((v : ι → set X), «expr ∧ »(∀
  a, is_open (v a), «expr ∧ »(«expr = »(«expr⋃ , »((i), v i), univ), «expr ∧ »(locally_finite v, ∀
    a, «expr ⊆ »(v a, u a))))) :=
begin
  have [] [] [":=", expr paracompact_space.locally_finite_refinement (range u) coe «expr $ »(set_coe.forall.2, forall_range_iff.2 uo) (by rwa ["[", "<-", expr sUnion_range, ",", expr subtype.range_coe, "]"] [])],
  simp [] [] ["only"] ["[", expr set_coe.exists, ",", expr subtype.coe_mk, ",", expr exists_range_iff', ",", expr Union_eq_univ_iff, ",", expr exists_prop, "]"] [] ["at", ident this],
  choose [] [ident α] [ident t, ident hto, ident hXt, ident htf, ident ind, ident hind] [],
  choose [] [ident t_inv] [ident ht_inv] ["using", expr hXt],
  choose [] [ident U] [ident hxU, ident hU] ["using", expr htf],
  refine [expr ⟨λ i, «expr⋃ , »((a : α) (ha : «expr = »(ind a, i)), t a), _, _, _, _⟩],
  { exact [expr λ a, is_open_Union (λ a, «expr $ »(is_open_Union, λ ha, hto a))] },
  { simp [] [] ["only"] ["[", expr eq_univ_iff_forall, ",", expr mem_Union, "]"] [] [],
    exact [expr λ x, ⟨ind (t_inv x), _, rfl, ht_inv _⟩] },
  { refine [expr λ x, ⟨U x, hxU x, ((hU x).image ind).subset _⟩],
    simp [] [] ["only"] ["[", expr subset_def, ",", expr mem_Union, ",", expr mem_set_of_eq, ",", expr set.nonempty, ",", expr mem_inter_eq, "]"] [] [],
    rintro [ident i, "⟨", ident y, ",", "⟨", ident a, ",", ident rfl, ",", ident hya, "⟩", ",", ident hyU, "⟩"],
    exact [expr mem_image_of_mem _ ⟨y, hya, hyU⟩] },
  { simp [] [] ["only"] ["[", expr subset_def, ",", expr mem_Union, "]"] [] [],
    rintro [ident i, ident x, "⟨", ident a, ",", ident rfl, ",", ident hxa, "⟩"],
    exact [expr hind _ hxa] }
end

/-- In a paracompact space, every open covering of a closed set admits a locally finite refinement
indexed by the same type. -/
theorem precise_refinement_set [ParacompactSpace X] {s : Set X} (hs : IsClosed s) (u : ι → Set X)
  (uo : ∀ i, IsOpen (u i)) (us : s ⊆ ⋃i, u i) :
  ∃ v : ι → Set X, (∀ i, IsOpen (v i)) ∧ (s ⊆ ⋃i, v i) ∧ LocallyFinite v ∧ ∀ i, v i ⊆ u i :=
  by 
    rcases
      precise_refinement (fun i => Option.elim i («expr ᶜ» s) u) (Option.forall.2 ⟨is_open_compl_iff.2 hs, uo⟩) _ with
      ⟨v, vo, vc, vf, vu⟩
    refine' ⟨v ∘ some, fun i => vo _, _, vf.comp_injective (Option.some_injective _), fun i => vu _⟩
    ·
      simp only [Union_option, ←compl_subset_iff_union] at vc 
      exact subset.trans (subset_compl_comm.1$ vu Option.none) vc
    ·
      simpa only [Union_option, Option.elim, ←compl_subset_iff_union, compl_compl]

-- error in Topology.Paracompact: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A compact space is paracompact. -/
@[priority 100]
instance paracompact_of_compact [compact_space X] : paracompact_space X :=
begin
  refine [expr ⟨λ ι s ho hu, _⟩],
  rcases [expr compact_univ.elim_finite_subcover _ ho hu.ge, "with", "⟨", ident T, ",", ident hT, "⟩"],
  have [] [] [":=", expr hT],
  simp [] [] ["only"] ["[", expr subset_def, ",", expr mem_Union, "]"] [] ["at", ident this],
  choose [] [ident i] [ident hiT, ident hi] ["using", expr λ x, this x (mem_univ x)],
  refine [expr ⟨(T : set ι), λ t, s t, λ t, ho _, _, locally_finite_of_fintype _, λ t, ⟨t, subset.rfl⟩⟩],
  rwa ["[", expr Union_coe_set, ",", expr finset.set_bUnion_coe, ",", "<-", expr univ_subset_iff, "]"] []
end

-- error in Topology.Paracompact: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
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
theorem refinement_of_locally_compact_sigma_compact_of_nhds_basis_set
[locally_compact_space X]
[sigma_compact_space X]
[t2_space X]
{ι : X → Type u}
{p : ∀ x, ι x → exprProp()}
{B : ∀ x, ι x → set X}
{s : set X}
(hs : is_closed s)
(hB : ∀
 x «expr ∈ » s, (expr𝓝() x).has_basis (p x) (B x)) : «expr∃ , »((α : Type v)
 (c : α → X)
 (r : ∀
  a, ι (c a)), «expr ∧ »(∀
  a, «expr ∧ »(«expr ∈ »(c a, s), p (c a) (r a)), «expr ∧ »(«expr ⊆ »(s, «expr⋃ , »((a), B (c a) (r a))), locally_finite (λ
    a, B (c a) (r a))))) :=
begin
  classical,
  set [] [ident K'] [":", expr compact_exhaustion X] [":="] [expr compact_exhaustion.choice X] [],
  set [] [ident K] [":", expr compact_exhaustion X] [":="] [expr K'.shiftr.shiftr] [],
  set [] [ident Kdiff] [] [":="] [expr λ n, «expr \ »(K «expr + »(n, 1), interior (K n))] [],
  have [ident hKcov] [":", expr ∀ x, «expr ∈ »(x, Kdiff «expr + »(K'.find x, 1))] [],
  { intro [ident x],
    simpa [] [] ["only"] ["[", expr K'.find_shiftr, "]"] [] ["using", expr diff_subset_diff_right interior_subset (K'.shiftr.mem_diff_shiftr_find x)] },
  have [ident Kdiffc] [":", expr ∀ n, is_compact «expr ∩ »(Kdiff n, s)] [],
  from [expr λ n, ((K.is_compact _).diff is_open_interior).inter_right hs],
  have [] [":", expr ∀ (n) (x : «expr ∩ »(Kdiff «expr + »(n, 1), s)), «expr ∈ »(«expr ᶜ»(K n), expr𝓝() (x : X))] [],
  from [expr λ
   n x, is_open.mem_nhds (K.is_closed n).is_open_compl (λ hx', «expr $ »(x.2.1.2, K.subset_interior_succ _ hx'))],
  haveI [] [":", expr ∀ (n) (x : «expr ∩ »(Kdiff n, s)), nonempty (ι x)] [":=", expr λ n x, (hB x x.2.2).nonempty],
  choose ["!"] [ident r] [ident hrp, ident hr] ["using", expr λ
   (n)
   (x : «expr ∩ »(Kdiff «expr + »(n, 1), s)), (hB x x.2.2).mem_iff.1 (this n x)],
  have [ident hxr] [":", expr ∀
   (n x)
   (hx : «expr ∈ »(x, «expr ∩ »(Kdiff «expr + »(n, 1), s))), «expr ∈ »(B x (r n ⟨x, hx⟩), expr𝓝() x)] [],
  from [expr λ n x hx, (hB x hx.2).mem_of_mem (hrp _ ⟨x, hx⟩)],
  choose [] [ident T] [ident hT] ["using", expr λ n, (Kdiffc «expr + »(n, 1)).elim_nhds_subcover' _ (hxr n)],
  set [] [ident T'] [":", expr ∀ n, set «expr↥ »(«expr ∩ »(Kdiff «expr + »(n, 1), s))] [":="] [expr λ n, T n] [],
  refine [expr ⟨«exprΣ , »((n), T' n), λ a, a.2, λ a, r a.1 a.2, _, _, _⟩],
  { rintro ["⟨", ident n, ",", ident x, ",", ident hx, "⟩"],
    exact [expr ⟨x.2.2, hrp _ _⟩] },
  { refine [expr λ x hx, mem_Union.2 _],
    rcases [expr mem_bUnion_iff.1 (hT _ ⟨hKcov x, hx⟩), "with", "⟨", "⟨", ident c, ",", ident hc, "⟩", ",", ident hcT, ",", ident hcx, "⟩"],
    exact [expr ⟨⟨_, ⟨c, hc⟩, hcT⟩, hcx⟩] },
  { intro [ident x],
    refine [expr ⟨interior (K «expr + »(K'.find x, 3)), is_open.mem_nhds is_open_interior (K.subset_interior_succ _ (hKcov x).1), _⟩],
    have [] [":", expr («expr⋃ , »((k «expr ≤ » «expr + »(K'.find x, 2)), «expr $ »(range, sigma.mk k)) : set «exprΣ , »((n), T' n)).finite] [],
    from [expr (finite_le_nat _).bUnion (λ k hk, finite_range _)],
    apply [expr this.subset],
    rintro ["⟨", ident k, ",", ident c, ",", ident hc, "⟩"],
    simp [] [] ["only"] ["[", expr mem_Union, ",", expr mem_set_of_eq, ",", expr mem_image_eq, ",", expr subtype.coe_mk, "]"] [] [],
    rintro ["⟨", ident x, ",", ident hxB, ":", expr «expr ∈ »(x, B c (r k c)), ",", ident hxK, "⟩"],
    refine [expr ⟨k, _, ⟨c, hc⟩, rfl⟩],
    have [] [] [":=", expr (mem_compl_iff _ _).1 (hr k c hxB)],
    contrapose ["!"] [ident this, "with", ident hnk],
    exact [expr K.subset hnk (interior_subset hxK)] }
end

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
  ∃ (α : Type v)(c : α → X)(r : ∀ a, ι (c a)),
    (∀ a, p (c a) (r a)) ∧ (⋃a, B (c a) (r a)) = univ ∧ LocallyFinite fun a => B (c a) (r a) :=
  let ⟨α, c, r, hp, hU, hfin⟩ :=
    refinement_of_locally_compact_sigma_compact_of_nhds_basis_set is_closed_univ fun x _ => hB x
  ⟨α, c, r, fun a => (hp a).2, univ_subset_iff.1 hU, hfin⟩

-- error in Topology.Paracompact: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A locally compact sigma compact Hausdorff space is paracompact. See also
`refinement_of_locally_compact_sigma_compact_of_nhds_basis` for a more precise statement. -/
@[priority 100]
instance paracompact_of_locally_compact_sigma_compact
[locally_compact_space X]
[sigma_compact_space X]
[t2_space X] : paracompact_space X :=
begin
  refine [expr ⟨λ α s ho hc, _⟩],
  choose [] [ident i] [ident hi] ["using", expr Union_eq_univ_iff.1 hc],
  have [] [":", expr ∀
   x : X, (expr𝓝() x).has_basis (λ
    t : set X, «expr ∧ »(«expr ∧ »(«expr ∈ »(x, t), is_open t), «expr ⊆ »(t, s (i x)))) id] [],
  from [expr λ x : X, (nhds_basis_opens x).restrict_subset (is_open.mem_nhds (ho (i x)) (hi x))],
  rcases [expr refinement_of_locally_compact_sigma_compact_of_nhds_basis this, "with", "⟨", ident β, ",", ident c, ",", ident t, ",", ident hto, ",", ident htc, ",", ident htf, "⟩"],
  exact [expr ⟨β, t, λ x, (hto x).1.2, htc, htf, λ b, ⟨«expr $ »(i, c b), (hto b).2⟩⟩]
end

-- error in Topology.Paracompact: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem normal_of_paracompact_t2 [t2_space X] [paracompact_space X] : normal_space X :=
begin
  have [] [":", expr ∀
   s
   t : set X, is_closed s → is_closed t → ∀
   x «expr ∈ » s, «expr∃ , »((u
     v), «expr ∧ »(is_open u, «expr ∧ »(is_open v, «expr ∧ »(«expr ∈ »(x, u), «expr ∧ »(«expr ⊆ »(t, v), disjoint u v))))) → «expr∃ , »((u
     v), «expr ∧ »(is_open u, «expr ∧ »(is_open v, «expr ∧ »(«expr ⊆ »(s, u), «expr ∧ »(«expr ⊆ »(t, v), disjoint u v)))))] [],
  { intros [ident s, ident t, ident hs, ident ht, ident H],
    choose [] [ident u] [ident v, ident hu, ident hv, ident hxu, ident htv, ident huv] ["using", expr set_coe.forall'.1 H],
    rcases [expr precise_refinement_set hs u hu (λ
      x
      hx, mem_Union.2 ⟨⟨x, hx⟩, hxu _⟩), "with", "⟨", ident u', ",", ident hu'o, ",", ident hcov', ",", ident hu'fin, ",", ident hsub, "⟩"],
    refine [expr ⟨«expr⋃ , »((i), u' i), «expr ᶜ»(closure «expr⋃ , »((i), u' i)), is_open_Union hu'o, is_closed_closure.is_open_compl, hcov', _, disjoint_compl_right.mono le_rfl (compl_le_compl subset_closure)⟩],
    rw ["[", expr hu'fin.closure_Union, ",", expr compl_Union, ",", expr subset_Inter_iff, "]"] [],
    refine [expr λ i x hxt hxu, absurd (htv i hxt) (closure_minimal _ «expr $ »(is_closed_compl_iff.2, hv _) hxu)],
    exact [expr λ y hyu hyv, huv i ⟨hsub _ hyu, hyv⟩] },
  refine [expr ⟨λ s t hs ht hst, this s t hs ht (λ x hx, _)⟩],
  rcases [expr this t {x} ht is_closed_singleton (λ
    y
    hyt, _), "with", "⟨", ident v, ",", ident u, ",", ident hv, ",", ident hu, ",", ident htv, ",", ident hxu, ",", ident huv, "⟩"],
  { exact [expr ⟨u, v, hu, hv, singleton_subset_iff.1 hxu, htv, huv.symm⟩] },
  { have [] [":", expr «expr ≠ »(x, y)] [],
    by { rintro [ident rfl],
      exact [expr hst ⟨hx, hyt⟩] },
    rcases [expr t2_separation this, "with", "⟨", ident v, ",", ident u, ",", ident hv, ",", ident hu, ",", ident hxv, ",", ident hyu, ",", ident hd, "⟩"],
    exact [expr ⟨u, v, hu, hv, hyu, singleton_subset_iff.2 hxv, disjoint.symm hd.le⟩] }
end

