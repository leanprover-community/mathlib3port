import Mathbin.Dynamics.Flow

/-!
# ω-limits

For a function `ϕ : τ → α → β` where `β` is a topological space, we
define the ω-limit under `ϕ` of a set `s` in `α` with respect to
filter `f` on `τ`: an element `y : β` is in the ω-limit of `s` if the
forward images of `s` intersect arbitrarily small neighbourhoods of
`y` frequently "in the direction of `f`".

In practice `ϕ` is often a continuous monoid-act, but the definition
requires only that `ϕ` has a coercion to the appropriate function
type. In the case where `τ` is `ℕ` or `ℝ` and `f` is `at_top`, we
recover the usual definition of the ω-limit set as the set of all `y`
such that there exist sequences `(tₙ)`, `(xₙ)` such that `ϕ tₙ xₙ ⟶ y`
as `n ⟶ ∞`.

## Notations

The `omega_limit` locale provides the localised notation `ω` for
`omega_limit`, as well as `ω⁺` and `ω⁻` for `omega_limit at_top` and
`omega_limit at_bot` respectively for when the acting monoid is
endowed with an order.
-/


open Set Function Filter

open_locale TopologicalSpace

/-!
### Definition and notation
-/


section OmegaLimit

variable{τ : Type _}{α : Type _}{β : Type _}{ι : Type _}

/-- The ω-limit of a set `s` under `ϕ` with respect to a filter `f` is
    ⋂ u ∈ f, cl (ϕ u s). -/
def OmegaLimit [TopologicalSpace β] (f : Filter τ) (ϕ : τ → α → β) (s : Set α) : Set β :=
  ⋂(u : _)(_ : u ∈ f), Closure (image2 ϕ u s)

localized [OmegaLimit] notation "ω" => OmegaLimit

localized [OmegaLimit] notation "ω⁺" => OmegaLimit at_top

localized [OmegaLimit] notation "ω⁻" => OmegaLimit at_bot

variable[TopologicalSpace β]

variable(f : Filter τ)(ϕ : τ → α → β)(s s₁ s₂ : Set α)

/-!
### Elementary properties
-/


theorem omega_limit_def : ω f ϕ s = ⋂(u : _)(_ : u ∈ f), Closure (image2 ϕ u s) :=
  rfl

theorem omega_limit_subset_of_tendsto {m : τ → τ} {f₁ f₂ : Filter τ} (hf : tendsto m f₁ f₂) :
  ω f₁ (fun t x => ϕ (m t) x) s ⊆ ω f₂ ϕ s :=
  by 
    apply Inter_subset_Inter2 
    intro u 
    use m ⁻¹' u 
    apply Inter_subset_Inter2 
    intro hu 
    use tendsto_def.mp hf _ hu 
    rw [←image2_image_left]
    exact closure_mono (image2_subset (image_preimage_subset _ _) subset.rfl)

theorem omega_limit_mono_left {f₁ f₂ : Filter τ} (hf : f₁ ≤ f₂) : ω f₁ ϕ s ⊆ ω f₂ ϕ s :=
  omega_limit_subset_of_tendsto ϕ s (tendsto_id' hf)

theorem omega_limit_mono_right {s₁ s₂ : Set α} (hs : s₁ ⊆ s₂) : ω f ϕ s₁ ⊆ ω f ϕ s₂ :=
  bInter_mono$ fun u hu => closure_mono (image2_subset subset.rfl hs)

theorem is_closed_omega_limit : IsClosed (ω f ϕ s) :=
  is_closed_Inter$ fun u => is_closed_Inter$ fun hu => is_closed_closure

theorem maps_to_omega_limit' {α' β' : Type _} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ → α → β} {ϕ' : τ → α' → β'}
  {ga : α → α'} {s' : Set α'} (hs : maps_to ga s s') {gb : β → β'} (hg : ∀ᶠt in f, eq_on (gb ∘ ϕ t) (ϕ' t ∘ ga) s)
  (hgc : Continuous gb) : maps_to gb (ω f ϕ s) (ω f ϕ' s') :=
  by 
    simp only [omega_limit_def, mem_Inter, maps_to]
    intro y hy u hu 
    refine' map_mem_closure hgc (hy _ (inter_mem hu hg)) (forall_image2_iff.2$ fun t ht x hx => _)
    calc gb (ϕ t x) = ϕ' t (ga x) := ht.2 hx _ ∈ image2 ϕ' u s' := mem_image2_of_mem ht.1 (hs hx)

theorem maps_to_omega_limit {α' β' : Type _} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ → α → β} {ϕ' : τ → α' → β'}
  {ga : α → α'} {s' : Set α'} (hs : maps_to ga s s') {gb : β → β'} (hg : ∀ t x, gb (ϕ t x) = ϕ' t (ga x))
  (hgc : Continuous gb) : maps_to gb (ω f ϕ s) (ω f ϕ' s') :=
  maps_to_omega_limit' _ hs (eventually_of_forall$ fun t x hx => hg t x) hgc

theorem omega_limit_image_eq {α' : Type _} (ϕ : τ → α' → β) (f : Filter τ) (g : α → α') :
  ω f ϕ (g '' s) = ω f (fun t x => ϕ t (g x)) s :=
  by 
    simp only [OmegaLimit, image2_image_right]

theorem omega_limit_preimage_subset {α' : Type _} (ϕ : τ → α' → β) (s : Set α') (f : Filter τ) (g : α → α') :
  ω f (fun t x => ϕ t (g x)) (g ⁻¹' s) ⊆ ω f ϕ s :=
  maps_to_omega_limit _ (maps_to_preimage _ _) (fun t x => rfl) continuous_id

/-!
### Equivalent definitions of the omega limit

The next few lemmas are various versions of the property
characterising ω-limits:
-/


/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
    preimages of an arbitrary neighbourhood of `y` frequently
    (w.r.t. `f`) intersects of `s`. -/
theorem mem_omega_limit_iff_frequently (y : β) : y ∈ ω f ϕ s ↔ ∀ n _ : n ∈ 𝓝 y, ∃ᶠt in f, (s ∩ ϕ t ⁻¹' n).Nonempty :=
  by 
    simpRw [frequently_iff, omega_limit_def, mem_Inter, mem_closure_iff_nhds]
    split 
    ·
      intro h _ hn _ hu 
      rcases h _ hu _ hn with ⟨_, _, _, _, ht, hx, hϕtx⟩
      exact
        ⟨_, ht, _, hx,
          by 
            rwa [mem_preimage, hϕtx]⟩
    ·
      intro h _ hu _ hn 
      rcases h _ hn hu with ⟨_, ht, _, hx, hϕtx⟩
      exact ⟨_, hϕtx, _, _, ht, hx, rfl⟩

/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
    forward images of `s` frequently (w.r.t. `f`) intersect arbitrary
    neighbourhoods of `y`. -/
theorem mem_omega_limit_iff_frequently₂ (y : β) : y ∈ ω f ϕ s ↔ ∀ n _ : n ∈ 𝓝 y, ∃ᶠt in f, (ϕ t '' s ∩ n).Nonempty :=
  by 
    simpRw [mem_omega_limit_iff_frequently, image_inter_nonempty_iff]

/-- An element `y` is in the ω-limit of `x` w.r.t. `f` if the forward
    images of `x` frequently (w.r.t. `f`) falls within an arbitrary
    neighbourhood of `y`. -/
theorem mem_omega_limit_singleton_iff_map_cluster_point (x : α) (y : β) :
  y ∈ ω f ϕ {x} ↔ MapClusterPt y f fun t => ϕ t x :=
  by 
    simpRw [mem_omega_limit_iff_frequently, map_cluster_pt_iff, singleton_inter_nonempty, mem_preimage]

/-!
### Set operations and omega limits
-/


theorem omega_limit_inter : ω f ϕ (s₁ ∩ s₂) ⊆ ω f ϕ s₁ ∩ ω f ϕ s₂ :=
  subset_inter (omega_limit_mono_right _ _ (inter_subset_left _ _))
    (omega_limit_mono_right _ _ (inter_subset_right _ _))

theorem omega_limit_Inter (p : ι → Set α) : ω f ϕ (⋂i, p i) ⊆ ⋂i, ω f ϕ (p i) :=
  subset_Inter$ fun i => omega_limit_mono_right _ _ (Inter_subset _ _)

theorem omega_limit_union : ω f ϕ (s₁ ∪ s₂) = ω f ϕ s₁ ∪ ω f ϕ s₂ :=
  by 
    ext y 
    split 
    ·
      simp only [mem_union, mem_omega_limit_iff_frequently, union_inter_distrib_right, union_nonempty,
        frequently_or_distrib]
      contrapose! 
      simp only [not_frequently, not_nonempty_iff_eq_empty, ←subset_empty_iff]
      rintro ⟨⟨n₁, hn₁, h₁⟩, ⟨n₂, hn₂, h₂⟩⟩
      refine' ⟨n₁ ∩ n₂, inter_mem hn₁ hn₂, h₁.mono$ fun t => _, h₂.mono$ fun t => _⟩
      exacts[subset.trans$ inter_subset_inter_right _$ preimage_mono$ inter_subset_left _ _,
        subset.trans$ inter_subset_inter_right _$ preimage_mono$ inter_subset_right _ _]
    ·
      rintro (hy | hy)
      exacts[omega_limit_mono_right _ _ (subset_union_left _ _) hy,
        omega_limit_mono_right _ _ (subset_union_right _ _) hy]

theorem omega_limit_Union (p : ι → Set α) : (⋃i, ω f ϕ (p i)) ⊆ ω f ϕ (⋃i, p i) :=
  by 
    rw [Union_subset_iff]
    exact fun i => omega_limit_mono_right _ _ (subset_Union _ _)

/-!
Different expressions for omega limits, useful for rewrites. In
particular, one may restrict the intersection to sets in `f` which are
subsets of some set `v` also in `f`.
-/


theorem omega_limit_eq_Inter : ω f ϕ s = ⋂u : «expr↥ » f.sets, Closure (image2 ϕ u s) :=
  bInter_eq_Inter _ _

theorem omega_limit_eq_bInter_inter {v : Set τ} (hv : v ∈ f) :
  ω f ϕ s = ⋂(u : _)(_ : u ∈ f), Closure (image2 ϕ (u ∩ v) s) :=
  subset.antisymm (Inter_subset_Inter2 fun u => ⟨u ∩ v, Inter_subset_Inter2 fun hu => ⟨inter_mem hu hv, subset.rfl⟩⟩)
    (Inter_subset_Inter
      fun u => Inter_subset_Inter fun hu => closure_mono (image2_subset (inter_subset_left _ _) subset.rfl))

theorem omega_limit_eq_Inter_inter {v : Set τ} (hv : v ∈ f) :
  ω f ϕ s = ⋂u : «expr↥ » f.sets, Closure (image2 ϕ (u ∩ v) s) :=
  by 
    rw [omega_limit_eq_bInter_inter _ _ _ hv]
    apply bInter_eq_Inter

theorem omega_limit_subset_closure_fw_image {u : Set τ} (hu : u ∈ f) : ω f ϕ s ⊆ Closure (image2 ϕ u s) :=
  by 
    rw [omega_limit_eq_Inter]
    intro _ hx 
    rw [mem_Inter] at hx 
    exact hx ⟨u, hu⟩

/-!
### `ω-limits and compactness
-/


-- error in Dynamics.OmegaLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
theorem eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset'
{c : set β}
(hc₁ : is_compact c)
(hc₂ : «expr∃ , »((v «expr ∈ » f), «expr ⊆ »(closure (image2 ϕ v s), c)))
{n : set β}
(hn₁ : is_open n)
(hn₂ : «expr ⊆ »(exprω() f ϕ s, n)) : «expr∃ , »((u «expr ∈ » f), «expr ⊆ »(closure (image2 ϕ u s), n)) :=
begin
  rcases [expr hc₂, "with", "⟨", ident v, ",", ident hv₁, ",", ident hv₂, "⟩"],
  let [ident k] [] [":=", expr closure (image2 ϕ v s)],
  have [ident hk] [":", expr is_compact «expr \ »(k, n)] [":=", expr is_compact.diff (compact_of_is_closed_subset hc₁ is_closed_closure hv₂) hn₁],
  let [ident j] [] [":=", expr λ u, «expr ᶜ»(closure (image2 ϕ «expr ∩ »(u, v) s))],
  have [ident hj₁] [":", expr ∀ u «expr ∈ » f, is_open (j u)] [],
  from [expr λ _ _, is_open_compl_iff.mpr is_closed_closure],
  have [ident hj₂] [":", expr «expr ⊆ »(«expr \ »(k, n), «expr⋃ , »((u «expr ∈ » f), j u))] [],
  begin
    have [] [":", expr «expr = »(«expr⋃ , »((u «expr ∈ » f), j u), «expr⋃ , »((u : «expr↥ »(f.sets)), j u))] [],
    from [expr bUnion_eq_Union _ _],
    rw ["[", expr this, ",", expr diff_subset_comm, ",", expr diff_Union, "]"] [],
    rw [expr omega_limit_eq_Inter_inter _ _ _ hv₁] ["at", ident hn₂],
    simp_rw [expr diff_compl] [],
    rw ["<-", expr inter_Inter] [],
    exact [expr subset.trans (inter_subset_right _ _) hn₂]
  end,
  rcases [expr hk.elim_finite_subcover_image hj₁ hj₂, "with", "⟨", ident g, ",", ident hg₁, ":", expr ∀
   u «expr ∈ » g, «expr ∈ »(u, f), ",", ident hg₂, ",", ident hg₃, "⟩"],
  let [ident w] [] [":=", expr «expr ∩ »(«expr⋂ , »((u «expr ∈ » g), u), v)],
  have [ident hw₂] [":", expr «expr ∈ »(w, f)] [],
  by simpa [] [] [] ["*"] [] [],
  have [ident hw₃] [":", expr «expr ⊆ »(«expr \ »(k, n), «expr ᶜ»(closure (image2 ϕ w s)))] [],
  from [expr calc
     «expr ⊆ »(«expr \ »(k, n), «expr⋃ , »((u «expr ∈ » g), j u)) : hg₃
     «expr ⊆ »(..., «expr ᶜ»(closure (image2 ϕ w s))) : begin
       simp [] [] ["only"] ["[", expr Union_subset_iff, ",", expr compl_subset_compl, "]"] [] [],
       intros [ident u, ident hu],
       mono ["*"] [] [] ["using", "[", expr w, "]"],
       exact [expr Inter_subset_of_subset u (Inter_subset_of_subset hu subset.rfl)]
     end],
  have [ident hw₄] [":", expr «expr ⊆ »(«expr ᶜ»(k), «expr ᶜ»(closure (image2 ϕ w s)))] [],
  begin
    rw [expr compl_subset_compl] [],
    calc
      «expr ⊆ »(closure (image2 ϕ w s), _) : closure_mono (image2_subset (inter_subset_right _ _) subset.rfl)
  end,
  have [ident hnc] [":", expr «expr ⊆ »(«expr ᶜ»(n), «expr ∪ »(«expr \ »(k, n), «expr ᶜ»(k)))] [],
  by rw ["[", expr union_comm, ",", "<-", expr inter_subset, ",", expr diff_eq, ",", expr inter_comm, "]"] [],
  have [ident hw] [":", expr «expr ⊆ »(closure (image2 ϕ w s), n)] [],
  from [expr compl_subset_compl.mp (subset.trans hnc (union_subset hw₃ hw₄))],
  exact [expr ⟨_, hw₂, hw⟩]
end

/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
theorem eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset [T2Space β] {c : Set β}
  (hc₁ : IsCompact c) (hc₂ : ∀ᶠt in f, maps_to (ϕ t) s c) {n : Set β} (hn₁ : IsOpen n) (hn₂ : ω f ϕ s ⊆ n) :
  ∃ (u : _)(_ : u ∈ f), Closure (image2 ϕ u s) ⊆ n :=
  eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset' f ϕ _ hc₁
    ⟨_, hc₂, closure_minimal (image2_subset_iff.2 fun t => id) hc₁.is_closed⟩ hn₁ hn₂

theorem eventually_maps_to_of_is_compact_absorbing_of_is_open_of_omega_limit_subset [T2Space β] {c : Set β}
  (hc₁ : IsCompact c) (hc₂ : ∀ᶠt in f, maps_to (ϕ t) s c) {n : Set β} (hn₁ : IsOpen n) (hn₂ : ω f ϕ s ⊆ n) :
  ∀ᶠt in f, maps_to (ϕ t) s n :=
  by 
    rcases eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset f ϕ s hc₁ hc₂ hn₁ hn₂ with
      ⟨u, hu_mem, hu⟩
    refine' mem_of_superset hu_mem fun t ht x hx => _ 
    exact hu (subset_closure$ mem_image2_of_mem ht hx)

theorem eventually_closure_subset_of_is_open_of_omega_limit_subset [CompactSpace β] {v : Set β} (hv₁ : IsOpen v)
  (hv₂ : ω f ϕ s ⊆ v) : ∃ (u : _)(_ : u ∈ f), Closure (image2 ϕ u s) ⊆ v :=
  eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset' _ _ _ compact_univ
    ⟨univ, univ_mem, subset_univ _⟩ hv₁ hv₂

theorem eventually_maps_to_of_is_open_of_omega_limit_subset [CompactSpace β] {v : Set β} (hv₁ : IsOpen v)
  (hv₂ : ω f ϕ s ⊆ v) : ∀ᶠt in f, maps_to (ϕ t) s v :=
  by 
    rcases eventually_closure_subset_of_is_open_of_omega_limit_subset f ϕ s hv₁ hv₂ with ⟨u, hu_mem, hu⟩
    refine' mem_of_superset hu_mem fun t ht x hx => _ 
    exact hu (subset_closure$ mem_image2_of_mem ht hx)

-- error in Dynamics.OmegaLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The ω-limit of a nonempty set w.r.t. a nontrivial filter is nonempty. -/
theorem nonempty_omega_limit_of_is_compact_absorbing
[ne_bot f]
{c : set β}
(hc₁ : is_compact c)
(hc₂ : «expr∃ , »((v «expr ∈ » f), «expr ⊆ »(closure (image2 ϕ v s), c)))
(hs : s.nonempty) : (exprω() f ϕ s).nonempty :=
begin
  rcases [expr hc₂, "with", "⟨", ident v, ",", ident hv₁, ",", ident hv₂, "⟩"],
  rw [expr omega_limit_eq_Inter_inter _ _ _ hv₁] [],
  apply [expr is_compact.nonempty_Inter_of_directed_nonempty_compact_closed],
  { rintro ["⟨", ident u₁, ",", ident hu₁, "⟩", "⟨", ident u₂, ",", ident hu₂, "⟩"],
    use [expr ⟨«expr ∩ »(u₁, u₂), inter_mem hu₁ hu₂⟩],
    split,
    all_goals { exact [expr closure_mono (image2_subset (inter_subset_inter_left _ (by simp [] [] [] [] [] [])) subset.rfl)] } },
  { intro [ident u],
    have [ident hn] [":", expr (image2 ϕ «expr ∩ »(u, v) s).nonempty] [],
    from [expr nonempty.image2 (nonempty_of_mem (inter_mem u.prop hv₁)) hs],
    exact [expr hn.mono subset_closure] },
  { intro ["_"],
    apply [expr compact_of_is_closed_subset hc₁ is_closed_closure],
    calc
      «expr ⊆ »(_, closure (image2 ϕ v s)) : closure_mono (image2_subset (inter_subset_right _ _) subset.rfl)
      «expr ⊆ »(..., c) : hv₂ },
  { exact [expr λ _, is_closed_closure] }
end

theorem nonempty_omega_limit [CompactSpace β] [ne_bot f] (hs : s.nonempty) : (ω f ϕ s).Nonempty :=
  nonempty_omega_limit_of_is_compact_absorbing _ _ _ compact_univ ⟨univ, univ_mem, subset_univ _⟩ hs

end OmegaLimit

/-!
### ω-limits of Flows by a Monoid
-/


namespace Flow

variable{τ :
    Type
      _}[TopologicalSpace
      τ][AddMonoidₓ τ][HasContinuousAdd τ]{α : Type _}[TopologicalSpace α](f : Filter τ)(ϕ : Flow τ α)(s : Set α)

open_locale OmegaLimit

theorem is_invariant_omega_limit (hf : ∀ t, tendsto ((·+·) t) f f) : IsInvariant ϕ (ω f ϕ s) :=
  fun t =>
    maps_to.mono (subset.refl _) (omega_limit_subset_of_tendsto ϕ s (hf t))$
      maps_to_omega_limit _ (maps_to_id _) (fun t' x => (ϕ.map_add _ _ _).symm) (continuous_const.Flow ϕ continuous_id)

theorem omega_limit_image_subset (t : τ) (ht : tendsto (·+t) f f) : ω f ϕ (ϕ t '' s) ⊆ ω f ϕ s :=
  by 
    simp only [omega_limit_image_eq, ←map_add]
    exact omega_limit_subset_of_tendsto ϕ s ht

end Flow

/-!
### ω-limits of Flows by a Group
-/


namespace Flow

variable{τ :
    Type
      _}[TopologicalSpace
      τ][AddCommGroupₓ τ][TopologicalAddGroup τ]{α : Type _}[TopologicalSpace α](f : Filter τ)(ϕ : Flow τ α)(s : Set α)

open_locale OmegaLimit

/-- the ω-limit of a forward image of `s` is the same as the ω-limit of `s`. -/
@[simp]
theorem omega_limit_image_eq (hf : ∀ t, tendsto (·+t) f f) (t : τ) : ω f ϕ (ϕ t '' s) = ω f ϕ s :=
  subset.antisymm (omega_limit_image_subset _ _ _ _ (hf t))$
    calc ω f ϕ s = ω f ϕ (ϕ (-t) '' (ϕ t '' s)) :=
      by 
        simp [image_image, ←map_add]
      _ ⊆ ω f ϕ (ϕ t '' s) := omega_limit_image_subset _ _ _ _ (hf _)
      

-- error in Dynamics.OmegaLimit: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem omega_limit_omega_limit
(hf : ∀ t, tendsto (((«expr + »)) t) f f) : «expr ⊆ »(exprω() f ϕ (exprω() f ϕ s), exprω() f ϕ s) :=
begin
  simp [] [] ["only"] ["[", expr subset_def, ",", expr mem_omega_limit_iff_frequently₂, ",", expr frequently_iff, "]"] [] [],
  intros ["_", ident h],
  rintro [ident n, ident hn, ident u, ident hu],
  rcases [expr mem_nhds_iff.mp hn, "with", "⟨", ident o, ",", ident ho₁, ",", ident ho₂, ",", ident ho₃, "⟩"],
  rcases [expr h o (is_open.mem_nhds ho₂ ho₃) hu, "with", "⟨", ident t, ",", ident ht₁, ",", ident ht₂, "⟩"],
  have [ident l₁] [":", expr «expr ∩ »(exprω() f ϕ s, o).nonempty] [],
  from [expr ht₂.mono (inter_subset_inter_left _ ((is_invariant_iff_image _ _).mp (is_invariant_omega_limit _ _ _ hf) _))],
  have [ident l₂] [":", expr «expr ∩ »(closure (image2 ϕ u s), o).nonempty] [":=", expr l₁.mono (λ
    b hb, ⟨omega_limit_subset_closure_fw_image _ _ _ hu hb.1, hb.2⟩)],
  have [ident l₃] [":", expr «expr ∩ »(o, image2 ϕ u s).nonempty] [],
  begin
    rcases [expr l₂, "with", "⟨", ident b, ",", ident hb₁, ",", ident hb₂, "⟩"],
    exact [expr mem_closure_iff_nhds.mp hb₁ o (is_open.mem_nhds ho₂ hb₂)]
  end,
  rcases [expr l₃, "with", "⟨", ident ϕra, ",", ident ho, ",", "⟨", "_", ",", "_", ",", ident hr, ",", ident ha, ",", ident hϕra, "⟩", "⟩"],
  exact [expr ⟨_, hr, ϕra, ⟨_, ha, hϕra⟩, ho₁ ho⟩]
end

end Flow

