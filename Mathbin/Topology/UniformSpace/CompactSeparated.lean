import Mathbin.Topology.UniformSpace.Separation 
import Mathbin.Topology.UniformSpace.UniformConvergence

/-!
# Compact separated uniform spaces

## Main statements

* `compact_space_uniformity`: On a separated compact uniform space, the topology determines the
  uniform structure, entourages are exactly the neighborhoods of the diagonal.
* `uniform_space_of_compact_t2`: every compact T2 topological structure is induced by a uniform
  structure. This uniform structure is described in the previous item.
* Heine-Cantor theorem: continuous functions on compact separated uniform spaces with values in
  uniform spaces are automatically uniformly continuous. There are several variations, the main one
  is `compact_space.uniform_continuous_of_continuous`.

## Implementation notes

The construction `uniform_space_of_compact_t2` is not declared as an instance, as it would badly
loop.

## tags

uniform space, uniform continuity, compact space
-/


open_locale Classical uniformity TopologicalSpace Filter

open Filter UniformSpace Set

variable {α β γ : Type _} [UniformSpace α] [UniformSpace β]

/-!
### Uniformity on compact separated spaces
-/


-- error in Topology.UniformSpace.CompactSeparated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- On a separated compact uniform space, the topology determines the uniform structure, entourages
are exactly the neighborhoods of the diagonal. -/
theorem compact_space_uniformity
[compact_space α]
[separated_space α] : «expr = »(expr𝓤() α, «expr⨆ , »((x : α), expr𝓝() (x, x))) :=
begin
  symmetry,
  refine [expr le_antisymm supr_nhds_le_uniformity _],
  by_contra [ident H],
  obtain ["⟨", ident V, ",", ident hV, ",", ident h, "⟩", ":", expr «expr∃ , »((V : set «expr × »(α, α)), «expr ∧ »(∀
     x : α, «expr ∈ »(V, expr𝓝() (x, x)), «expr ≠ »(«expr ⊓ »(expr𝓤() α, expr𝓟() «expr ᶜ»(V)), «expr⊥»())))],
  { simpa [] [] [] ["[", expr le_iff_forall_inf_principal_compl, "]"] [] ["using", expr H] },
  let [ident F] [] [":=", expr «expr ⊓ »(expr𝓤() α, expr𝓟() «expr ᶜ»(V))],
  haveI [] [":", expr ne_bot F] [":=", expr ⟨h⟩],
  obtain ["⟨", "⟨", ident x, ",", ident y, "⟩", ",", ident hx, "⟩", ":", expr «expr∃ , »((p : «expr × »(α, α)), cluster_pt p F), ":=", expr cluster_point_of_compact F],
  have [] [":", expr cluster_pt (x, y) (expr𝓤() α)] [":=", expr hx.of_inf_left],
  have [ident hxy] [":", expr «expr = »(x, y)] [":=", expr eq_of_uniformity_inf_nhds this],
  subst [expr hxy],
  have [] [":", expr cluster_pt (x, x) (expr𝓟() «expr ᶜ»(V))] [":=", expr hx.of_inf_right],
  have [] [":", expr «expr ∉ »((x, x), interior V)] [],
  { have [] [":", expr «expr ∈ »((x, x), closure «expr ᶜ»(V))] [],
    by rwa [expr mem_closure_iff_cluster_pt] [],
    rwa [expr closure_compl] ["at", ident this] },
  have [] [":", expr «expr ∈ »((x, x), interior V)] [],
  { rw [expr mem_interior_iff_mem_nhds] [],
    exact [expr hV x] },
  contradiction
end

-- error in Topology.UniformSpace.CompactSeparated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem unique_uniformity_of_compact_t2
[t : topological_space γ]
[compact_space γ]
[t2_space γ]
{u u' : uniform_space γ}
(h : «expr = »(u.to_topological_space, t))
(h' : «expr = »(u'.to_topological_space, t)) : «expr = »(u, u') :=
begin
  apply [expr uniform_space_eq],
  change [expr «expr = »(uniformity _, uniformity _)] [] [],
  haveI [] [":", expr @compact_space γ u.to_topological_space] [],
  { rw [expr h] []; assumption },
  haveI [] [":", expr @compact_space γ u'.to_topological_space] [],
  { rw [expr h'] []; assumption },
  haveI [] [":", expr @separated_space γ u] [],
  { rwa ["[", expr separated_iff_t2, ",", expr h, "]"] [] },
  haveI [] [":", expr @separated_space γ u'] [],
  { rwa ["[", expr separated_iff_t2, ",", expr h', "]"] [] },
  rw ["[", expr compact_space_uniformity, ",", expr compact_space_uniformity, ",", expr h, ",", expr h', "]"] []
end

-- error in Topology.UniformSpace.CompactSeparated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The unique uniform structure inducing a given compact Hausdorff topological structure. -/
def uniform_space_of_compact_t2 [topological_space γ] [compact_space γ] [t2_space γ] : uniform_space γ :=
{ uniformity := «expr⨆ , »((x), expr𝓝() (x, x)),
  refl := begin
    simp_rw ["[", expr filter.principal_le_iff, ",", expr mem_supr, "]"] [],
    rintros [ident V, ident V_in, "⟨", ident x, ",", "_", "⟩", "⟨", "⟩"],
    exact [expr mem_of_mem_nhds (V_in x)]
  end,
  symm := begin
    refine [expr le_of_eq _],
    rw [expr map_supr] [],
    congr' [] ["with", ident x, ":", 1],
    erw ["[", expr nhds_prod_eq, ",", "<-", expr prod_comm, "]"] []
  end,
  comp := begin
    set [] [ident 𝓝Δ] [] [":="] [expr «expr⨆ , »((x : γ), expr𝓝() (x, x))] [],
    set [] [ident F] [] [":="] [expr 𝓝Δ.lift' (λ s : set «expr × »(γ, γ), «expr ○ »(s, s))] [],
    rw [expr le_iff_forall_inf_principal_compl] [],
    intros [ident V, ident V_in],
    by_contra [ident H],
    haveI [] [":", expr ne_bot «expr ⊓ »(F, expr𝓟() «expr ᶜ»(V))] [":=", expr ⟨H⟩],
    obtain ["⟨", "⟨", ident x, ",", ident y, "⟩", ",", ident hxy, "⟩", ":", expr «expr∃ , »((p : «expr × »(γ, γ)), cluster_pt p «expr ⊓ »(F, expr𝓟() «expr ᶜ»(V))), ":=", expr cluster_point_of_compact _],
    have [ident clV] [":", expr cluster_pt (x, y) «expr $ »(expr𝓟(), «expr ᶜ»(V))] [":=", expr hxy.of_inf_right],
    have [] [":", expr «expr ∉ »((x, y), interior V)] [],
    { have [] [":", expr «expr ∈ »((x, y), closure «expr ᶜ»(V))] [],
      by rwa [expr mem_closure_iff_cluster_pt] [],
      rwa [expr closure_compl] ["at", ident this] },
    have [ident diag_subset] [":", expr «expr ⊆ »(diagonal γ, interior V)] [],
    { rw [expr subset_interior_iff_nhds] [],
      rintros ["⟨", ident x, ",", ident x, "⟩", "⟨", "⟩"],
      exact [expr (mem_supr.mp V_in : _) x] },
    have [ident x_ne_y] [":", expr «expr ≠ »(x, y)] [],
    { intro [ident h],
      apply [expr this],
      apply [expr diag_subset],
      simp [] [] [] ["[", expr h, "]"] [] [] },
    haveI [] [":", expr normal_space γ] [":=", expr normal_of_compact_t2],
    obtain ["⟨", ident U₁, ",", ident V₁, ",", ident U₁_in, ",", ident V₁_in, ",", ident U₂, ",", ident V₂, ",", ident U₂_in₂, ",", ident V₂_in, ",", ident V₁_cl, ",", ident V₂_cl, ",", ident U₁_op, ",", ident U₂_op, ",", ident VU₁, ",", ident VU₂, ",", ident hU₁₂, "⟩", ":", expr «expr∃ , »((U₁
       V₁ «expr ∈ » expr𝓝() x)
      (U₂
       V₂ «expr ∈ » expr𝓝() y), «expr ∧ »(is_closed V₁, «expr ∧ »(is_closed V₂, «expr ∧ »(is_open U₁, «expr ∧ »(is_open U₂, «expr ∧ »(«expr ⊆ »(V₁, U₁), «expr ∧ »(«expr ⊆ »(V₂, U₂), «expr = »(«expr ∩ »(U₁, U₂), «expr∅»())))))))), ":=", expr disjoint_nested_nhds x_ne_y],
    let [ident U₃] [] [":=", expr «expr ᶜ»(«expr ∪ »(V₁, V₂))],
    have [ident U₃_op] [":", expr is_open U₃] [":=", expr is_open_compl_iff.mpr (is_closed.union V₁_cl V₂_cl)],
    let [ident W] [] [":=", expr «expr ∪ »(«expr ∪ »(U₁.prod U₁, U₂.prod U₂), U₃.prod U₃)],
    have [ident W_in] [":", expr «expr ∈ »(W, 𝓝Δ)] [],
    { rw [expr mem_supr] [],
      intros [ident x],
      apply [expr is_open.mem_nhds (is_open.union (is_open.union _ _) _)],
      { by_cases [expr hx, ":", expr «expr ∈ »(x, «expr ∪ »(V₁, V₂))],
        { left,
          cases [expr hx] ["with", ident hx, ident hx]; [left, right]; split; tauto [] },
        { right,
          rw [expr mem_prod] [],
          tauto [] } },
      all_goals { simp [] [] ["only"] ["[", expr is_open.prod, ",", "*", "]"] [] [] } },
    have [] [":", expr «expr ∈ »(«expr ○ »(W, W), F)] [],
    by simpa [] [] ["only"] [] [] ["using", expr mem_lift' W_in],
    have [ident hV₁₂] [":", expr «expr ∈ »(V₁.prod V₂, expr𝓝() (x, y))] [":=", expr prod_is_open.mem_nhds V₁_in V₂_in],
    have [ident clF] [":", expr cluster_pt (x, y) F] [":=", expr hxy.of_inf_left],
    obtain ["⟨", ident p, ",", ident p_in, "⟩", ":", expr «expr∃ , »((p), «expr ∈ »(p, «expr ∩ »(V₁.prod V₂, «expr ○ »(W, W)))), ":=", expr cluster_pt_iff.mp clF hV₁₂ this],
    have [ident inter_empty] [":", expr «expr = »(«expr ∩ »(V₁.prod V₂, «expr ○ »(W, W)), «expr∅»())] [],
    { rw [expr eq_empty_iff_forall_not_mem] [],
      rintros ["⟨", ident u, ",", ident v, "⟩", "⟨", "⟨", ident u_in, ",", ident v_in, "⟩", ",", ident w, ",", ident huw, ",", ident hwv, "⟩"],
      have [ident uw_in] [":", expr «expr ∈ »((u, w), U₁.prod U₁)] [":=", expr set.mem_prod.2 ((huw.resolve_right (λ
          h, «expr $ »(h.1, or.inl u_in))).resolve_right (λ
         h, have «expr ∈ »(u, «expr ∩ »(U₁, U₂)), from ⟨VU₁ u_in, h.1⟩,
         by rwa [expr hU₁₂] ["at", ident this]))],
      have [ident wv_in] [":", expr «expr ∈ »((w, v), U₂.prod U₂)] [":=", expr set.mem_prod.2 ((hwv.resolve_right (λ
          h, «expr $ »(h.2, or.inr v_in))).resolve_left (λ
         h, have «expr ∈ »(v, «expr ∩ »(U₁, U₂)), from ⟨h.2, VU₂ v_in⟩,
         by rwa [expr hU₁₂] ["at", ident this]))],
      have [] [":", expr «expr ∈ »(w, «expr ∩ »(U₁, U₂))] [":=", expr ⟨uw_in.2, wv_in.1⟩],
      rwa [expr hU₁₂] ["at", ident this] },
    rwa [expr inter_empty] ["at", ident p_in]
  end,
  is_open_uniformity := begin
    suffices [] [":", expr ∀ x : γ, «expr = »(filter.comap (prod.mk x) «expr⨆ , »((y), expr𝓝() (y, y)), expr𝓝() x)],
    { intros [ident s],
      change [expr «expr ↔ »(is_open s, _)] [] [],
      simp_rw ["[", expr is_open_iff_mem_nhds, ",", expr nhds_eq_comap_uniformity_aux, ",", expr this, "]"] [] },
    intros [ident x],
    simp_rw ["[", expr comap_supr, ",", expr nhds_prod_eq, ",", expr comap_prod, ",", expr show «expr = »(«expr ∘ »(prod.fst, prod.mk x), λ
      y : γ, x), by ext [] [] []; simp [] [] [] [] [] [], ",", expr show «expr = »(«expr ∘ »(prod.snd, prod.mk x), (id : γ → γ)), by ext [] [] []; refl, ",", expr comap_id, "]"] [],
    rw ["[", expr supr_split_single _ x, ",", expr comap_const_of_mem (λ V, mem_of_mem_nhds), "]"] [],
    suffices [] [":", expr ∀ y «expr ≠ » x, «expr ≤ »(«expr ⊓ »(comap (λ y : γ, x) (expr𝓝() y), expr𝓝() y), expr𝓝() x)],
    by simpa [] [] [] [] [] [],
    intros [ident y, ident hxy],
    simp [] [] [] ["[", expr comap_const_of_not_mem (compl_singleton_mem_nhds hxy) (by simp [] [] [] [] [] []), "]"] [] []
  end }

/-!
### Heine-Cantor theorem
-/


/-- Heine-Cantor: a continuous function on a compact separated uniform space is uniformly
continuous. -/
theorem CompactSpace.uniform_continuous_of_continuous [CompactSpace α] [SeparatedSpace α] {f : α → β}
  (h : Continuous f) : UniformContinuous f :=
  calc map (Prod.map f f) (𝓤 α) = map (Prod.map f f) (⨆x, 𝓝 (x, x)) :=
    by 
      rw [compact_space_uniformity]
    _ = ⨆x, map (Prod.map f f) (𝓝 (x, x)) :=
    by 
      rw [map_supr]
    _ ≤ ⨆x, 𝓝 (f x, f x) := supr_le_supr fun x => (h.prod_map h).ContinuousAt 
    _ ≤ ⨆y, 𝓝 (y, y) := supr_comp_le (fun y => 𝓝 (y, y)) f 
    _ ≤ 𝓤 β := supr_nhds_le_uniformity
    

/-- Heine-Cantor: a continuous function on a compact separated set of a uniform space is
uniformly continuous. -/
theorem IsCompact.uniform_continuous_on_of_continuous' {s : Set α} {f : α → β} (hs : IsCompact s) (hs' : IsSeparated s)
  (hf : ContinuousOn f s) : UniformContinuousOn f s :=
  by 
    rw [uniform_continuous_on_iff_restrict]
    rw [is_separated_iff_induced] at hs' 
    rw [is_compact_iff_compact_space] at hs 
    rw [continuous_on_iff_continuous_restrict] at hf 
    skip 
    exact CompactSpace.uniform_continuous_of_continuous hf

/-- Heine-Cantor: a continuous function on a compact set of a separated uniform space
is uniformly continuous. -/
theorem IsCompact.uniform_continuous_on_of_continuous [SeparatedSpace α] {s : Set α} {f : α → β} (hs : IsCompact s)
  (hf : ContinuousOn f s) : UniformContinuousOn f s :=
  hs.uniform_continuous_on_of_continuous' (is_separated_of_separated_space s) hf

-- error in Topology.UniformSpace.CompactSeparated: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A family of functions `α → β → γ` tends uniformly to its value at `x` if `α` is locally compact,
`β` is compact and separated and `f` is continuous on `U × (univ : set β)` for some separated
neighborhood `U` of `x`. -/
theorem continuous_on.tendsto_uniformly
[locally_compact_space α]
[compact_space β]
[separated_space β]
[uniform_space γ]
{f : α → β → γ}
{x : α}
{U : set α}
(hxU : «expr ∈ »(U, expr𝓝() x))
(hU : is_separated U)
(h : continuous_on «expr↿ »(f) (U.prod univ)) : tendsto_uniformly f (f x) (expr𝓝() x) :=
begin
  rcases [expr locally_compact_space.local_compact_nhds _ _ hxU, "with", "⟨", ident K, ",", ident hxK, ",", ident hKU, ",", ident hK, "⟩"],
  have [] [":", expr uniform_continuous_on «expr↿ »(f) (K.prod univ)] [],
  { refine [expr is_compact.uniform_continuous_on_of_continuous' (hK.prod compact_univ) _ «expr $ »(h.mono, prod_mono hKU subset.rfl)],
    exact [expr (hU.mono hKU).prod (is_separated_of_separated_space _)] },
  exact [expr this.tendsto_uniformly hxK]
end

/-- A continuous family of functions `α → β → γ` tends uniformly to its value at `x` if `α` is
locally compact and `β` is compact and separated. -/
theorem Continuous.tendsto_uniformly [SeparatedSpace α] [LocallyCompactSpace α] [CompactSpace β] [SeparatedSpace β]
  [UniformSpace γ] (f : α → β → γ) (h : Continuous («expr↿ » f)) (x : α) : TendstoUniformly f (f x) (𝓝 x) :=
  h.continuous_on.tendsto_uniformly univ_mem$ is_separated_of_separated_space _

