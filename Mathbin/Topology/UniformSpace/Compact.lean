/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov

! This file was ported from Lean 3 source module topology.uniform_space.compact
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.UniformSpace.UniformConvergence
import Mathbin.Topology.UniformSpace.Equicontinuity
import Mathbin.Topology.Separation

/-!
# Compact separated uniform spaces

## Main statements

* `compact_space_uniformity`: On a compact uniform space, the topology determines the
  uniform structure, entourages are exactly the neighborhoods of the diagonal.

* `uniform_space_of_compact_t2`: every compact T2 topological structure is induced by a uniform
  structure. This uniform structure is described in the previous item.

* **Heine-Cantor** theorem: continuous functions on compact uniform spaces with values in uniform
  spaces are automatically uniformly continuous. There are several variations, the main one is
  `compact_space.uniform_continuous_of_continuous`.

## Implementation notes

The construction `uniform_space_of_compact_t2` is not declared as an instance, as it would badly
loop.

## tags

uniform space, uniform continuity, compact space
-/


open Classical uniformity TopologicalSpace Filter

open Filter UniformSpace Set

variable {α β γ : Type _} [UniformSpace α] [UniformSpace β]

/-!
### Uniformity on compact spaces
-/


/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- On a compact uniform space, the topology determines the uniform structure, entourages are
exactly the neighborhoods of the diagonal. -/
theorem nhdsSet_diagonal_eq_uniformity [CompactSpace α] : 𝓝ˢ (diagonal α) = 𝓤 α :=
  by
  refine' nhds_set_diagonal_le_uniformity.antisymm _
  have :
    (𝓤 (α × α)).HasBasis (fun U => U ∈ 𝓤 α) fun U =>
      (fun p : (α × α) × α × α => ((p.1.1, p.2.1), p.1.2, p.2.2)) ⁻¹' U ×ˢ U :=
    by
    rw [uniformity_prod_eq_comap_prod]
    exact (𝓤 α).basis_sets.prod_self.comap _
  refine' (is_compact_diagonal.nhds_set_basis_uniformity this).ge_iff.2 fun U hU => _
  exact mem_of_superset hU fun ⟨x, y⟩ hxy => mem_Union₂.2 ⟨(x, x), rfl, refl_mem_uniformity hU, hxy⟩
#align nhds_set_diagonal_eq_uniformity nhdsSet_diagonal_eq_uniformity

/-- On a compact uniform space, the topology determines the uniform structure, entourages are
exactly the neighborhoods of the diagonal. -/
theorem compactSpace_uniformity [CompactSpace α] : 𝓤 α = ⨆ x, 𝓝 (x, x) :=
  nhdsSet_diagonal_eq_uniformity.symm.trans (nhdsSet_diagonal _)
#align compact_space_uniformity compactSpace_uniformity

theorem unique_uniformity_of_compact [t : TopologicalSpace γ] [CompactSpace γ]
    {u u' : UniformSpace γ} (h : u.toTopologicalSpace = t) (h' : u'.toTopologicalSpace = t) :
    u = u' := by
  apply uniformSpace_eq
  change uniformity _ = uniformity _
  have : @CompactSpace γ u.to_topological_space := by rwa [h]
  have : @CompactSpace γ u'.to_topological_space := by rwa [h']
  rw [compactSpace_uniformity, compactSpace_uniformity, h, h']
#align unique_uniformity_of_compact unique_uniformity_of_compact

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (y «expr ≠ » x) -/
/-- The unique uniform structure inducing a given compact topological structure. -/
def uniformSpaceOfCompactT2 [TopologicalSpace γ] [CompactSpace γ] [T2Space γ] : UniformSpace γ
    where
  uniformity := ⨆ x, 𝓝 (x, x)
  refl := by
    simp_rw [Filter.principal_le_iff, mem_supr]
    rintro V V_in ⟨x, _⟩ ⟨⟩
    exact mem_of_mem_nhds (V_in x)
  symm := by
    refine' le_of_eq _
    rw [Filter.map_supᵢ]
    congr with x : 1
    erw [nhds_prod_eq, ← prod_comm]
  comp :=
    by
    /-
        This is the difficult part of the proof. We need to prove that, for each neighborhood W
        of the diagonal Δ, W ○ W is still a neighborhood of the diagonal.
        -/
    set 𝓝Δ := ⨆ x : γ, 𝓝 (x, x)
    -- The filter of neighborhoods of Δ
    set F := 𝓝Δ.lift' fun s : Set (γ × γ) => s ○ s
    -- Compositions of neighborhoods of Δ
    -- If this weren't true, then there would be V ∈ 𝓝Δ such that F ⊓ 𝓟 Vᶜ ≠ ⊥
    rw [le_iff_forall_inf_principal_compl]
    intro V V_in
    by_contra H
    haveI : ne_bot (F ⊓ 𝓟 (Vᶜ)) := ⟨H⟩
    -- Hence compactness would give us a cluster point (x, y) for F ⊓ 𝓟 Vᶜ
    obtain ⟨⟨x, y⟩, hxy⟩ : ∃ p : γ × γ, ClusterPt p (F ⊓ 𝓟 (Vᶜ)) := cluster_point_of_compact _
    -- In particular (x, y) is a cluster point of 𝓟 Vᶜ, hence is not in the interior of V,
    -- and a fortiori not in Δ, so x ≠ y
    have clV : ClusterPt (x, y) (𝓟 <| Vᶜ) := hxy.of_inf_right
    have : (x, y) ∉ interior V :=
      by
      have : (x, y) ∈ closure (Vᶜ) := by rwa [mem_closure_iff_clusterPt]
      rwa [closure_compl] at this
    have diag_subset : diagonal γ ⊆ interior V :=
      by
      rw [subset_interior_iff_nhds]
      rintro ⟨x, x⟩ ⟨⟩
      exact (mem_supr.mp V_in : _) x
    have x_ne_y : x ≠ y := by
      intro h
      apply this
      apply diag_subset
      simp [h]
    -- Since γ is compact and Hausdorff, it is normal, hence T₃.
    haveI : NormalSpace γ := normalOfCompactT2
    -- So there are closed neighboords V₁ and V₂ of x and y contained in disjoint open neighborhoods
    -- U₁ and U₂.
    obtain
      ⟨U₁, U₁_in, V₁, V₁_in, U₂, U₂_in₂, V₂, V₂_in, V₁_cl, V₂_cl, U₁_op, U₂_op, VU₁, VU₂, hU₁₂⟩ :=
      disjoint_nested_nhds x_ne_y
    -- We set U₃ := (V₁ ∪ V₂)ᶜ so that W := U₁ ×ˢ U₁ ∪ U₂ ×ˢ U₂ ∪ U₃ ×ˢ U₃ is an open
    -- neighborhood of Δ.
    let U₃ := (V₁ ∪ V₂)ᶜ
    have U₃_op : IsOpen U₃ := is_open_compl_iff.mpr (IsClosed.union V₁_cl V₂_cl)
    let W := U₁ ×ˢ U₁ ∪ U₂ ×ˢ U₂ ∪ U₃ ×ˢ U₃
    have W_in : W ∈ 𝓝Δ := by
      rw [mem_supr]
      intro x
      apply IsOpen.mem_nhds (IsOpen.union (IsOpen.union _ _) _)
      · by_cases hx : x ∈ V₁ ∪ V₂
        · left
          cases' hx with hx hx <;> [left, right] <;> constructor <;> tauto
        · right
          rw [mem_prod]
          tauto
      all_goals simp only [IsOpen.prod, *]
    -- So W ○ W ∈ F by definition of F
    have : W ○ W ∈ F := by simpa only using mem_lift' W_in
    -- And V₁ ×ˢ V₂ ∈ 𝓝 (x, y)
    have hV₁₂ : V₁ ×ˢ V₂ ∈ 𝓝 (x, y) := prod_mem_nhds V₁_in V₂_in
    -- But (x, y) is also a cluster point of F so (V₁ ×ˢ V₂) ∩ (W ○ W) ≠ ∅
    -- However the construction of W implies (V₁ ×ˢ V₂) ∩ (W ○ W) = ∅.
    -- Indeed assume for contradiction there is some (u, v) in the intersection.
    obtain ⟨⟨u, v⟩, ⟨u_in, v_in⟩, w, huw, hwv⟩ := cluster_pt_iff.mp hxy.of_inf_left hV₁₂ this
    -- So u ∈ V₁, v ∈ V₂, and there exists some w such that (u, w) ∈ W and (w ,v) ∈ W.
    -- Because u is in V₁ which is disjoint from U₂ and U₃, (u, w) ∈ W forces (u, w) ∈ U₁ ×ˢ U₁.
    have uw_in : (u, w) ∈ U₁ ×ˢ U₁ :=
      (huw.resolve_right fun h => h.1 <| Or.inl u_in).resolve_right fun h =>
        hU₁₂.le_bot ⟨VU₁ u_in, h.1⟩
    -- Similarly, because v ∈ V₂, (w ,v) ∈ W forces (w, v) ∈ U₂ ×ˢ U₂.
    have wv_in : (w, v) ∈ U₂ ×ˢ U₂ :=
      (hwv.resolve_right fun h => h.2 <| Or.inr v_in).resolve_left fun h =>
        hU₁₂.le_bot ⟨h.2, VU₂ v_in⟩
    -- Hence w ∈ U₁ ∩ U₂ which is empty.
    -- So we have a contradiction
    exact hU₁₂.le_bot ⟨uw_in.2, wv_in.1⟩
  is_open_uniformity :=
    by
    -- Here we need to prove the topology induced by the constructed uniformity is the
    -- topology we started with.
    suffices ∀ x : γ, Filter.comap (Prod.mk x) (⨆ y, 𝓝 (y, y)) = 𝓝 x
      by
      intro s
      change IsOpen s ↔ _
      simp_rw [isOpen_iff_mem_nhds, nhds_eq_comap_uniformity_aux, this]
    intro x
    simp_rw [comap_supr, nhds_prod_eq, comap_prod,
      show Prod.fst ∘ Prod.mk x = fun y : γ => x by ext <;> simp,
      show Prod.snd ∘ Prod.mk x = (id : γ → γ) by ext <;> rfl, comap_id]
    rw [supᵢ_split_single _ x, comap_const_of_mem fun V => mem_of_mem_nhds]
    suffices ∀ (y) (_ : y ≠ x), comap (fun y : γ => x) (𝓝 y) ⊓ 𝓝 y ≤ 𝓝 x by simpa
    intro y hxy
    simp [comap_const_of_not_mem (compl_singleton_mem_nhds hxy) (by simp)]
#align uniform_space_of_compact_t2 uniformSpaceOfCompactT2

/-!
### Heine-Cantor theorem
-/


/-- Heine-Cantor: a continuous function on a compact uniform space is uniformly
continuous. -/
theorem CompactSpace.uniformContinuous_of_continuous [CompactSpace α] {f : α → β}
    (h : Continuous f) : UniformContinuous f :=
  calc
    map (Prod.map f f) (𝓤 α) = map (Prod.map f f) (⨆ x, 𝓝 (x, x)) := by rw [compactSpace_uniformity]
    _ = ⨆ x, map (Prod.map f f) (𝓝 (x, x)) := by rw [Filter.map_supᵢ]
    _ ≤ ⨆ x, 𝓝 (f x, f x) := supᵢ_mono fun x => (h.prod_map h).ContinuousAt
    _ ≤ ⨆ y, 𝓝 (y, y) := supᵢ_comp_le (fun y => 𝓝 (y, y)) f
    _ ≤ 𝓤 β := supᵢ_nhds_le_uniformity
    
#align compact_space.uniform_continuous_of_continuous CompactSpace.uniformContinuous_of_continuous

/-- Heine-Cantor: a continuous function on a compact set of a uniform space is uniformly
continuous. -/
theorem IsCompact.uniformContinuousOn_of_continuous {s : Set α} {f : α → β} (hs : IsCompact s)
    (hf : ContinuousOn f s) : UniformContinuousOn f s :=
  by
  rw [uniformContinuousOn_iff_restrict]
  rw [isCompact_iff_compactSpace] at hs
  rw [continuousOn_iff_continuous_restrict] at hf
  skip
  exact CompactSpace.uniformContinuous_of_continuous hf
#align is_compact.uniform_continuous_on_of_continuous IsCompact.uniformContinuousOn_of_continuous

/-- If `s` is compact and `f` is continuous at all points of `s`, then `f` is
"uniformly continuous at the set `s`", i.e. `f x` is close to `f y` whenever `x ∈ s` and `y` is
close to `x` (even if `y` is not itself in `s`, so this is a stronger assertion than
`uniform_continuous_on s`). -/
theorem IsCompact.uniform_continuousAt_of_continuousAt {r : Set (β × β)} {s : Set α}
    (hs : IsCompact s) (f : α → β) (hf : ∀ a ∈ s, ContinuousAt f a) (hr : r ∈ 𝓤 β) :
    { x : α × α | x.1 ∈ s → (f x.1, f x.2) ∈ r } ∈ 𝓤 α :=
  by
  obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
  choose U hU T hT hb using fun a ha =>
    exists_mem_nhds_ball_subset_of_mem_nhds ((hf a ha).preimage_mem_nhds <| mem_nhds_left _ ht)
  obtain ⟨fs, hsU⟩ := hs.elim_nhds_subcover' U hU
  apply mem_of_superset ((bInter_finset_mem fs).2 fun a _ => hT a a.2)
  rintro ⟨a₁, a₂⟩ h h₁
  obtain ⟨a, ha, haU⟩ := Set.mem_unionᵢ₂.1 (hsU h₁)
  apply htr
  refine' ⟨f a, htsymm.mk_mem_comm.1 (hb _ _ _ haU _), hb _ _ _ haU _⟩
  exacts[mem_ball_self _ (hT a a.2), mem_Inter₂.1 h a ha]
#align is_compact.uniform_continuous_at_of_continuous_at IsCompact.uniform_continuousAt_of_continuousAt

theorem Continuous.uniformContinuous_of_zero_at_infty {f : α → β} [Zero β] (h_cont : Continuous f)
    (h_zero : Tendsto f (cocompact α) (𝓝 0)) : UniformContinuous f :=
  uniformContinuous_def.2 fun r hr =>
    by
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    obtain ⟨s, hs, hst⟩ := mem_cocompact.1 (h_zero <| mem_nhds_left 0 ht)
    apply
      mem_of_superset
        (symmetrize_mem_uniformity <|
          (hs.uniform_continuous_at_of_continuous_at f fun _ _ => h_cont.continuous_at) <|
            symmetrize_mem_uniformity hr)
    rintro ⟨b₁, b₂⟩ h
    by_cases h₁ : b₁ ∈ s; · exact (h.1 h₁).1
    by_cases h₂ : b₂ ∈ s; · exact (h.2 h₂).2
    apply htr
    exact ⟨0, htsymm.mk_mem_comm.1 (hst h₁), hst h₂⟩
#align continuous.uniform_continuous_of_zero_at_infty Continuous.uniformContinuous_of_zero_at_infty

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A family of functions `α → β → γ` tends uniformly to its value at `x` if `α` is locally compact,
`β` is compact and `f` is continuous on `U × (univ : set β)` for some neighborhood `U` of `x`. -/
theorem ContinuousOn.tendstoUniformly [LocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
    {f : α → β → γ} {x : α} {U : Set α} (hxU : U ∈ 𝓝 x) (h : ContinuousOn (↿f) (U ×ˢ univ)) :
    TendstoUniformly f (f x) (𝓝 x) :=
  by
  rcases LocallyCompactSpace.local_compact_nhds _ _ hxU with ⟨K, hxK, hKU, hK⟩
  have : UniformContinuousOn (↿f) (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ)
      (h.mono <| prod_mono hKU subset.rfl)
  exact this.tendsto_uniformly hxK
#align continuous_on.tendsto_uniformly ContinuousOn.tendstoUniformly

/-- A continuous family of functions `α → β → γ` tends uniformly to its value at `x` if `α` is
locally compact and `β` is compact. -/
theorem Continuous.tendstoUniformly [LocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
    (f : α → β → γ) (h : Continuous ↿f) (x : α) : TendstoUniformly f (f x) (𝓝 x) :=
  h.ContinuousOn.TendstoUniformly univ_mem
#align continuous.tendsto_uniformly Continuous.tendstoUniformly

section UniformConvergence

/-- An equicontinuous family of functions defined on a compact uniform space is automatically
uniformly equicontinuous. -/
theorem CompactSpace.uniformEquicontinuous_of_equicontinuous {ι : Type _} {F : ι → β → α}
    [CompactSpace β] (h : Equicontinuous F) : UniformEquicontinuous F :=
  by
  rw [equicontinuous_iff_continuous] at h
  rw [uniformEquicontinuous_iff_uniformContinuous]
  exact CompactSpace.uniformContinuous_of_continuous h
#align compact_space.uniform_equicontinuous_of_equicontinuous CompactSpace.uniformEquicontinuous_of_equicontinuous

end UniformConvergence

