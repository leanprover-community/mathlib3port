import Mathbin.Topology.Separation 
import Mathbin.Topology.Opens

/-!
# The Alexandroff Compactification

We construct the Alexandroff compactification (the one-point compactification) of an arbitrary
topological space `X` and prove some properties inherited from `X`.

## Main definitions

* `alexandroff`: the Alexandroff compactification, we use coercion for the canonical embedding
  `X → alexandroff X`; when `X` is already compact, the compactification adds an isolated point
  to the space.
* `alexandroff.infty`: the extra point

## Main results

* The topological structure of `alexandroff X`
* The connectedness of `alexandroff X` for a noncompact, preconnected `X`
* `alexandroff X` is `T₀` for a T₀ space `X`
* `alexandroff X` is `T₁` for a T₁ space `X`
* `alexandroff X` is normal if `X` is a locally compact Hausdorff space

## Tags

one-point compactification, compactness
-/


open Set Filter

open_locale Classical TopologicalSpace Filter

/-!
### Definition and basic properties

In this section we define `alexandroff X` to be the disjoint union of `X` and `∞`, implemented as
`option X`. Then we restate some lemmas about `option X` for `alexandroff X`.
-/


/-- The Alexandroff extension of an arbitrary topological space `X` -/
def Alexandroff (X : Type _) :=
  Option X

namespace Alexandroff

variable {X : Type _}

/-- The point at infinity -/
def infty : Alexandroff X :=
  none

localized [Alexandroff] notation "∞" => Alexandroff.infty

instance : CoeTₓ X (Alexandroff X) :=
  ⟨Option.some⟩

instance : Inhabited (Alexandroff X) :=
  ⟨∞⟩

theorem coe_injective : Function.Injective (coeₓ : X → Alexandroff X) :=
  Option.some_injective X

@[normCast]
theorem coe_eq_coe {x y : X} : (x : Alexandroff X) = y ↔ x = y :=
  coe_injective.eq_iff

@[simp]
theorem coe_ne_infty (x : X) : (x : Alexandroff X) ≠ ∞ :=
  fun.

@[simp]
theorem infty_ne_coe (x : X) : ∞ ≠ (x : Alexandroff X) :=
  fun.

/-- Recursor for `alexandroff` using the preferred forms `∞` and `↑x`. -/
@[elab_as_eliminator]
protected def rec (C : Alexandroff X → Sort _) (h₁ : C ∞) (h₂ : ∀ x : X, C x) : ∀ z : Alexandroff X, C z :=
  Option.rec h₁ h₂

theorem is_compl_range_coe_infty : IsCompl (range (coeₓ : X → Alexandroff X)) {∞} :=
  is_compl_range_some_none X

@[simp]
theorem range_coe_union_infty : range (coeₓ : X → Alexandroff X) ∪ {∞} = univ :=
  range_some_union_none X

@[simp]
theorem range_coe_inter_infty : range (coeₓ : X → Alexandroff X) ∩ {∞} = ∅ :=
  range_some_inter_none X

@[simp]
theorem compl_range_coe : range (coeₓ : X → Alexandroff X)ᶜ = {∞} :=
  compl_range_some X

theorem compl_infty : ({∞}ᶜ : Set (Alexandroff X)) = range (coeₓ : X → Alexandroff X) :=
  (@is_compl_range_coe_infty X).symm.compl_eq

theorem compl_image_coe (s : Set X) : (coeₓ '' s : Set (Alexandroff X))ᶜ = coeₓ '' sᶜ ∪ {∞} :=
  by 
    rw [coe_injective.compl_image_eq, compl_range_coe]

theorem ne_infty_iff_exists {x : Alexandroff X} : x ≠ ∞ ↔ ∃ y : X, (y : Alexandroff X) = x :=
  by 
    induction x using Alexandroff.rec <;> simp 

instance : CanLift (Alexandroff X) X :=
  { coe := coeₓ, cond := fun x => x ≠ ∞, prf := fun x => ne_infty_iff_exists.1 }

theorem not_mem_range_coe_iff {x : Alexandroff X} : x ∉ range (coeₓ : X → Alexandroff X) ↔ x = ∞ :=
  by 
    rw [←mem_compl_iff, compl_range_coe, mem_singleton_iff]

theorem infty_not_mem_range_coe : ∞ ∉ range (coeₓ : X → Alexandroff X) :=
  not_mem_range_coe_iff.2 rfl

theorem infty_not_mem_image_coe {s : Set X} : ∞ ∉ (coeₓ : X → Alexandroff X) '' s :=
  not_mem_subset (image_subset_range _ _) infty_not_mem_range_coe

@[simp]
theorem coe_preimage_infty : (coeₓ : X → Alexandroff X) ⁻¹' {∞} = ∅ :=
  by 
    ext 
    simp 

/-!
### Topological space structure on `alexandroff X`

We define a topological space structure on `alexandroff X` so that `s` is open if and only if

* `coe ⁻¹' s` is open in `X`;
* if `∞ ∈ s`, then `(coe ⁻¹' s)ᶜ` is compact.

Then we reformulate this definition in a few different ways, and prove that
`coe : X → alexandroff X` is an open embedding. If `X` is not a compact space, then we also prove
that `coe` has dense range, so it is a dense embedding.
-/


variable [TopologicalSpace X]

instance : TopologicalSpace (Alexandroff X) :=
  { IsOpen :=
      fun s => (∞ ∈ s → IsCompact (((coeₓ : X → Alexandroff X) ⁻¹' s)ᶜ)) ∧ IsOpen ((coeₓ : X → Alexandroff X) ⁻¹' s),
    is_open_univ :=
      by 
        simp ,
    is_open_inter :=
      fun s t =>
        by 
          rintro ⟨hms, hs⟩ ⟨hmt, ht⟩
          refine' ⟨_, hs.inter ht⟩
          rintro ⟨hms', hmt'⟩
          simpa [compl_inter] using (hms hms').union (hmt hmt'),
    is_open_sUnion :=
      fun S ho =>
        by 
          suffices  : IsOpen (coeₓ ⁻¹' ⋃₀S : Set X)
          ·
            refine' ⟨_, this⟩
            rintro ⟨s, hsS : s ∈ S, hs : ∞ ∈ s⟩
            refine' compact_of_is_closed_subset ((ho s hsS).1 hs) this.is_closed_compl _ 
            exact compl_subset_compl.mpr (preimage_mono$ subset_sUnion_of_mem hsS)
          rw [preimage_sUnion]
          exact is_open_bUnion fun s hs => (ho s hs).2 }

variable {s : Set (Alexandroff X)} {t : Set X}

theorem is_open_def : IsOpen s ↔ (∞ ∈ s → IsCompact ((coeₓ ⁻¹' s : Set X)ᶜ)) ∧ IsOpen (coeₓ ⁻¹' s : Set X) :=
  Iff.rfl

theorem is_open_iff_of_mem' (h : ∞ ∈ s) : IsOpen s ↔ IsCompact ((coeₓ ⁻¹' s : Set X)ᶜ) ∧ IsOpen (coeₓ ⁻¹' s : Set X) :=
  by 
    simp [is_open_def, h]

theorem is_open_iff_of_mem (h : ∞ ∈ s) :
  IsOpen s ↔ IsClosed ((coeₓ ⁻¹' s : Set X)ᶜ) ∧ IsCompact ((coeₓ ⁻¹' s : Set X)ᶜ) :=
  by 
    simp only [is_open_iff_of_mem' h, is_closed_compl_iff, And.comm]

theorem is_open_iff_of_not_mem (h : ∞ ∉ s) : IsOpen s ↔ IsOpen (coeₓ ⁻¹' s : Set X) :=
  by 
    simp [is_open_def, h]

theorem is_closed_iff_of_mem (h : ∞ ∈ s) : IsClosed s ↔ IsClosed (coeₓ ⁻¹' s : Set X) :=
  have  : ∞ ∉ sᶜ := fun H => H h 
  by 
    rw [←is_open_compl_iff, is_open_iff_of_not_mem this, ←is_open_compl_iff, preimage_compl]

theorem is_closed_iff_of_not_mem (h : ∞ ∉ s) :
  IsClosed s ↔ IsClosed (coeₓ ⁻¹' s : Set X) ∧ IsCompact (coeₓ ⁻¹' s : Set X) :=
  by 
    rw [←is_open_compl_iff, is_open_iff_of_mem (mem_compl h), ←preimage_compl, compl_compl]

@[simp]
theorem is_open_image_coe {s : Set X} : IsOpen (coeₓ '' s : Set (Alexandroff X)) ↔ IsOpen s :=
  by 
    rw [is_open_iff_of_not_mem infty_not_mem_image_coe, preimage_image_eq _ coe_injective]

theorem is_open_compl_image_coe {s : Set X} : IsOpen ((coeₓ '' s : Set (Alexandroff X))ᶜ) ↔ IsClosed s ∧ IsCompact s :=
  by 
    rw [is_open_iff_of_mem, ←preimage_compl, compl_compl, preimage_image_eq _ coe_injective]
    exact infty_not_mem_image_coe

@[simp]
theorem is_closed_image_coe {s : Set X} : IsClosed (coeₓ '' s : Set (Alexandroff X)) ↔ IsClosed s ∧ IsCompact s :=
  by 
    rw [←is_open_compl_iff, is_open_compl_image_coe]

/-- An open set in `alexandroff X` constructed from a closed compact set in `X` -/
def opens_of_compl (s : Set X) (h₁ : IsClosed s) (h₂ : IsCompact s) : TopologicalSpace.Opens (Alexandroff X) :=
  ⟨(coeₓ '' s)ᶜ, is_open_compl_image_coe.2 ⟨h₁, h₂⟩⟩

theorem infty_mem_opens_of_compl {s : Set X} (h₁ : IsClosed s) (h₂ : IsCompact s) : ∞ ∈ opens_of_compl s h₁ h₂ :=
  mem_compl infty_not_mem_image_coe

@[continuity]
theorem continuous_coe : Continuous (coeₓ : X → Alexandroff X) :=
  continuous_def.mpr fun s hs => hs.right

theorem is_open_map_coe : IsOpenMap (coeₓ : X → Alexandroff X) :=
  fun s => is_open_image_coe.2

theorem open_embedding_coe : OpenEmbedding (coeₓ : X → Alexandroff X) :=
  open_embedding_of_continuous_injective_open continuous_coe coe_injective is_open_map_coe

theorem is_open_range_coe : IsOpen (range (coeₓ : X → Alexandroff X)) :=
  open_embedding_coe.open_range

theorem is_closed_infty : IsClosed ({∞} : Set (Alexandroff X)) :=
  by 
    rw [←compl_range_coe, is_closed_compl_iff]
    exact is_open_range_coe

theorem nhds_coe_eq (x : X) : 𝓝 (↑x) = map (coeₓ : X → Alexandroff X) (𝓝 x) :=
  (open_embedding_coe.map_nhds_eq x).symm

theorem nhds_within_coe_image (s : Set X) (x : X) : 𝓝[coeₓ '' s] (x : Alexandroff X) = map coeₓ (𝓝[s] x) :=
  (open_embedding_coe.toEmbedding.map_nhds_within_eq _ _).symm

theorem nhds_within_coe (s : Set (Alexandroff X)) (x : X) : 𝓝[s] ↑x = map coeₓ (𝓝[coeₓ ⁻¹' s] x) :=
  (open_embedding_coe.map_nhds_within_preimage_eq _ _).symm

theorem comap_coe_nhds (x : X) : comap (coeₓ : X → Alexandroff X) (𝓝 x) = 𝓝 x :=
  (open_embedding_coe.to_inducing.nhds_eq_comap x).symm

/-- If `x` is not an isolated point of `X`, then `x : alexandroff X` is not an isolated point
of `alexandroff X`. -/
instance nhds_within_compl_coe_ne_bot (x : X) [h : ne_bot (𝓝[{x}ᶜ] x)] : ne_bot (𝓝[{x}ᶜ] (x : Alexandroff X)) :=
  by 
    simpa [nhds_within_coe, preimage, coe_eq_coe] using h.map coeₓ

theorem nhds_within_compl_infty_eq : 𝓝[{∞}ᶜ] (∞ : Alexandroff X) = map coeₓ (coclosed_compact X) :=
  by 
    refine' (nhds_within_basis_open ∞ _).ext (has_basis_coclosed_compact.map _) _ _
    ·
      rintro s ⟨hs, hso⟩
      refine' ⟨_, (is_open_iff_of_mem hs).mp hso, _⟩
      simp 
    ·
      rintro s ⟨h₁, h₂⟩
      refine' ⟨_, ⟨mem_compl infty_not_mem_image_coe, is_open_compl_image_coe.2 ⟨h₁, h₂⟩⟩, _⟩
      simp [compl_image_coe, ←diff_eq, subset_preimage_image]

/-- If `X` is a non-compact space, then `∞` is not an isolated point of `alexandroff X`. -/
instance nhds_within_compl_infty_ne_bot [NoncompactSpace X] : ne_bot (𝓝[{∞}ᶜ] (∞ : Alexandroff X)) :=
  by 
    rw [nhds_within_compl_infty_eq]
    infer_instance

instance (priority := 900) nhds_within_compl_ne_bot [∀ x : X, ne_bot (𝓝[{x}ᶜ] x)] [NoncompactSpace X]
  (x : Alexandroff X) : ne_bot (𝓝[{x}ᶜ] x) :=
  Alexandroff.rec _ Alexandroff.nhds_within_compl_infty_ne_bot (fun y => Alexandroff.nhds_within_compl_coe_ne_bot y) x

theorem nhds_infty_eq : 𝓝 (∞ : Alexandroff X) = map coeₓ (coclosed_compact X)⊔pure ∞ :=
  by 
    rw [←nhds_within_compl_infty_eq, nhds_within_compl_singleton_sup_pure]

theorem has_basis_nhds_infty :
  (𝓝 (∞ : Alexandroff X)).HasBasis (fun s : Set X => IsClosed s ∧ IsCompact s) fun s => coeₓ '' sᶜ ∪ {∞} :=
  by 
    rw [nhds_infty_eq]
    exact (has_basis_coclosed_compact.map _).sup_pure _

@[simp]
theorem comap_coe_nhds_infty : comap (coeₓ : X → Alexandroff X) (𝓝 ∞) = coclosed_compact X :=
  by 
    simp [nhds_infty_eq, comap_sup, comap_map coe_injective]

theorem le_nhds_infty {f : Filter (Alexandroff X)} :
  f ≤ 𝓝 ∞ ↔ ∀ s : Set X, IsClosed s → IsCompact s → coeₓ '' sᶜ ∪ {∞} ∈ f :=
  by 
    simp only [has_basis_nhds_infty.ge_iff, and_imp]

theorem ultrafilter_le_nhds_infty {f : Ultrafilter (Alexandroff X)} :
  (f : Filter (Alexandroff X)) ≤ 𝓝 ∞ ↔ ∀ s : Set X, IsClosed s → IsCompact s → coeₓ '' s ∉ f :=
  by 
    simp only [le_nhds_infty, ←compl_image_coe, Ultrafilter.mem_coe, Ultrafilter.compl_mem_iff_not_mem]

theorem tendsto_nhds_infty' {α : Type _} {f : Alexandroff X → α} {l : Filter α} :
  tendsto f (𝓝 ∞) l ↔ tendsto f (pure ∞) l ∧ tendsto (f ∘ coeₓ) (coclosed_compact X) l :=
  by 
    simp [nhds_infty_eq, and_comm]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (s «expr ∈ » l)
theorem tendsto_nhds_infty {α : Type _} {f : Alexandroff X → α} {l : Filter α} :
  tendsto f (𝓝 ∞) l ↔ ∀ s _ : s ∈ l, f ∞ ∈ s ∧ ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ maps_to (f ∘ coeₓ) (tᶜ) s :=
  tendsto_nhds_infty'.trans$
    by 
      simp only [tendsto_pure_left, has_basis_coclosed_compact.tendsto_left_iff, forall_and_distrib, and_assoc,
        exists_prop]

theorem continuous_at_infty' {Y : Type _} [TopologicalSpace Y] {f : Alexandroff X → Y} :
  ContinuousAt f ∞ ↔ tendsto (f ∘ coeₓ) (coclosed_compact X) (𝓝 (f ∞)) :=
  tendsto_nhds_infty'.trans$ and_iff_right (tendsto_pure_nhds _ _)

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (s «expr ∈ » expr𝓝() (f «expr∞»()))
theorem continuous_at_infty {Y : Type _} [TopologicalSpace Y] {f : Alexandroff X → Y} :
  ContinuousAt f ∞ ↔ ∀ s _ : s ∈ 𝓝 (f ∞), ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ maps_to (f ∘ coeₓ) (tᶜ) s :=
  continuous_at_infty'.trans$
    by 
      simp only [has_basis_coclosed_compact.tendsto_left_iff, exists_prop, and_assoc]

theorem continuous_at_coe {Y : Type _} [TopologicalSpace Y] {f : Alexandroff X → Y} {x : X} :
  ContinuousAt f x ↔ ContinuousAt (f ∘ coeₓ) x :=
  by 
    rw [ContinuousAt, nhds_coe_eq, tendsto_map'_iff, ContinuousAt]

/-- If `X` is not a compact space, then the natural embedding `X → alexandroff X` has dense range.
-/
theorem dense_range_coe [NoncompactSpace X] : DenseRange (coeₓ : X → Alexandroff X) :=
  by 
    rw [DenseRange, ←compl_infty]
    exact dense_compl_singleton _

theorem dense_embedding_coe [NoncompactSpace X] : DenseEmbedding (coeₓ : X → Alexandroff X) :=
  { open_embedding_coe with dense := dense_range_coe }

/-!
### Compactness and separation properties

In this section we prove that `alexandroff X` is a compact space; it is a T₀ (resp., T₁) space if
the original space satisfies the same separation axiom. If the original space is a locally compact
Hausdorff space, then `alexandroff X` is a normal (hence, regular and Hausdorff) space.

Finally, if the original space `X` is *not* compact and is a preconnected space, then
`alexandroff X` is a connected space.
-/


/-- For any topological space `X`, its one point compactification is a compact space. -/
instance : CompactSpace (Alexandroff X) :=
  { compact_univ :=
      by 
        refine' is_compact_iff_ultrafilter_le_nhds.2 fun f hf => _ 
        clear hf 
        byCases' hf : (f : Filter (Alexandroff X)) ≤ 𝓝 ∞
        ·
          exact ⟨∞, mem_univ _, hf⟩
        ·
          simp only [ultrafilter_le_nhds_infty, not_forall, not_not] at hf 
          rcases hf with ⟨s, h₁, h₂, hsf⟩
          have hf : range (coeₓ : X → Alexandroff X) ∈ f 
          exact mem_of_superset hsf (image_subset_range _ _)
          have hsf' : s ∈ f.comap coe_injective hf 
          exact (f.mem_comap _ _).2 hsf 
          rcases h₂.ultrafilter_le_nhds _ (le_principal_iff.2 hsf') with ⟨a, has, hle⟩
          rw [Ultrafilter.coe_comap, ←comap_coe_nhds, comap_le_comap_iff hf] at hle 
          exact ⟨a, mem_univ _, hle⟩ }

/-- The one point compactification of a `t0_space` space is a `t0_space`. -/
instance [T0Space X] : T0Space (Alexandroff X) :=
  by 
    refine' ⟨fun x y hxy => _⟩
    induction x using Alexandroff.rec <;> induction y using Alexandroff.rec
    ·
      exact (hxy rfl).elim
    ·
      use {∞}ᶜ
      simp [is_closed_infty]
    ·
      use {∞}ᶜ
      simp [is_closed_infty]
    ·
      rcases T0Space.t0 x y (mt coe_eq_coe.mpr hxy) with ⟨U, hUo, hU⟩
      refine' ⟨coeₓ '' U, is_open_image_coe.2 hUo, _⟩
      simpa [coe_eq_coe]

/-- The one point compactification of a `t1_space` space is a `t1_space`. -/
instance [T1Space X] : T1Space (Alexandroff X) :=
  { t1 :=
      fun z =>
        by 
          induction z using Alexandroff.rec
          ·
            exact is_closed_infty
          ·
            simp only [←image_singleton, is_closed_image_coe]
            exact ⟨is_closed_singleton, is_compact_singleton⟩ }

/-- The one point compactification of a locally compact Hausdorff space is a normal (hence,
Hausdorff and regular) topological space. -/
instance [LocallyCompactSpace X] [T2Space X] : NormalSpace (Alexandroff X) :=
  by 
    have key : ∀ z : X, ∃ u v : Set (Alexandroff X), IsOpen u ∧ IsOpen v ∧ ↑z ∈ u ∧ ∞ ∈ v ∧ u ∩ v = ∅
    ·
      intro z 
      rcases exists_open_with_compact_closure z with ⟨u, hu, huy', Hu⟩
      refine'
        ⟨coeₓ '' u, (coeₓ '' Closure u)ᶜ, is_open_image_coe.2 hu, is_open_compl_image_coe.2 ⟨is_closed_closure, Hu⟩,
          mem_image_of_mem _ huy', mem_compl infty_not_mem_image_coe, _⟩
      rw [←subset_compl_iff_disjoint, compl_compl]
      exact image_subset _ subset_closure 
    refine' @normal_of_compact_t2 _ _ _ ⟨fun x y hxy => _⟩
    induction x using Alexandroff.rec <;> induction y using Alexandroff.rec
    ·
      exact (hxy rfl).elim
    ·
      rcases key y with ⟨u, v, hu, hv, hxu, hyv, huv⟩
      exact ⟨v, u, hv, hu, hyv, hxu, inter_comm u v ▸ huv⟩
    ·
      exact key x
    ·
      exact separated_by_open_embedding open_embedding_coe (mt coe_eq_coe.mpr hxy)

/-- If `X` is not a compact space, then `alexandroff X` is a connected space. -/
instance [PreconnectedSpace X] [NoncompactSpace X] : ConnectedSpace (Alexandroff X) :=
  { to_preconnected_space := dense_embedding_coe.to_dense_inducing.PreconnectedSpace, to_nonempty := inferInstance }

end Alexandroff

