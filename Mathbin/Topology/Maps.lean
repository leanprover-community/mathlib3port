import Mathbin.Topology.Order

/-!
# Specific classes of maps between topological spaces

This file introduces the following properties of a map `f : X → Y` between topological spaces:

* `is_open_map f` means the image of an open set under `f` is open.
* `is_closed_map f` means the image of a closed set under `f` is closed.

(Open and closed maps need not be continuous.)

* `inducing f` means the topology on `X` is the one induced via `f` from the topology on `Y`.
  These behave like embeddings except they need not be injective. Instead, points of `X` which
  are identified by `f` are also indistinguishable in the topology on `X`.
* `embedding f` means `f` is inducing and also injective. Equivalently, `f` identifies `X` with
  a subspace of `Y`.
* `open_embedding f` means `f` is an embedding with open image, so it identifies `X` with an
  open subspace of `Y`. Equivalently, `f` is an embedding and an open map.
* `closed_embedding f` similarly means `f` is an embedding with closed image, so it identifies
  `X` with a closed subspace of `Y`. Equivalently, `f` is an embedding and a closed map.

* `quotient_map f` is the dual condition to `embedding f`: `f` is surjective and the topology
  on `Y` is the one coinduced via `f` from the topology on `X`. Equivalently, `f` identifies
  `Y` with a quotient of `X`. Quotient maps are also sometimes known as identification maps.

## References

* <https://en.wikipedia.org/wiki/Open_and_closed_maps>
* <https://en.wikipedia.org/wiki/Embedding#General_topology>
* <https://en.wikipedia.org/wiki/Quotient_space_(topology)#Quotient_map>

## Tags

open map, closed map, embedding, quotient map, identification map

-/


open Set Filter

open_locale TopologicalSpace Filter

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

section Inducing

/-- A function `f : α → β` between topological spaces is inducing if the topology on `α` is induced
by the topology on `β` through `f`, meaning that a set `s : set α` is open iff it is the preimage
under `f` of some open set `t : set β`. -/
structure Inducing [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : α → β) : Prop where 
  induced : tα = tβ.induced f

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

theorem inducing_id : Inducing (@id α) :=
  ⟨induced_id.symm⟩

protected theorem Inducing.comp {g : β → γ} {f : α → β} (hg : Inducing g) (hf : Inducing f) : Inducing (g ∘ f) :=
  ⟨by 
      rw [hf.induced, hg.induced, induced_compose]⟩

theorem inducing_of_inducing_compose {f : α → β} {g : β → γ} (hf : Continuous f) (hg : Continuous g)
  (hgf : Inducing (g ∘ f)) : Inducing f :=
  ⟨le_antisymmₓ
      (by 
        rwa [←continuous_iff_le_induced])
      (by 
        rw [hgf.induced, ←continuous_iff_le_induced]
        apply hg.comp continuous_induced_dom)⟩

theorem Inducing.nhds_eq_comap {f : α → β} (hf : Inducing f) : ∀ a : α, 𝓝 a = comap f (𝓝$ f a) :=
  (induced_iff_nhds_eq f).1 hf.induced

theorem Inducing.map_nhds_eq {f : α → β} (hf : Inducing f) (a : α) : (𝓝 a).map f = 𝓝[range f] f a :=
  hf.induced.symm ▸ map_nhds_induced_eq a

theorem Inducing.map_nhds_of_mem {f : α → β} (hf : Inducing f) (a : α) (h : range f ∈ 𝓝 (f a)) :
  (𝓝 a).map f = 𝓝 (f a) :=
  hf.induced.symm ▸ map_nhds_induced_of_mem h

theorem Inducing.tendsto_nhds_iff {ι : Type _} {f : ι → β} {g : β → γ} {a : Filter ι} {b : β} (hg : Inducing g) :
  tendsto f a (𝓝 b) ↔ tendsto (g ∘ f) a (𝓝 (g b)) :=
  by 
    rw [tendsto, tendsto, hg.induced, nhds_induced, ←map_le_iff_le_comap, Filter.map_map]

theorem Inducing.continuous_at_iff {f : α → β} {g : β → γ} (hg : Inducing g) {x : α} :
  ContinuousAt f x ↔ ContinuousAt (g ∘ f) x :=
  by 
    simpRw [ContinuousAt, Inducing.tendsto_nhds_iff hg]

theorem Inducing.continuous_iff {f : α → β} {g : β → γ} (hg : Inducing g) : Continuous f ↔ Continuous (g ∘ f) :=
  by 
    simpRw [continuous_iff_continuous_at, hg.continuous_at_iff]

theorem Inducing.continuous_at_iff' {f : α → β} {g : β → γ} (hf : Inducing f) {x : α} (h : range f ∈ 𝓝 (f x)) :
  ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) :=
  by 
    simpRw [ContinuousAt, Filter.Tendsto, ←hf.map_nhds_of_mem _ h, Filter.map_map]

theorem Inducing.continuous {f : α → β} (hf : Inducing f) : Continuous f :=
  hf.continuous_iff.mp continuous_id

theorem Inducing.closure_eq_preimage_closure_image {f : α → β} (hf : Inducing f) (s : Set α) :
  Closure s = f ⁻¹' Closure (f '' s) :=
  by 
    ext x 
    rw [Set.mem_preimage, ←closure_induced, hf.induced]

theorem Inducing.is_closed_iff {f : α → β} (hf : Inducing f) {s : Set α} : IsClosed s ↔ ∃ t, IsClosed t ∧ f ⁻¹' t = s :=
  by 
    rw [hf.induced, is_closed_induced_iff]

theorem Inducing.is_open_iff {f : α → β} (hf : Inducing f) {s : Set α} : IsOpen s ↔ ∃ t, IsOpen t ∧ f ⁻¹' t = s :=
  by 
    rw [hf.induced, is_open_induced_iff]

end Inducing

section Embedding

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : set α`, `s` is open iff it is the preimage of an open set. -/
structure Embedding [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : α → β) extends Inducing f : Prop where 
  inj : Function.Injective f

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

theorem Embedding.mk' (f : α → β) (inj : Function.Injective f) (induced : ∀ a, comap f (𝓝 (f a)) = 𝓝 a) : Embedding f :=
  ⟨⟨(induced_iff_nhds_eq f).2 fun a => (induced a).symm⟩, inj⟩

theorem embedding_id : Embedding (@id α) :=
  ⟨inducing_id, fun a₁ a₂ h => h⟩

theorem Embedding.comp {g : β → γ} {f : α → β} (hg : Embedding g) (hf : Embedding f) : Embedding (g ∘ f) :=
  { hg.to_inducing.comp hf.to_inducing with inj := fun a₁ a₂ h => hf.inj$ hg.inj h }

theorem embedding_of_embedding_compose {f : α → β} {g : β → γ} (hf : Continuous f) (hg : Continuous g)
  (hgf : Embedding (g ∘ f)) : Embedding f :=
  { induced := (inducing_of_inducing_compose hf hg hgf.to_inducing).induced,
    inj :=
      fun a₁ a₂ h =>
        hgf.inj$
          by 
            simp [h, · ∘ ·] }

protected theorem Function.LeftInverse.embedding {f : α → β} {g : β → α} (h : Function.LeftInverse f g)
  (hf : Continuous f) (hg : Continuous g) : Embedding g :=
  embedding_of_embedding_compose hg hf$ h.comp_eq_id.symm ▸ embedding_id

theorem Embedding.map_nhds_eq {f : α → β} (hf : Embedding f) (a : α) : (𝓝 a).map f = 𝓝[range f] f a :=
  hf.1.map_nhds_eq a

theorem Embedding.map_nhds_of_mem {f : α → β} (hf : Embedding f) (a : α) (h : range f ∈ 𝓝 (f a)) :
  (𝓝 a).map f = 𝓝 (f a) :=
  hf.1.map_nhds_of_mem a h

theorem Embedding.tendsto_nhds_iff {ι : Type _} {f : ι → β} {g : β → γ} {a : Filter ι} {b : β} (hg : Embedding g) :
  tendsto f a (𝓝 b) ↔ tendsto (g ∘ f) a (𝓝 (g b)) :=
  hg.to_inducing.tendsto_nhds_iff

theorem Embedding.continuous_iff {f : α → β} {g : β → γ} (hg : Embedding g) : Continuous f ↔ Continuous (g ∘ f) :=
  Inducing.continuous_iff hg.1

theorem Embedding.continuous {f : α → β} (hf : Embedding f) : Continuous f :=
  Inducing.continuous hf.1

theorem Embedding.closure_eq_preimage_closure_image {e : α → β} (he : Embedding e) (s : Set α) :
  Closure s = e ⁻¹' Closure (e '' s) :=
  he.1.closure_eq_preimage_closure_image s

end Embedding

/-- A function between topological spaces is a quotient map if it is surjective,
  and for all `s : set β`, `s` is open iff its preimage is an open set. -/
def QuotientMap {α : Type _} {β : Type _} [tα : TopologicalSpace α] [tβ : TopologicalSpace β] (f : α → β) : Prop :=
  Function.Surjective f ∧ tβ = tα.coinduced f

theorem quotient_map_iff {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
  QuotientMap f ↔ Function.Surjective f ∧ ∀ s : Set β, IsOpen s ↔ IsOpen (f ⁻¹' s) :=
  and_congr Iff.rfl topological_space_eq_iff

namespace QuotientMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

protected theorem id : QuotientMap (@id α) :=
  ⟨fun a => ⟨a, rfl⟩, coinduced_id.symm⟩

protected theorem comp {g : β → γ} {f : α → β} (hg : QuotientMap g) (hf : QuotientMap f) : QuotientMap (g ∘ f) :=
  ⟨hg.left.comp hf.left,
    by 
      rw [hg.right, hf.right, coinduced_compose]⟩

protected theorem of_quotient_map_compose {f : α → β} {g : β → γ} (hf : Continuous f) (hg : Continuous g)
  (hgf : QuotientMap (g ∘ f)) : QuotientMap g :=
  ⟨fun b =>
      let ⟨a, h⟩ := hgf.left b
      ⟨f a, h⟩,
    le_antisymmₓ
      (by 
        rw [hgf.right, ←continuous_iff_coinduced_le] <;> apply continuous_coinduced_rng.comp hf)
      (by 
        rwa [←continuous_iff_coinduced_le])⟩

protected theorem continuous_iff {f : α → β} {g : β → γ} (hf : QuotientMap f) : Continuous g ↔ Continuous (g ∘ f) :=
  by 
    rw [continuous_iff_coinduced_le, continuous_iff_coinduced_le, hf.right, coinduced_compose]

protected theorem Continuous {f : α → β} (hf : QuotientMap f) : Continuous f :=
  hf.continuous_iff.mp continuous_id

protected theorem surjective {f : α → β} (hf : QuotientMap f) : Function.Surjective f :=
  hf.1

protected theorem is_open_preimage {f : α → β} (hf : QuotientMap f) {s : Set β} : IsOpen (f ⁻¹' s) ↔ IsOpen s :=
  ((quotient_map_iff.1 hf).2 s).symm

end QuotientMap

/-- A map `f : α → β` is said to be an *open map*, if the image of any open `U : set α`
is open in `β`. -/
def IsOpenMap [TopologicalSpace α] [TopologicalSpace β] (f : α → β) :=
  ∀ U : Set α, IsOpen U → IsOpen (f '' U)

namespace IsOpenMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {f : α → β}

open Function

protected theorem id : IsOpenMap (@id α) :=
  fun s hs =>
    by 
      rwa [image_id]

protected theorem comp {g : β → γ} {f : α → β} (hg : IsOpenMap g) (hf : IsOpenMap f) : IsOpenMap (g ∘ f) :=
  by 
    intro s hs <;> rw [image_comp] <;> exact hg _ (hf _ hs)

theorem is_open_range (hf : IsOpenMap f) : IsOpen (range f) :=
  by 
    rw [←image_univ]
    exact hf _ is_open_univ

theorem image_mem_nhds (hf : IsOpenMap f) {x : α} {s : Set α} (hx : s ∈ 𝓝 x) : f '' s ∈ 𝓝 (f x) :=
  let ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.1 hx 
  mem_of_superset (IsOpen.mem_nhds (hf t ht) (mem_image_of_mem _ hxt)) (image_subset _ hts)

theorem image_interior_subset (hf : IsOpenMap f) (s : Set α) : f '' Interior s ⊆ Interior (f '' s) :=
  interior_maximal (image_subset _ interior_subset) (hf _ is_open_interior)

theorem nhds_le (hf : IsOpenMap f) (a : α) : 𝓝 (f a) ≤ (𝓝 a).map f :=
  le_map$ fun s => hf.image_mem_nhds

theorem of_nhds_le (hf : ∀ a, 𝓝 (f a) ≤ map f (𝓝 a)) : IsOpenMap f :=
  fun s hs => is_open_iff_mem_nhds.2$ fun b ⟨a, has, hab⟩ => hab ▸ hf _ (image_mem_map$ IsOpen.mem_nhds hs has)

theorem of_inverse {f : α → β} {f' : β → α} (h : Continuous f') (l_inv : left_inverse f f')
  (r_inv : RightInverse f f') : IsOpenMap f :=
  by 
    intro s hs 
    rw [image_eq_preimage_of_inverse r_inv l_inv]
    exact hs.preimage h

theorem to_quotient_map {f : α → β} (open_map : IsOpenMap f) (cont : Continuous f) (surj : Function.Surjective f) :
  QuotientMap f :=
  ⟨surj,
    by 
      ext s 
      show IsOpen s ↔ IsOpen (f ⁻¹' s)
      split 
      ·
        exact continuous_def.1 cont s
      ·
        intro h 
        rw [←surj.image_preimage s]
        exact open_map _ h⟩

theorem interior_preimage_subset_preimage_interior {s : Set β} (hf : IsOpenMap f) :
  Interior (f ⁻¹' s) ⊆ f ⁻¹' Interior s :=
  by 
    rw [←Set.image_subset_iff]
    refine' interior_maximal _ (hf _ is_open_interior)
    rw [Set.image_subset_iff]
    exact interior_subset

theorem preimage_interior_eq_interior_preimage {s : Set β} (hf₁ : Continuous f) (hf₂ : IsOpenMap f) :
  f ⁻¹' Interior s = Interior (f ⁻¹' s) :=
  subset.antisymm (preimage_interior_subset_interior_preimage hf₁) (interior_preimage_subset_preimage_interior hf₂)

end IsOpenMap

theorem is_open_map_iff_nhds_le [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
  IsOpenMap f ↔ ∀ a : α, 𝓝 (f a) ≤ (𝓝 a).map f :=
  ⟨fun hf => hf.nhds_le, IsOpenMap.of_nhds_le⟩

theorem is_open_map_iff_interior [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
  IsOpenMap f ↔ ∀ s, f '' Interior s ⊆ Interior (f '' s) :=
  ⟨IsOpenMap.image_interior_subset,
    fun hs u hu =>
      subset_interior_iff_open.mp$
        calc f '' u = f '' Interior u :=
          by 
            rw [hu.interior_eq]
          _ ⊆ Interior (f '' u) := hs u
          ⟩

theorem Inducing.is_open_map [TopologicalSpace α] [TopologicalSpace β] {f : α → β} (hi : Inducing f)
  (ho : IsOpen (range f)) : IsOpenMap f :=
  IsOpenMap.of_nhds_le$ fun x => (hi.map_nhds_of_mem _$ IsOpen.mem_nhds ho$ mem_range_self _).Ge

section IsClosedMap

variable [TopologicalSpace α] [TopologicalSpace β]

/-- A map `f : α → β` is said to be a *closed map*, if the image of any closed `U : set α`
is closed in `β`. -/
def IsClosedMap (f : α → β) :=
  ∀ U : Set α, IsClosed U → IsClosed (f '' U)

end IsClosedMap

namespace IsClosedMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

open Function

protected theorem id : IsClosedMap (@id α) :=
  fun s hs =>
    by 
      rwa [image_id]

protected theorem comp {g : β → γ} {f : α → β} (hg : IsClosedMap g) (hf : IsClosedMap f) : IsClosedMap (g ∘ f) :=
  by 
    intro s hs 
    rw [image_comp]
    exact hg _ (hf _ hs)

theorem closure_image_subset {f : α → β} (hf : IsClosedMap f) (s : Set α) : Closure (f '' s) ⊆ f '' Closure s :=
  closure_minimal (image_subset _ subset_closure) (hf _ is_closed_closure)

theorem of_inverse {f : α → β} {f' : β → α} (h : Continuous f') (l_inv : left_inverse f f')
  (r_inv : RightInverse f f') : IsClosedMap f :=
  fun s hs =>
    have  : f' ⁻¹' s = f '' s :=
      by 
        ext x <;> simp [mem_image_iff_of_inverse r_inv l_inv]
    this ▸ hs.preimage h

theorem of_nonempty {f : α → β} (h : ∀ s, IsClosed s → s.nonempty → IsClosed (f '' s)) : IsClosedMap f :=
  by 
    intro s hs 
    cases' eq_empty_or_nonempty s with h2s h2s
    ·
      simpRw [h2s, image_empty, is_closed_empty]
    ·
      exact h s hs h2s

theorem closed_range {f : α → β} (hf : IsClosedMap f) : IsClosed (range f) :=
  @image_univ _ _ f ▸ hf _ is_closed_univ

end IsClosedMap

theorem Inducing.is_closed_map [TopologicalSpace α] [TopologicalSpace β] {f : α → β} (hf : Inducing f)
  (h : IsClosed (range f)) : IsClosedMap f :=
  by 
    intro s hs 
    rcases hf.is_closed_iff.1 hs with ⟨t, ht, rfl⟩
    rw [image_preimage_eq_inter_range]
    exact IsClosed.inter ht h

theorem is_closed_map_iff_closure_image [TopologicalSpace α] [TopologicalSpace β] {f : α → β} :
  IsClosedMap f ↔ ∀ s, Closure (f '' s) ⊆ f '' Closure s :=
  ⟨IsClosedMap.closure_image_subset,
    fun hs c hc =>
      is_closed_of_closure_subset$
        calc Closure (f '' c) ⊆ f '' Closure c := hs c 
          _ = f '' c :=
          by 
            rw [hc.closure_eq]
          ⟩

section OpenEmbedding

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- An open embedding is an embedding with open image. -/
structure OpenEmbedding (f : α → β) extends Embedding f : Prop where 
  open_range : IsOpen$ range f

theorem OpenEmbedding.is_open_map {f : α → β} (hf : OpenEmbedding f) : IsOpenMap f :=
  hf.to_embedding.to_inducing.is_open_map hf.open_range

theorem OpenEmbedding.map_nhds_eq {f : α → β} (hf : OpenEmbedding f) (a : α) : map f (𝓝 a) = 𝓝 (f a) :=
  hf.to_embedding.map_nhds_of_mem _$ IsOpen.mem_nhds hf.open_range$ mem_range_self _

theorem OpenEmbedding.open_iff_image_open {f : α → β} (hf : OpenEmbedding f) {s : Set α} : IsOpen s ↔ IsOpen (f '' s) :=
  ⟨hf.is_open_map s,
    fun h =>
      by 
        convert ← h.preimage hf.to_embedding.continuous 
        apply preimage_image_eq _ hf.inj⟩

theorem OpenEmbedding.tendsto_nhds_iff {ι : Type _} {f : ι → β} {g : β → γ} {a : Filter ι} {b : β}
  (hg : OpenEmbedding g) : tendsto f a (𝓝 b) ↔ tendsto (g ∘ f) a (𝓝 (g b)) :=
  hg.to_embedding.tendsto_nhds_iff

theorem OpenEmbedding.continuous {f : α → β} (hf : OpenEmbedding f) : Continuous f :=
  hf.to_embedding.continuous

theorem OpenEmbedding.open_iff_preimage_open {f : α → β} (hf : OpenEmbedding f) {s : Set β} (hs : s ⊆ range f) :
  IsOpen s ↔ IsOpen (f ⁻¹' s) :=
  by 
    convert ← hf.open_iff_image_open.symm 
    rwa [image_preimage_eq_inter_range, inter_eq_self_of_subset_left]

theorem open_embedding_of_embedding_open {f : α → β} (h₁ : Embedding f) (h₂ : IsOpenMap f) : OpenEmbedding f :=
  ⟨h₁, h₂.is_open_range⟩

theorem open_embedding_of_continuous_injective_open {f : α → β} (h₁ : Continuous f) (h₂ : Function.Injective f)
  (h₃ : IsOpenMap f) : OpenEmbedding f :=
  by 
    refine' open_embedding_of_embedding_open ⟨⟨_⟩, h₂⟩ h₃ 
    apply le_antisymmₓ (continuous_iff_le_induced.mp h₁) _ 
    intro s 
    change IsOpen _ → IsOpen _ 
    rw [is_open_induced_iff]
    refine' fun hs => ⟨f '' s, h₃ s hs, _⟩
    rw [preimage_image_eq _ h₂]

theorem open_embedding_id : OpenEmbedding (@id α) :=
  ⟨embedding_id,
    by 
      convert is_open_univ <;> apply range_id⟩

theorem OpenEmbedding.comp {g : β → γ} {f : α → β} (hg : OpenEmbedding g) (hf : OpenEmbedding f) :
  OpenEmbedding (g ∘ f) :=
  ⟨hg.1.comp hf.1,
    show IsOpen (range (g ∘ f))by 
      rw [range_comp, ←hg.open_iff_image_open] <;> exact hf.2⟩

end OpenEmbedding

section ClosedEmbedding

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- A closed embedding is an embedding with closed image. -/
structure ClosedEmbedding (f : α → β) extends Embedding f : Prop where 
  closed_range : IsClosed$ range f

variable {f : α → β}

theorem ClosedEmbedding.tendsto_nhds_iff {ι : Type _} {g : ι → α} {a : Filter ι} {b : α} (hf : ClosedEmbedding f) :
  tendsto g a (𝓝 b) ↔ tendsto (f ∘ g) a (𝓝 (f b)) :=
  hf.to_embedding.tendsto_nhds_iff

theorem ClosedEmbedding.continuous (hf : ClosedEmbedding f) : Continuous f :=
  hf.to_embedding.continuous

theorem ClosedEmbedding.is_closed_map (hf : ClosedEmbedding f) : IsClosedMap f :=
  hf.to_embedding.to_inducing.is_closed_map hf.closed_range

theorem ClosedEmbedding.closed_iff_image_closed (hf : ClosedEmbedding f) {s : Set α} : IsClosed s ↔ IsClosed (f '' s) :=
  ⟨hf.is_closed_map s,
    fun h =>
      by 
        convert ← continuous_iff_is_closed.mp hf.continuous _ h 
        apply preimage_image_eq _ hf.inj⟩

theorem ClosedEmbedding.closed_iff_preimage_closed (hf : ClosedEmbedding f) {s : Set β} (hs : s ⊆ range f) :
  IsClosed s ↔ IsClosed (f ⁻¹' s) :=
  by 
    convert ← hf.closed_iff_image_closed.symm 
    rwa [image_preimage_eq_inter_range, inter_eq_self_of_subset_left]

theorem closed_embedding_of_embedding_closed (h₁ : Embedding f) (h₂ : IsClosedMap f) : ClosedEmbedding f :=
  ⟨h₁,
    by 
      convert h₂ univ is_closed_univ <;> simp ⟩

theorem closed_embedding_of_continuous_injective_closed (h₁ : Continuous f) (h₂ : Function.Injective f)
  (h₃ : IsClosedMap f) : ClosedEmbedding f :=
  by 
    refine' closed_embedding_of_embedding_closed ⟨⟨_⟩, h₂⟩ h₃ 
    apply le_antisymmₓ (continuous_iff_le_induced.mp h₁) _ 
    intro s' 
    change IsOpen _ ≤ IsOpen _ 
    rw [←is_closed_compl_iff, ←is_closed_compl_iff]
    generalize «expr ᶜ» s' = s 
    rw [is_closed_induced_iff]
    refine' fun hs => ⟨f '' s, h₃ s hs, _⟩
    rw [preimage_image_eq _ h₂]

theorem closed_embedding_id : ClosedEmbedding (@id α) :=
  ⟨embedding_id,
    by 
      convert is_closed_univ <;> apply range_id⟩

theorem ClosedEmbedding.comp {g : β → γ} {f : α → β} (hg : ClosedEmbedding g) (hf : ClosedEmbedding f) :
  ClosedEmbedding (g ∘ f) :=
  ⟨hg.to_embedding.comp hf.to_embedding,
    show IsClosed (range (g ∘ f))by 
      rw [range_comp, ←hg.closed_iff_image_closed] <;> exact hf.closed_range⟩

end ClosedEmbedding

