import Mathbin.Topology.Maps 
import Mathbin.Data.Fin.Tuple

/-!
# Constructions of new topological spaces from old ones

This file constructs products, sums, subtypes and quotients of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, sum, disjoint union, subspace, quotient space

-/


noncomputable theory

open TopologicalSpace Set Filter

open_locale Classical TopologicalSpace Filter

universe u v w x

variable{α : Type u}{β : Type v}{γ : Type w}{δ : Type x}

section Constructions

instance  {p : α → Prop} [t : TopologicalSpace α] : TopologicalSpace (Subtype p) :=
  induced coeₓ t

instance  {r : α → α → Prop} [t : TopologicalSpace α] : TopologicalSpace (Quot r) :=
  coinduced (Quot.mk r) t

instance  {s : Setoidₓ α} [t : TopologicalSpace α] : TopologicalSpace (Quotientₓ s) :=
  coinduced Quotientₓ.mk t

instance  [t₁ : TopologicalSpace α] [t₂ : TopologicalSpace β] : TopologicalSpace (α × β) :=
  induced Prod.fst t₁⊓induced Prod.snd t₂

instance  [t₁ : TopologicalSpace α] [t₂ : TopologicalSpace β] : TopologicalSpace (Sum α β) :=
  coinduced Sum.inl t₁⊔coinduced Sum.inr t₂

instance  {β : α → Type v} [t₂ : ∀ a, TopologicalSpace (β a)] : TopologicalSpace (Sigma β) :=
  ⨆a, coinduced (Sigma.mk a) (t₂ a)

instance Pi.topologicalSpace {β : α → Type v} [t₂ : ∀ a, TopologicalSpace (β a)] : TopologicalSpace (∀ a, β a) :=
  ⨅a, induced (fun f => f a) (t₂ a)

instance Ulift.topologicalSpace [t : TopologicalSpace α] : TopologicalSpace (Ulift.{v, u} α) :=
  t.induced Ulift.down

theorem Quotientₓ.preimage_mem_nhds [TopologicalSpace α] [s : Setoidₓ α] {V : Set$ Quotientₓ s} {a : α}
  (hs : V ∈ 𝓝 (Quotientₓ.mk a)) : Quotientₓ.mk ⁻¹' V ∈ 𝓝 a :=
  preimage_nhds_coinduced hs

/-- The image of a dense set under `quotient.mk` is a dense set. -/
theorem Dense.quotient [Setoidₓ α] [TopologicalSpace α] {s : Set α} (H : Dense s) : Dense (Quotientₓ.mk '' s) :=
  (surjective_quotient_mk α).DenseRange.dense_image continuous_coinduced_rng H

/-- The composition of `quotient.mk` and a function with dense range has dense range. -/
theorem DenseRange.quotient [Setoidₓ α] [TopologicalSpace α] {f : β → α} (hf : DenseRange f) :
  DenseRange (Quotientₓ.mk ∘ f) :=
  (surjective_quotient_mk α).DenseRange.comp hf continuous_coinduced_rng

instance  {p : α → Prop} [TopologicalSpace α] [DiscreteTopology α] : DiscreteTopology (Subtype p) :=
  ⟨bot_unique$ fun s hs => ⟨coeₓ '' s, is_open_discrete _, Set.preimage_image_eq _ Subtype.coe_injective⟩⟩

instance Sum.discrete_topology [TopologicalSpace α] [TopologicalSpace β] [hα : DiscreteTopology α]
  [hβ : DiscreteTopology β] : DiscreteTopology (Sum α β) :=
  ⟨by 
      unfold Sum.topologicalSpace <;> simp [hα.eq_bot, hβ.eq_bot]⟩

instance Sigma.discrete_topology {β : α → Type v} [∀ a, TopologicalSpace (β a)] [h : ∀ a, DiscreteTopology (β a)] :
  DiscreteTopology (Sigma β) :=
  ⟨by 
      unfold Sigma.topologicalSpace 
      simp [fun a => (h a).eq_bot]⟩

section Topα

variable[TopologicalSpace α]

theorem mem_nhds_subtype (s : Set α) (a : { x // x ∈ s }) (t : Set { x // x ∈ s }) :
  t ∈ 𝓝 a ↔ ∃ (u : _)(_ : u ∈ 𝓝 (a : α)), coeₓ ⁻¹' u ⊆ t :=
  mem_nhds_induced coeₓ a t

theorem nhds_subtype (s : Set α) (a : { x // x ∈ s }) : 𝓝 a = comap coeₓ (𝓝 (a : α)) :=
  nhds_induced coeₓ a

end Topα

end Constructions

section Prod

variable[TopologicalSpace α][TopologicalSpace β][TopologicalSpace γ][TopologicalSpace δ]

@[continuity]
theorem continuous_fst : Continuous (@Prod.fst α β) :=
  continuous_inf_dom_left continuous_induced_dom

theorem continuous_at_fst {p : α × β} : ContinuousAt Prod.fst p :=
  continuous_fst.ContinuousAt

theorem Continuous.fst {f : α → β × γ} (hf : Continuous f) : Continuous fun a : α => (f a).1 :=
  continuous_fst.comp hf

theorem ContinuousAt.fst {f : α → β × γ} {x : α} (hf : ContinuousAt f x) : ContinuousAt (fun a : α => (f a).1) x :=
  continuous_at_fst.comp hf

@[continuity]
theorem continuous_snd : Continuous (@Prod.snd α β) :=
  continuous_inf_dom_right continuous_induced_dom

theorem continuous_at_snd {p : α × β} : ContinuousAt Prod.snd p :=
  continuous_snd.ContinuousAt

theorem Continuous.snd {f : α → β × γ} (hf : Continuous f) : Continuous fun a : α => (f a).2 :=
  continuous_snd.comp hf

theorem ContinuousAt.snd {f : α → β × γ} {x : α} (hf : ContinuousAt f x) : ContinuousAt (fun a : α => (f a).2) x :=
  continuous_at_snd.comp hf

@[continuity]
theorem Continuous.prod_mk {f : γ → α} {g : γ → β} (hf : Continuous f) (hg : Continuous g) :
  Continuous fun x => (f x, g x) :=
  continuous_inf_rng (continuous_induced_rng hf) (continuous_induced_rng hg)

@[continuity]
theorem Continuous.Prod.mk (a : α) : Continuous (Prod.mk a : β → α × β) :=
  continuous_const.prod_mk continuous_id'

theorem Continuous.prod_map {f : γ → α} {g : δ → β} (hf : Continuous f) (hg : Continuous g) :
  Continuous fun x : γ × δ => (f x.1, g x.2) :=
  (hf.comp continuous_fst).prod_mk (hg.comp continuous_snd)

theorem Filter.Eventually.prod_inl_nhds {p : α → Prop} {a : α} (h : ∀ᶠx in 𝓝 a, p x) (b : β) :
  ∀ᶠx in 𝓝 (a, b), p (x : α × β).1 :=
  continuous_at_fst h

theorem Filter.Eventually.prod_inr_nhds {p : β → Prop} {b : β} (h : ∀ᶠx in 𝓝 b, p x) (a : α) :
  ∀ᶠx in 𝓝 (a, b), p (x : α × β).2 :=
  continuous_at_snd h

theorem Filter.Eventually.prod_mk_nhds {pa : α → Prop} {a} (ha : ∀ᶠx in 𝓝 a, pa x) {pb : β → Prop} {b}
  (hb : ∀ᶠy in 𝓝 b, pb y) : ∀ᶠp in 𝓝 (a, b), pa (p : α × β).1 ∧ pb p.2 :=
  (ha.prod_inl_nhds b).And (hb.prod_inr_nhds a)

theorem continuous_swap : Continuous (Prod.swap : α × β → β × α) :=
  continuous_snd.prod_mk continuous_fst

theorem continuous_uncurry_left {f : α → β → γ} (a : α) (h : Continuous (Function.uncurry f)) : Continuous (f a) :=
  show Continuous (Function.uncurry f ∘ fun b => (a, b)) from
    h.comp
      (by 
        continuity)

theorem continuous_uncurry_right {f : α → β → γ} (b : β) (h : Continuous (Function.uncurry f)) :
  Continuous fun a => f a b :=
  show Continuous (Function.uncurry f ∘ fun a => (a, b)) from
    h.comp
      (by 
        continuity)

theorem continuous_curry {g : α × β → γ} (a : α) (h : Continuous g) : Continuous (Function.curry g a) :=
  show Continuous (g ∘ fun b => (a, b)) from
    h.comp
      (by 
        continuity)

theorem IsOpen.prod {s : Set α} {t : Set β} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (Set.Prod s t) :=
  IsOpen.inter (hs.preimage continuous_fst) (ht.preimage continuous_snd)

theorem nhds_prod_eq {a : α} {b : β} : 𝓝 (a, b) = 𝓝 a ×ᶠ 𝓝 b :=
  by 
    rw [Filter.prod, Prod.topologicalSpace, nhds_inf, nhds_induced, nhds_induced]

theorem mem_nhds_prod_iff {a : α} {b : β} {s : Set (α × β)} :
  s ∈ 𝓝 (a, b) ↔ ∃ (u : _)(_ : u ∈ 𝓝 a)(v : _)(_ : v ∈ 𝓝 b), Set.Prod u v ⊆ s :=
  by 
    rw [nhds_prod_eq, mem_prod_iff]

theorem mem_nhds_prod_iff' {a : α} {b : β} {s : Set (α × β)} :
  s ∈ 𝓝 (a, b) ↔ ∃ u v, IsOpen u ∧ a ∈ u ∧ IsOpen v ∧ b ∈ v ∧ Set.Prod u v ⊆ s :=
  by 
    rw [mem_nhds_prod_iff]
    split 
    ·
      rintro ⟨u, Hu, v, Hv, h⟩
      rcases mem_nhds_iff.1 Hu with ⟨u', u'u, u'_open, Hu'⟩
      rcases mem_nhds_iff.1 Hv with ⟨v', v'v, v'_open, Hv'⟩
      exact ⟨u', v', u'_open, Hu', v'_open, Hv', (Set.prod_mono u'u v'v).trans h⟩
    ·
      rintro ⟨u, v, u_open, au, v_open, bv, huv⟩
      exact ⟨u, u_open.mem_nhds au, v, v_open.mem_nhds bv, huv⟩

theorem Filter.HasBasis.prod_nhds {ιa ιb : Type _} {pa : ιa → Prop} {pb : ιb → Prop} {sa : ιa → Set α} {sb : ιb → Set β}
  {a : α} {b : β} (ha : (𝓝 a).HasBasis pa sa) (hb : (𝓝 b).HasBasis pb sb) :
  (𝓝 (a, b)).HasBasis (fun i : ιa × ιb => pa i.1 ∧ pb i.2) fun i => (sa i.1).Prod (sb i.2) :=
  by 
    rw [nhds_prod_eq]
    exact ha.prod hb

theorem Filter.HasBasis.prod_nhds' {ιa ιb : Type _} {pa : ιa → Prop} {pb : ιb → Prop} {sa : ιa → Set α}
  {sb : ιb → Set β} {ab : α × β} (ha : (𝓝 ab.1).HasBasis pa sa) (hb : (𝓝 ab.2).HasBasis pb sb) :
  (𝓝 ab).HasBasis (fun i : ιa × ιb => pa i.1 ∧ pb i.2) fun i => (sa i.1).Prod (sb i.2) :=
  by 
    cases ab 
    exact ha.prod_nhds hb

instance  [DiscreteTopology α] [DiscreteTopology β] : DiscreteTopology (α × β) :=
  ⟨eq_of_nhds_eq_nhds$
      fun ⟨a, b⟩ =>
        by 
          rw [nhds_prod_eq, nhds_discrete α, nhds_discrete β, nhds_bot, Filter.prod_pure_pure]⟩

theorem prod_mem_nhds_iff {s : Set α} {t : Set β} {a : α} {b : β} : s.prod t ∈ 𝓝 (a, b) ↔ s ∈ 𝓝 a ∧ t ∈ 𝓝 b :=
  by 
    rw [nhds_prod_eq, prod_mem_prod_iff]

theorem ProdIsOpen.mem_nhds {s : Set α} {t : Set β} {a : α} {b : β} (ha : s ∈ 𝓝 a) (hb : t ∈ 𝓝 b) :
  Set.Prod s t ∈ 𝓝 (a, b) :=
  prod_mem_nhds_iff.2 ⟨ha, hb⟩

theorem nhds_swap (a : α) (b : β) : 𝓝 (a, b) = (𝓝 (b, a)).map Prod.swap :=
  by 
    rw [nhds_prod_eq, Filter.prod_comm, nhds_prod_eq] <;> rfl

theorem Filter.Tendsto.prod_mk_nhds {γ} {a : α} {b : β} {f : Filter γ} {ma : γ → α} {mb : γ → β}
  (ha : tendsto ma f (𝓝 a)) (hb : tendsto mb f (𝓝 b)) : tendsto (fun c => (ma c, mb c)) f (𝓝 (a, b)) :=
  by 
    rw [nhds_prod_eq] <;> exact Filter.Tendsto.prod_mk ha hb

theorem Filter.Eventually.curry_nhds {p : α × β → Prop} {x : α} {y : β} (h : ∀ᶠx in 𝓝 (x, y), p x) :
  ∀ᶠx' in 𝓝 x, ∀ᶠy' in 𝓝 y, p (x', y') :=
  by 
    rw [nhds_prod_eq] at h 
    exact h.curry

theorem ContinuousAt.prod {f : α → β} {g : α → γ} {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
  ContinuousAt (fun x => (f x, g x)) x :=
  hf.prod_mk_nhds hg

theorem ContinuousAt.prod_map {f : α → γ} {g : β → δ} {p : α × β} (hf : ContinuousAt f p.fst)
  (hg : ContinuousAt g p.snd) : ContinuousAt (fun p : α × β => (f p.1, g p.2)) p :=
  (hf.comp continuous_at_fst).Prod (hg.comp continuous_at_snd)

theorem ContinuousAt.prod_map' {f : α → γ} {g : β → δ} {x : α} {y : β} (hf : ContinuousAt f x) (hg : ContinuousAt g y) :
  ContinuousAt (fun p : α × β => (f p.1, g p.2)) (x, y) :=
  have hf : ContinuousAt f (x, y).fst := hf 
  have hg : ContinuousAt g (x, y).snd := hg 
  hf.prod_map hg

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prod_generate_from_generate_from_eq
{α β : Type*}
{s : set (set α)}
{t : set (set β)}
(hs : «expr = »(«expr⋃₀ »(s), univ))
(ht : «expr = »(«expr⋃₀ »(t), univ)) : «expr = »(@prod.topological_space α β (generate_from s) (generate_from t), generate_from {g | «expr∃ , »((u «expr ∈ » s), «expr∃ , »((v «expr ∈ » t), «expr = »(g, set.prod u v)))}) :=
let G := generate_from {g | «expr∃ , »((u «expr ∈ » s), «expr∃ , »((v «expr ∈ » t), «expr = »(g, set.prod u v)))} in
le_antisymm «expr $ »(le_generate_from, assume
 (g)
 ⟨u, hu, v, hv, g_eq⟩, «expr ▸ »(g_eq.symm, @is_open.prod _ _ (generate_from s) (generate_from t) _ _ (generate_open.basic _ hu) (generate_open.basic _ hv))) (le_inf «expr $ »(coinduced_le_iff_le_induced.mp, «expr $ »(le_generate_from, assume
   u hu, have «expr = »(«expr⋃ , »((v «expr ∈ » t), set.prod u v), «expr ⁻¹' »(prod.fst, u)), from calc
     «expr = »(«expr⋃ , »((v «expr ∈ » t), set.prod u v), set.prod u univ) : «expr $ »(set.ext, assume
      ⟨a, b⟩, by rw ["<-", expr ht] []; simp [] [] [] ["[", expr and.left_comm, "]"] [] [] { contextual := tt })
     «expr = »(..., «expr ⁻¹' »(prod.fst, u)) : by simp [] [] [] ["[", expr set.prod, ",", expr preimage, "]"] [] [],
   show G.is_open «expr ⁻¹' »(prod.fst, u), from «expr $ »(«expr ▸ »(this, @is_open_Union _ _ G _), assume
    v, «expr $ »(@is_open_Union _ _ G _, assume
     hv, generate_open.basic _ ⟨_, hu, _, hv, rfl⟩)))) «expr $ »(coinduced_le_iff_le_induced.mp, «expr $ »(le_generate_from, assume
   v hv, have «expr = »(«expr⋃ , »((u «expr ∈ » s), set.prod u v), «expr ⁻¹' »(prod.snd, v)), from calc
     «expr = »(«expr⋃ , »((u «expr ∈ » s), set.prod u v), set.prod univ v) : «expr $ »(set.ext, assume
      ⟨a, b⟩, by rw ["[", "<-", expr hs, "]"] []; by_cases [expr «expr ∈ »(b, v)]; simp [] [] [] ["[", expr h, "]"] [] [] { contextual := tt })
     «expr = »(..., «expr ⁻¹' »(prod.snd, v)) : by simp [] [] [] ["[", expr set.prod, ",", expr preimage, "]"] [] [],
   show G.is_open «expr ⁻¹' »(prod.snd, v), from «expr $ »(«expr ▸ »(this, @is_open_Union _ _ G _), assume
    u, «expr $ »(@is_open_Union _ _ G _, assume hu, generate_open.basic _ ⟨_, hu, _, hv, rfl⟩)))))

theorem prod_eq_generate_from :
  Prod.topologicalSpace = generate_from { g | ∃ (s : Set α)(t : Set β), IsOpen s ∧ IsOpen t ∧ g = Set.Prod s t } :=
  le_antisymmₓ (le_generate_from$ fun g ⟨s, t, hs, ht, g_eq⟩ => g_eq.symm ▸ hs.prod ht)
    (le_inf
      (ball_image_of_ball$
        fun t ht =>
          generate_open.basic _
            ⟨t, univ,
              by 
                simpa [Set.prod_eq] using ht⟩)
      (ball_image_of_ball$
        fun t ht =>
          generate_open.basic _
            ⟨univ, t,
              by 
                simpa [Set.prod_eq] using ht⟩))

theorem is_open_prod_iff {s : Set (α × β)} :
  IsOpen s ↔ ∀ a b, (a, b) ∈ s → ∃ u v, IsOpen u ∧ IsOpen v ∧ a ∈ u ∧ b ∈ v ∧ Set.Prod u v ⊆ s :=
  by 
    rw [is_open_iff_nhds]
    simpRw [le_principal_iff, Prod.forall, ((nhds_basis_opens _).prod_nhds (nhds_basis_opens _)).mem_iff, Prod.exists,
      exists_prop]
    simp only [and_assoc, And.left_comm]

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A product of induced topologies is induced by the product map -/
theorem prod_induced_induced
{α γ : Type*}
(f : α → β)
(g : γ → δ) : «expr = »(@prod.topological_space α γ (induced f «expr‹ ›»(_)) (induced g «expr‹ ›»(_)), induced (λ
  p, (f p.1, g p.2)) prod.topological_space) :=
begin
  set [] [ident fxg] [] [":="] [expr λ p : «expr × »(α, γ), (f p.1, g p.2)] [],
  have [ident key1] [":", expr «expr = »(«expr ∘ »(f, (prod.fst : «expr × »(α, γ) → α)), «expr ∘ »((prod.fst : «expr × »(β, δ) → β), fxg))] [],
  from [expr rfl],
  have [ident key2] [":", expr «expr = »(«expr ∘ »(g, (prod.snd : «expr × »(α, γ) → γ)), «expr ∘ »((prod.snd : «expr × »(β, δ) → δ), fxg))] [],
  from [expr rfl],
  unfold [ident prod.topological_space] [],
  conv_lhs [] [] { rw ["[", expr induced_compose, ",", expr induced_compose, ",", expr key1, ",", expr key2, "]"],
    congr,
    rw ["<-", expr induced_compose],
    skip,
    rw ["<-", expr induced_compose] },
  rw [expr induced_inf] []
end

theorem continuous_uncurry_of_discrete_topology_left [DiscreteTopology α] {f : α → β → γ} (h : ∀ a, Continuous (f a)) :
  Continuous (Function.uncurry f) :=
  continuous_iff_continuous_at.2$
    fun ⟨a, b⟩ =>
      by 
        simp only [ContinuousAt, nhds_prod_eq, nhds_discrete α, pure_prod, tendsto_map'_iff, · ∘ ·, Function.uncurry,
          (h a).Tendsto]

/-- Given a neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborhood
  that is a subset of `s`. -/
theorem exists_nhds_square {s : Set (α × α)} {x : α} (hx : s ∈ 𝓝 (x, x)) : ∃ U, IsOpen U ∧ x ∈ U ∧ Set.Prod U U ⊆ s :=
  by 
    simpa [nhds_prod_eq, (nhds_basis_opens x).prod_self.mem_iff, And.assoc, And.left_comm] using hx

/-- `prod.fst` maps neighborhood of `x : α × β` within the section `prod.snd ⁻¹' {x.2}`
to `𝓝 x.1`. -/
theorem map_fst_nhds_within (x : α × β) : map Prod.fst (𝓝[Prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1 :=
  by 
    refine' le_antisymmₓ (continuous_at_fst.mono_left inf_le_left) fun s hs => _ 
    rcases x with ⟨x, y⟩
    rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs 
    rcases hs with ⟨u, hu, v, hv, H⟩
    simp only [prod_subset_iff, mem_singleton_iff, mem_set_of_eq, mem_preimage] at H 
    exact mem_of_superset hu fun z hz => H _ hz _ (mem_of_mem_nhds hv) rfl

@[simp]
theorem map_fst_nhds (x : α × β) : map Prod.fst (𝓝 x) = 𝓝 x.1 :=
  le_antisymmₓ continuous_at_fst$ (map_fst_nhds_within x).symm.trans_le (map_mono inf_le_left)

/-- The first projection in a product of topological spaces sends open sets to open sets. -/
theorem is_open_map_fst : IsOpenMap (@Prod.fst α β) :=
  is_open_map_iff_nhds_le.2$ fun x => (map_fst_nhds x).Ge

/-- `prod.snd` maps neighborhood of `x : α × β` within the section `prod.fst ⁻¹' {x.1}`
to `𝓝 x.2`. -/
theorem map_snd_nhds_within (x : α × β) : map Prod.snd (𝓝[Prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2 :=
  by 
    refine' le_antisymmₓ (continuous_at_snd.mono_left inf_le_left) fun s hs => _ 
    rcases x with ⟨x, y⟩
    rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs 
    rcases hs with ⟨u, hu, v, hv, H⟩
    simp only [prod_subset_iff, mem_singleton_iff, mem_set_of_eq, mem_preimage] at H 
    exact mem_of_superset hv fun z hz => H _ (mem_of_mem_nhds hu) _ hz rfl

@[simp]
theorem map_snd_nhds (x : α × β) : map Prod.snd (𝓝 x) = 𝓝 x.2 :=
  le_antisymmₓ continuous_at_snd$ (map_snd_nhds_within x).symm.trans_le (map_mono inf_le_left)

/-- The second projection in a product of topological spaces sends open sets to open sets. -/
theorem is_open_map_snd : IsOpenMap (@Prod.snd α β) :=
  is_open_map_iff_nhds_le.2$ fun x => (map_snd_nhds x).Ge

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A product set is open in a product space if and only if each factor is open, or one of them is
empty -/
theorem is_open_prod_iff'
{s : set α}
{t : set β} : «expr ↔ »(is_open (set.prod s t), «expr ∨ »(«expr ∧ »(is_open s, is_open t), «expr ∨ »(«expr = »(s, «expr∅»()), «expr = »(t, «expr∅»())))) :=
begin
  cases [expr (set.prod s t).eq_empty_or_nonempty] ["with", ident h, ident h],
  { simp [] [] [] ["[", expr h, ",", expr prod_eq_empty_iff.1 h, "]"] [] [] },
  { have [ident st] [":", expr «expr ∧ »(s.nonempty, t.nonempty)] [],
    from [expr prod_nonempty_iff.1 h],
    split,
    { assume [binders (H : is_open (set.prod s t))],
      refine [expr or.inl ⟨_, _⟩],
      show [expr is_open s],
      { rw ["<-", expr fst_image_prod s st.2] [],
        exact [expr is_open_map_fst _ H] },
      show [expr is_open t],
      { rw ["<-", expr snd_image_prod st.1 t] [],
        exact [expr is_open_map_snd _ H] } },
    { assume [binders (H)],
      simp [] [] ["only"] ["[", expr st.1.ne_empty, ",", expr st.2.ne_empty, ",", expr not_false_iff, ",", expr or_false, "]"] [] ["at", ident H],
      exact [expr H.1.prod H.2] } }
end

theorem closure_prod_eq {s : Set α} {t : Set β} : Closure (Set.Prod s t) = Set.Prod (Closure s) (Closure t) :=
  Set.ext$
    fun ⟨a, b⟩ =>
      have  : (𝓝 a ×ᶠ 𝓝 b)⊓𝓟 (Set.Prod s t) = 𝓝 a⊓𝓟 s ×ᶠ 𝓝 b⊓𝓟 t :=
        by 
          rw [←prod_inf_prod, prod_principal_principal]
      by 
        simp [closure_eq_cluster_pts, ClusterPt, nhds_prod_eq, this] <;> exact prod_ne_bot

theorem interior_prod_eq (s : Set α) (t : Set β) : Interior (s.prod t) = (Interior s).Prod (Interior t) :=
  Set.ext$
    fun ⟨a, b⟩ =>
      by 
        simp only [mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff]

theorem frontier_prod_eq (s : Set α) (t : Set β) :
  Frontier (s.prod t) = (Closure s).Prod (Frontier t) ∪ (Frontier s).Prod (Closure t) :=
  by 
    simp only [Frontier, closure_prod_eq, interior_prod_eq, prod_diff_prod]

@[simp]
theorem frontier_prod_univ_eq (s : Set α) : Frontier (s.prod (univ : Set β)) = (Frontier s).Prod univ :=
  by 
    simp [frontier_prod_eq]

@[simp]
theorem frontier_univ_prod_eq (s : Set β) : Frontier ((univ : Set α).Prod s) = (univ : Set α).Prod (Frontier s) :=
  by 
    simp [frontier_prod_eq]

theorem map_mem_closure2 {s : Set α} {t : Set β} {u : Set γ} {f : α → β → γ} {a : α} {b : β}
  (hf : Continuous fun p : α × β => f p.1 p.2) (ha : a ∈ Closure s) (hb : b ∈ Closure t)
  (hu : ∀ a b, a ∈ s → b ∈ t → f a b ∈ u) : f a b ∈ Closure u :=
  have  : (a, b) ∈ Closure (Set.Prod s t) :=
    by 
      rw [closure_prod_eq] <;> exact ⟨ha, hb⟩
  show (fun p : α × β => f p.1 p.2) (a, b) ∈ Closure u from map_mem_closure hf this$ fun ⟨a, b⟩ ⟨ha, hb⟩ => hu a b ha hb

theorem IsClosed.prod {s₁ : Set α} {s₂ : Set β} (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : IsClosed (Set.Prod s₁ s₂) :=
  closure_eq_iff_is_closed.mp$
    by 
      simp only [h₁.closure_eq, h₂.closure_eq, closure_prod_eq]

/-- The product of two dense sets is a dense set. -/
theorem Dense.prod {s : Set α} {t : Set β} (hs : Dense s) (ht : Dense t) : Dense (s.prod t) :=
  fun x =>
    by 
      rw [closure_prod_eq]
      exact ⟨hs x.1, ht x.2⟩

/-- If `f` and `g` are maps with dense range, then `prod.map f g` has dense range. -/
theorem DenseRange.prod_map {ι : Type _} {κ : Type _} {f : ι → β} {g : κ → γ} (hf : DenseRange f) (hg : DenseRange g) :
  DenseRange (Prod.mapₓ f g) :=
  by 
    simpa only [DenseRange, prod_range_range_eq] using hf.prod hg

theorem Inducing.prod_mk {f : α → β} {g : γ → δ} (hf : Inducing f) (hg : Inducing g) :
  Inducing fun x : α × γ => (f x.1, g x.2) :=
  ⟨by 
      rw [Prod.topologicalSpace, Prod.topologicalSpace, hf.induced, hg.induced, induced_compose, induced_compose,
        induced_inf, induced_compose, induced_compose]⟩

theorem Embedding.prod_mk {f : α → β} {g : γ → δ} (hf : Embedding f) (hg : Embedding g) :
  Embedding fun x : α × γ => (f x.1, g x.2) :=
  { hf.to_inducing.prod_mk hg.to_inducing with
    inj :=
      fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ =>
        by 
          simp  <;> exact fun h₁ h₂ => ⟨hf.inj h₁, hg.inj h₂⟩ }

protected theorem IsOpenMap.prod {f : α → β} {g : γ → δ} (hf : IsOpenMap f) (hg : IsOpenMap g) :
  IsOpenMap fun p : α × γ => (f p.1, g p.2) :=
  by 
    rw [is_open_map_iff_nhds_le]
    rintro ⟨a, b⟩
    rw [nhds_prod_eq, nhds_prod_eq, ←Filter.prod_map_map_eq]
    exact Filter.prod_mono (is_open_map_iff_nhds_le.1 hf a) (is_open_map_iff_nhds_le.1 hg b)

protected theorem OpenEmbedding.prod {f : α → β} {g : γ → δ} (hf : OpenEmbedding f) (hg : OpenEmbedding g) :
  OpenEmbedding fun x : α × γ => (f x.1, g x.2) :=
  open_embedding_of_embedding_open (hf.1.prod_mk hg.1) (hf.is_open_map.prod hg.is_open_map)

theorem embedding_graph {f : α → β} (hf : Continuous f) : Embedding fun x => (x, f x) :=
  embedding_of_embedding_compose (continuous_id.prod_mk hf) continuous_fst embedding_id

end Prod

section Sum

open Sum

variable[TopologicalSpace α][TopologicalSpace β][TopologicalSpace γ]

@[continuity]
theorem continuous_inl : Continuous (@inl α β) :=
  continuous_sup_rng_left continuous_coinduced_rng

@[continuity]
theorem continuous_inr : Continuous (@inr α β) :=
  continuous_sup_rng_right continuous_coinduced_rng

@[continuity]
theorem continuous_sum_rec {f : α → γ} {g : β → γ} (hf : Continuous f) (hg : Continuous g) :
  @Continuous (Sum α β) γ _ _ (@Sum.rec α β (fun _ => γ) f g) :=
  by 
    apply continuous_sup_dom <;> rw [continuous_def] at hf hg⊢ <;> assumption

theorem is_open_sum_iff {s : Set (Sum α β)} : IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsOpen (inr ⁻¹' s) :=
  Iff.rfl

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_open_map_sum
{f : «expr ⊕ »(α, β) → γ}
(h₁ : is_open_map (λ a, f (inl a)))
(h₂ : is_open_map (λ b, f (inr b))) : is_open_map f :=
begin
  intros [ident u, ident hu],
  rw [expr is_open_sum_iff] ["at", ident hu],
  cases [expr hu] ["with", ident hu₁, ident hu₂],
  have [] [":", expr «expr = »(u, «expr ∪ »(«expr '' »(inl, «expr ⁻¹' »(inl, u)), «expr '' »(inr, «expr ⁻¹' »(inr, u))))] [],
  { ext [] ["(", "_", "|", "_", ")"] []; simp [] [] [] [] [] [] },
  rw ["[", expr this, ",", expr set.image_union, ",", expr set.image_image, ",", expr set.image_image, "]"] [],
  exact [expr is_open.union (h₁ _ hu₁) (h₂ _ hu₂)]
end

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem embedding_inl : embedding (@inl α β) :=
{ induced := begin
    unfold [ident sum.topological_space] [],
    apply [expr le_antisymm],
    { rw ["<-", expr coinduced_le_iff_le_induced] [],
      exact [expr le_sup_left] },
    { intros [ident u, ident hu],
      existsi [expr «expr '' »(inl, u)],
      change [expr «expr ∧ »(«expr ∧ »(is_open «expr ⁻¹' »(inl, «expr '' »(@inl α β, u)), is_open «expr ⁻¹' »(inr, «expr '' »(@inl α β, u))), «expr = »(«expr ⁻¹' »(inl, «expr '' »(inl, u)), u))] [] [],
      have [] [":", expr «expr = »(«expr ⁻¹' »(inl, «expr '' »(@inl α β, u)), u)] [":=", expr preimage_image_eq u (λ
        _ _, inl.inj_iff.mp)],
      rw [expr this] [],
      have [] [":", expr «expr = »(«expr ⁻¹' »(inr, «expr '' »(@inl α β, u)), «expr∅»())] [":=", expr eq_empty_iff_forall_not_mem.mpr (assume
        (a)
        ⟨b, _, h⟩, inl_ne_inr h)],
      rw [expr this] [],
      exact [expr ⟨⟨hu, is_open_empty⟩, rfl⟩] }
  end,
  inj := λ _ _, inl.inj_iff.mp }

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem embedding_inr : embedding (@inr α β) :=
{ induced := begin
    unfold [ident sum.topological_space] [],
    apply [expr le_antisymm],
    { rw ["<-", expr coinduced_le_iff_le_induced] [],
      exact [expr le_sup_right] },
    { intros [ident u, ident hu],
      existsi [expr «expr '' »(inr, u)],
      change [expr «expr ∧ »(«expr ∧ »(is_open «expr ⁻¹' »(inl, «expr '' »(@inr α β, u)), is_open «expr ⁻¹' »(inr, «expr '' »(@inr α β, u))), «expr = »(«expr ⁻¹' »(inr, «expr '' »(inr, u)), u))] [] [],
      have [] [":", expr «expr = »(«expr ⁻¹' »(inl, «expr '' »(@inr α β, u)), «expr∅»())] [":=", expr eq_empty_iff_forall_not_mem.mpr (assume
        (b)
        ⟨a, _, h⟩, inr_ne_inl h)],
      rw [expr this] [],
      have [] [":", expr «expr = »(«expr ⁻¹' »(inr, «expr '' »(@inr α β, u)), u)] [":=", expr preimage_image_eq u (λ
        _ _, inr.inj_iff.mp)],
      rw [expr this] [],
      exact [expr ⟨⟨is_open_empty, hu⟩, rfl⟩] }
  end,
  inj := λ _ _, inr.inj_iff.mp }

theorem is_open_range_inl : IsOpen (range (inl : α → Sum α β)) :=
  is_open_sum_iff.2$
    by 
      simp 

theorem is_open_range_inr : IsOpen (range (inr : β → Sum α β)) :=
  is_open_sum_iff.2$
    by 
      simp 

theorem open_embedding_inl : OpenEmbedding (inl : α → Sum α β) :=
  { embedding_inl with open_range := is_open_range_inl }

theorem open_embedding_inr : OpenEmbedding (inr : β → Sum α β) :=
  { embedding_inr with open_range := is_open_range_inr }

end Sum

section Subtype

variable[TopologicalSpace α][TopologicalSpace β][TopologicalSpace γ]{p : α → Prop}

theorem embedding_subtype_coe : Embedding (coeₓ : Subtype p → α) :=
  ⟨⟨rfl⟩, Subtype.coe_injective⟩

theorem closed_embedding_subtype_coe (h : IsClosed { a | p a }) : ClosedEmbedding (coeₓ : Subtype p → α) :=
  ⟨embedding_subtype_coe,
    by 
      rwa [Subtype.range_coe_subtype]⟩

@[continuity]
theorem continuous_subtype_val : Continuous (@Subtype.val α p) :=
  continuous_induced_dom

theorem continuous_subtype_coe : Continuous (coeₓ : Subtype p → α) :=
  continuous_subtype_val

theorem IsOpen.open_embedding_subtype_coe {s : Set α} (hs : IsOpen s) : OpenEmbedding (coeₓ : s → α) :=
  { induced := rfl, inj := Subtype.coe_injective, open_range := (Subtype.range_coe : range coeₓ = s).symm ▸ hs }

theorem IsOpen.is_open_map_subtype_coe {s : Set α} (hs : IsOpen s) : IsOpenMap (coeₓ : s → α) :=
  hs.open_embedding_subtype_coe.is_open_map

theorem IsOpenMap.restrict {f : α → β} (hf : IsOpenMap f) {s : Set α} (hs : IsOpen s) : IsOpenMap (s.restrict f) :=
  hf.comp hs.is_open_map_subtype_coe

theorem IsClosed.closed_embedding_subtype_coe {s : Set α} (hs : IsClosed s) :
  ClosedEmbedding (coeₓ : { x // x ∈ s } → α) :=
  { induced := rfl, inj := Subtype.coe_injective, closed_range := (Subtype.range_coe : range coeₓ = s).symm ▸ hs }

@[continuity]
theorem continuous_subtype_mk {f : β → α} (hp : ∀ x, p (f x)) (h : Continuous f) :
  Continuous fun x => (⟨f x, hp x⟩ : Subtype p) :=
  continuous_induced_rng h

theorem continuous_inclusion {s t : Set α} (h : s ⊆ t) : Continuous (inclusion h) :=
  continuous_subtype_mk _ continuous_subtype_coe

theorem continuous_at_subtype_coe {p : α → Prop} {a : Subtype p} : ContinuousAt (coeₓ : Subtype p → α) a :=
  continuous_iff_continuous_at.mp continuous_subtype_coe _

theorem map_nhds_subtype_coe_eq {a : α} (ha : p a) (h : { a | p a } ∈ 𝓝 a) :
  map (coeₓ : Subtype p → α) (𝓝 ⟨a, ha⟩) = 𝓝 a :=
  map_nhds_induced_of_mem$
    by 
      simpa only [Subtype.coe_mk, Subtype.range_coe] using h

theorem nhds_subtype_eq_comap {a : α} {h : p a} : 𝓝 (⟨a, h⟩ : Subtype p) = comap coeₓ (𝓝 a) :=
  nhds_induced _ _

theorem tendsto_subtype_rng {β : Type _} {p : α → Prop} {b : Filter β} {f : β → Subtype p} :
  ∀ {a : Subtype p}, tendsto f b (𝓝 a) ↔ tendsto (fun x => (f x : α)) b (𝓝 (a : α))
| ⟨a, ha⟩ =>
  by 
    rw [nhds_subtype_eq_comap, tendsto_comap_iff, Subtype.coe_mk]

theorem continuous_subtype_nhds_cover {ι : Sort _} {f : α → β} {c : ι → α → Prop}
  (c_cover : ∀ x : α, ∃ i, { x | c i x } ∈ 𝓝 x) (f_cont : ∀ i, Continuous fun x : Subtype (c i) => f x) :
  Continuous f :=
  continuous_iff_continuous_at.mpr$
    fun x =>
      let ⟨i, (c_sets : { x | c i x } ∈ 𝓝 x)⟩ := c_cover x 
      let x' : Subtype (c i) := ⟨x, mem_of_mem_nhds c_sets⟩
      calc map f (𝓝 x) = map f (map coeₓ (𝓝 x')) := congr_argₓ (map f) (map_nhds_subtype_coe_eq _$ c_sets).symm 
        _ = map (fun x : Subtype (c i) => f x) (𝓝 x') := rfl 
        _ ≤ 𝓝 (f x) := continuous_iff_continuous_at.mp (f_cont i) x'
        

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_subtype_is_closed_cover
{ι : Sort*}
{f : α → β}
(c : ι → α → exprProp())
(h_lf : locally_finite (λ i, {x | c i x}))
(h_is_closed : ∀ i, is_closed {x | c i x})
(h_cover : ∀ x, «expr∃ , »((i), c i x))
(f_cont : ∀ i, continuous (λ x : subtype (c i), f x)) : continuous f :=
«expr $ »(continuous_iff_is_closed.mpr, assume
 s
 hs, have ∀
 i, is_closed «expr '' »((coe : {x | c i x} → α), «expr ⁻¹' »(«expr ∘ »(f, coe), s)), from assume
 i, (closed_embedding_subtype_coe (h_is_closed _)).is_closed_map _ (hs.preimage (f_cont i)),
 have is_closed «expr⋃ , »((i), «expr '' »((coe : {x | c i x} → α), «expr ⁻¹' »(«expr ∘ »(f, coe), s))), from locally_finite.is_closed_Union «expr $ »(h_lf.subset, assume
  (i x)
  ⟨⟨x', hx'⟩, _, heq⟩, «expr ▸ »(heq, hx')) this,
 have «expr = »(«expr ⁻¹' »(f, s), «expr⋃ , »((i), «expr '' »((coe : {x | c i x} → α), «expr ⁻¹' »(«expr ∘ »(f, coe), s)))), begin
   apply [expr set.ext],
   have [] [":", expr ∀
    x : α, «expr ↔ »(«expr ∈ »(f x, s), «expr∃ , »((i : ι), «expr ∧ »(c i x, «expr ∈ »(f x, s))))] [":=", expr λ
    x, ⟨λ hx, let ⟨i, hi⟩ := h_cover x in ⟨i, hi, hx⟩, λ ⟨i, hi, hx⟩, hx⟩],
   simpa [] [] [] ["[", expr and.comm, ",", expr @and.left_comm (c _ _), ",", "<-", expr exists_and_distrib_right, "]"] [] []
 end,
 by rwa ["[", expr this, "]"] [])

theorem closure_subtype {x : { a // p a }} {s : Set { a // p a }} :
  x ∈ Closure s ↔ (x : α) ∈ Closure ((coeₓ : _ → α) '' s) :=
  closure_induced

end Subtype

section Quotientₓ

variable[TopologicalSpace α][TopologicalSpace β][TopologicalSpace γ]

variable{r : α → α → Prop}{s : Setoidₓ α}

theorem quotient_map_quot_mk : QuotientMap (@Quot.mk α r) :=
  ⟨Quot.exists_rep, rfl⟩

@[continuity]
theorem continuous_quot_mk : Continuous (@Quot.mk α r) :=
  continuous_coinduced_rng

@[continuity]
theorem continuous_quot_lift {f : α → β} (hr : ∀ a b, r a b → f a = f b) (h : Continuous f) :
  Continuous (Quot.lift f hr : Quot r → β) :=
  continuous_coinduced_dom h

theorem quotient_map_quotient_mk : QuotientMap (@Quotientₓ.mk α s) :=
  quotient_map_quot_mk

theorem continuous_quotient_mk : Continuous (@Quotientₓ.mk α s) :=
  continuous_coinduced_rng

theorem continuous_quotient_lift {f : α → β} (hs : ∀ a b, a ≈ b → f a = f b) (h : Continuous f) :
  Continuous (Quotientₓ.lift f hs : Quotientₓ s → β) :=
  continuous_coinduced_dom h

end Quotientₓ

section Pi

variable{ι : Type _}{π : ι → Type _}

@[continuity]
theorem continuous_pi [TopologicalSpace α] [∀ i, TopologicalSpace (π i)] {f : α → ∀ i : ι, π i}
  (h : ∀ i, Continuous fun a => f a i) : Continuous f :=
  continuous_infi_rng$ fun i => continuous_induced_rng$ h i

@[continuity]
theorem continuous_apply [∀ i, TopologicalSpace (π i)] (i : ι) : Continuous fun p : ∀ i, π i => p i :=
  continuous_infi_dom continuous_induced_dom

theorem continuous_at_apply [∀ i, TopologicalSpace (π i)] (i : ι) (x : ∀ i, π i) :
  ContinuousAt (fun p : ∀ i, π i => p i) x :=
  (continuous_apply i).ContinuousAt

theorem Filter.Tendsto.apply [∀ i, TopologicalSpace (π i)] {l : Filter α} {f : α → ∀ i, π i} {x : ∀ i, π i}
  (h : tendsto f l (𝓝 x)) (i : ι) : tendsto (fun a => f a i) l (𝓝$ x i) :=
  (continuous_at_apply i _).Tendsto.comp h

theorem continuous_pi_iff [TopologicalSpace α] [∀ i, TopologicalSpace (π i)] {f : α → ∀ i, π i} :
  Continuous f ↔ ∀ i, Continuous fun y => f y i :=
  Iff.intro (fun h i => (continuous_apply i).comp h) continuous_pi

theorem nhds_pi [t : ∀ i, TopologicalSpace (π i)] {a : ∀ i, π i} : 𝓝 a = ⨅i, comap (fun x => x i) (𝓝 (a i)) :=
  calc 𝓝 a = ⨅i, @nhds _ (@TopologicalSpace.induced _ _ (fun x : ∀ i, π i => x i) (t i)) a := nhds_infi 
    _ = ⨅i, comap (fun x => x i) (𝓝 (a i)) :=
    by 
      simp [nhds_induced]
    

theorem tendsto_pi [t : ∀ i, TopologicalSpace (π i)] {f : α → ∀ i, π i} {g : ∀ i, π i} {u : Filter α} :
  tendsto f u (𝓝 g) ↔ ∀ x, tendsto (fun i => f i x) u (𝓝 (g x)) :=
  by 
    simp [nhds_pi, Filter.tendsto_comap_iff]

theorem continuous_at_pi [∀ i, TopologicalSpace (π i)] [TopologicalSpace α] {f : α → ∀ i, π i} {x : α} :
  ContinuousAt f x ↔ ∀ i, ContinuousAt (fun y => f y i) x :=
  tendsto_pi

theorem Filter.Tendsto.update [∀ i, TopologicalSpace (π i)] [DecidableEq ι] {l : Filter α} {f : α → ∀ i, π i}
  {x : ∀ i, π i} (hf : tendsto f l (𝓝 x)) (i : ι) {g : α → π i} {xi : π i} (hg : tendsto g l (𝓝 xi)) :
  tendsto (fun a => Function.update (f a) i (g a)) l (𝓝$ Function.update x i xi) :=
  tendsto_pi.2$
    fun j =>
      by 
        rcases em (j = i) with (rfl | hj) <;> simp [hf.apply]

theorem ContinuousAt.update [∀ i, TopologicalSpace (π i)] [TopologicalSpace α] [DecidableEq ι] {f : α → ∀ i, π i}
  {a : α} (hf : ContinuousAt f a) (i : ι) {g : α → π i} (hg : ContinuousAt g a) :
  ContinuousAt (fun a => Function.update (f a) i (g a)) a :=
  hf.update i hg

theorem Continuous.update [∀ i, TopologicalSpace (π i)] [TopologicalSpace α] [DecidableEq ι] {f : α → ∀ i, π i}
  (hf : Continuous f) (i : ι) {g : α → π i} (hg : Continuous g) : Continuous fun a => Function.update (f a) i (g a) :=
  continuous_iff_continuous_at.2$ fun x => hf.continuous_at.update i hg.continuous_at

/-- `function.update f i x` is continuous in `(f, x)`. -/
@[continuity]
theorem continuous_update [∀ i, TopologicalSpace (π i)] [DecidableEq ι] (i : ι) :
  Continuous fun f : (∀ j, π j) × π i => Function.update f.1 i f.2 :=
  continuous_fst.update i continuous_snd

theorem Filter.Tendsto.fin_insert_nth {n} {π : Finₓ (n+1) → Type _} [∀ i, TopologicalSpace (π i)] (i : Finₓ (n+1))
  {f : α → π i} {l : Filter α} {x : π i} (hf : tendsto f l (𝓝 x)) {g : α → ∀ j : Finₓ n, π (i.succ_above j)}
  {y : ∀ j, π (i.succ_above j)} (hg : tendsto g l (𝓝 y)) :
  tendsto (fun a => i.insert_nth (f a) (g a)) l (𝓝$ i.insert_nth x y) :=
  tendsto_pi.2
    fun j =>
      Finₓ.succAboveCases i
        (by 
          simpa)
        (by 
          simpa using tendsto_pi.1 hg)
        j

theorem ContinuousAt.fin_insert_nth {n} {π : Finₓ (n+1) → Type _} [∀ i, TopologicalSpace (π i)] [TopologicalSpace α]
  (i : Finₓ (n+1)) {f : α → π i} {a : α} (hf : ContinuousAt f a) {g : α → ∀ j : Finₓ n, π (i.succ_above j)}
  (hg : ContinuousAt g a) : ContinuousAt (fun a => i.insert_nth (f a) (g a)) a :=
  hf.fin_insert_nth i hg

theorem Continuous.fin_insert_nth {n} {π : Finₓ (n+1) → Type _} [∀ i, TopologicalSpace (π i)] [TopologicalSpace α]
  (i : Finₓ (n+1)) {f : α → π i} (hf : Continuous f) {g : α → ∀ j : Finₓ n, π (i.succ_above j)} (hg : Continuous g) :
  Continuous fun a => i.insert_nth (f a) (g a) :=
  continuous_iff_continuous_at.2$ fun a => hf.continuous_at.fin_insert_nth i hg.continuous_at

theorem is_open_set_pi [∀ a, TopologicalSpace (π a)] {i : Set ι} {s : ∀ a, Set (π a)} (hi : finite i)
  (hs : ∀ a _ : a ∈ i, IsOpen (s a)) : IsOpen (pi i s) :=
  by 
    rw [pi_def] <;> exact is_open_bInter hi$ fun a ha => (hs _ ha).Preimage (continuous_apply _)

theorem is_closed_set_pi [∀ a, TopologicalSpace (π a)] {i : Set ι} {s : ∀ a, Set (π a)}
  (hs : ∀ a _ : a ∈ i, IsClosed (s a)) : IsClosed (pi i s) :=
  by 
    rw [pi_def] <;> exact is_closed_Inter$ fun a => is_closed_Inter$ fun ha => (hs _ ha).Preimage (continuous_apply _)

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_nhds_pi
{ι : Type*}
{α : ι → Type*}
[∀ i : ι, topological_space (α i)]
{I : set ι}
{s : ∀ i, set (α i)}
(a : ∀ i, α i)
(hs : «expr ∈ »(I.pi s, expr𝓝() a))
{i : ι}
(hi : «expr ∈ »(i, I)) : «expr ∈ »(s i, expr𝓝() (a i)) :=
begin
  set [] [ident p] [] [":="] [expr λ i, λ x : ∀ i : ι, α i, x i] [],
  rw ["[", expr nhds_pi, ",", expr pi_def, "]"] ["at", ident hs],
  obtain ["⟨", ident t, ":", expr ι → set (∀
    i, α i), ",", ident ht, ":", expr ∀
   i, «expr ∈ »(t i, comap (p i) (expr𝓝() (a i))), ",", ident ht', ":", expr «expr = »(«expr⋂ , »((i «expr ∈ » I), «expr ⁻¹' »(p i, s i)), «expr⋂ , »((i : ι), t i)), "⟩", ":=", expr exists_Inter_of_mem_infi hs],
  simp [] [] ["only"] ["[", expr exists_prop, ",", expr mem_comap, "]"] [] ["at", ident ht],
  choose [] [ident v] [ident hv, ident hv'] ["using", expr ht],
  apply [expr mem_of_superset (hv i)],
  have [] [] [":=", expr calc
     «expr ⊆ »(«expr⋂ , »((i), «expr ⁻¹' »(p i, v i)), «expr⋂ , »((i), t i)) : Inter_subset_Inter hv'
     «expr = »(..., «expr⋂ , »((i «expr ∈ » I), «expr ⁻¹' »(p i, s i))) : by simp_rw [expr ht'] []
     «expr ⊆ »(..., «expr ⁻¹' »(p i, s i)) : bInter_subset_of_mem hi],
  rwa ["[", "<-", expr image_subset_iff, ",", expr image_projection_prod, "]"] ["at", ident this],
  use [expr a],
  rw ["[", expr mem_univ_pi, "]"] [],
  exact [expr λ j, mem_of_mem_nhds (hv j)]
end

theorem set_pi_mem_nhds [∀ a, TopologicalSpace (π a)] {i : Set ι} {s : ∀ a, Set (π a)} {x : ∀ a, π a} (hi : finite i)
  (hs : ∀ a _ : a ∈ i, s a ∈ 𝓝 (x a)) : pi i s ∈ 𝓝 x :=
  by 
    rw [pi_def, bInter_mem hi]
    exact fun a ha => (continuous_apply a).ContinuousAt (hs a ha)

theorem set_pi_mem_nhds_iff [Fintype ι] {α : ι → Type _} [∀ i : ι, TopologicalSpace (α i)] {I : Set ι}
  {s : ∀ i, Set (α i)} (a : ∀ i, α i) : I.pi s ∈ 𝓝 a ↔ ∀ i : ι, i ∈ I → s i ∈ 𝓝 (a i) :=
  ⟨by 
      apply mem_nhds_pi,
    set_pi_mem_nhds$ finite.of_fintype I⟩

theorem interior_pi_set [Fintype ι] {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {I : Set ι} {s : ∀ i, Set (α i)} :
  Interior (pi I s) = I.pi fun i => Interior (s i) :=
  by 
    ext a 
    simp only [mem_pi, mem_interior_iff_mem_nhds, set_pi_mem_nhds_iff]

theorem exists_finset_piecewise_mem_of_mem_nhds [DecidableEq ι] [∀ i, TopologicalSpace (π i)] {s : Set (∀ a, π a)}
  {x : ∀ a, π a} (hs : s ∈ 𝓝 x) (y : ∀ a, π a) : ∃ I : Finset ι, I.piecewise x y ∈ s :=
  by 
    simp only [nhds_pi, mem_infi', mem_comap] at hs 
    rcases hs with ⟨I, hI, V, hV, hV_univ, rfl, -⟩
    choose t ht htV using hV 
    refine' ⟨hI.to_finset, mem_bInter$ fun i hi => htV i _⟩
    simpa [hI.mem_to_finset.2 hi] using mem_of_mem_nhds (ht i)

theorem pi_eq_generate_from [∀ a, TopologicalSpace (π a)] :
  Pi.topologicalSpace =
    generate_from { g | ∃ (s : ∀ a, Set (π a))(i : Finset ι), (∀ a _ : a ∈ i, IsOpen (s a)) ∧ g = pi («expr↑ » i) s } :=
  le_antisymmₓ (le_generate_from$ fun g ⟨s, i, hi, Eq⟩ => Eq.symm ▸ is_open_set_pi (Finset.finite_to_set _) hi)
    (le_infi$
      fun a s ⟨t, ht, s_eq⟩ =>
        generate_open.basic _$
          ⟨Function.update (fun a => univ) a t, {a},
            by 
              simpa using ht,
            by 
              ext f <;> simp [s_eq.symm, pi]⟩)

theorem pi_generate_from_eq {g : ∀ a, Set (Set (π a))} :
  (@Pi.topologicalSpace ι π fun a => generate_from (g a)) =
    generate_from { t | ∃ (s : ∀ a, Set (π a))(i : Finset ι), (∀ a _ : a ∈ i, s a ∈ g a) ∧ t = pi («expr↑ » i) s } :=
  let G := { t | ∃ (s : ∀ a, Set (π a))(i : Finset ι), (∀ a _ : a ∈ i, s a ∈ g a) ∧ t = pi («expr↑ » i) s }
  by 
    rw [pi_eq_generate_from]
    refine' le_antisymmₓ (generate_from_mono _) (le_generate_from _)
    exact fun s ⟨t, i, ht, Eq⟩ => ⟨t, i, fun a ha => generate_open.basic _ (ht a ha), Eq⟩
    ·
      rintro s ⟨t, i, hi, rfl⟩
      rw [pi_def]
      apply is_open_bInter (Finset.finite_to_set _)
      intro a ha 
      show ((generate_from G).coinduced fun f : ∀ a, π a => f a).IsOpen (t a)
      refine' le_generate_from _ _ (hi a ha)
      exact
        fun s hs =>
          generate_open.basic _
            ⟨Function.update (fun a => univ) a s, {a},
              by 
                simp [hs]⟩

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pi_generate_from_eq_fintype
{g : ∀ a, set (set (π a))}
[fintype ι]
(hg : ∀
 a, «expr = »(«expr⋃₀ »(g a), univ)) : «expr = »(@Pi.topological_space ι π (λ
  a, generate_from (g a)), generate_from {t | «expr∃ , »((s : ∀
   a, set (π a)), «expr ∧ »(∀ a, «expr ∈ »(s a, g a), «expr = »(t, pi univ s)))}) :=
begin
  rw ["[", expr pi_generate_from_eq, "]"] [],
  refine [expr le_antisymm (generate_from_mono _) (le_generate_from _)],
  exact [expr assume (s) ⟨t, ht, eq⟩, ⟨t, finset.univ, by simp [] [] [] ["[", expr ht, ",", expr eq, "]"] [] []⟩],
  { rintros [ident s, "⟨", ident t, ",", ident i, ",", ident ht, ",", ident rfl, "⟩"],
    apply [expr is_open_iff_forall_mem_open.2 _],
    assume [binders (f hf)],
    choose [] [ident c] [ident hc] ["using", expr show ∀
     a, «expr∃ , »((s), «expr ∧ »(«expr ∈ »(s, g a), «expr ∈ »(f a, s))), { assume [binders (a)],
       have [] [":", expr «expr ∈ »(f a, «expr⋃₀ »(g a))] [],
       { rw ["[", expr hg, "]"] [],
         apply [expr mem_univ] },
       simpa [] [] [] [] [] [] }],
    refine [expr ⟨pi univ (λ a, if «expr ∈ »(a, i) then t a else (c : ∀ a, set (π a)) a), _, _, _⟩],
    { simp [] [] [] ["[", expr pi_if, "]"] [] [] },
    { refine [expr generate_open.basic _ ⟨_, assume a, _, rfl⟩],
      by_cases [expr «expr ∈ »(a, i)]; simp [] [] [] ["[", "*", ",", expr pi, "]"] [] ["at", "*"] },
    { have [] [":", expr «expr ∈ »(f, pi {a | «expr ∉ »(a, i)} c)] [],
      { simp [] [] [] ["[", "*", ",", expr pi, "]"] [] ["at", "*"] },
      simpa [] [] [] ["[", expr pi_if, ",", expr hf, "]"] [] [] } }
end

/-- Suppose `π i` is a family of topological spaces indexed by `i : ι`, and `X` is a type
endowed with a family of maps `f i : X → π i` for every `i : ι`, hence inducing a
map `g : X → Π i, π i`. This lemma shows that infimum of the topologies on `X` induced by
the `f i` as `i : ι` varies is simply the topology on `X` induced by `g : X → Π i, π i`
where `Π i, π i` is endowed with the usual product topology. -/
theorem inducing_infi_to_pi {X : Type _} [∀ i, TopologicalSpace (π i)] (f : ∀ i, X → π i) :
  @Inducing X (∀ i, π i) (⨅i, induced (f i) inferInstance) _ fun x i => f i x :=
  by 
    constructor 
    erw [induced_infi]
    congr 1
    funext 
    erw [induced_compose]

variable[Fintype ι][∀ i, TopologicalSpace (π i)][∀ i, DiscreteTopology (π i)]

/-- A finite product of discrete spaces is discrete. -/
instance Pi.discrete_topology : DiscreteTopology (∀ i, π i) :=
  singletons_open_iff_discrete.mp
    fun x =>
      by 
        rw
          [show {x} = ⋂i, { y:∀ i, π i | y i = x i }by 
            ext 
            simp only [Function.funext_iffₓ, Set.mem_singleton_iff, Set.mem_Inter, Set.mem_set_of_eq]]
        exact is_open_Inter fun i => (continuous_apply i).is_open_preimage {x i} (is_open_discrete {x i})

end Pi

section Sigma

variable{ι : Type _}{σ : ι → Type _}[∀ i, TopologicalSpace (σ i)]

@[continuity]
theorem continuous_sigma_mk {i : ι} : Continuous (@Sigma.mk ι σ i) :=
  continuous_supr_rng continuous_coinduced_rng

theorem is_open_sigma_iff {s : Set (Sigma σ)} : IsOpen s ↔ ∀ i, IsOpen (Sigma.mk i ⁻¹' s) :=
  by 
    simp only [is_open_supr_iff, is_open_coinduced]

theorem is_closed_sigma_iff {s : Set (Sigma σ)} : IsClosed s ↔ ∀ i, IsClosed (Sigma.mk i ⁻¹' s) :=
  by 
    simp [←is_open_compl_iff, is_open_sigma_iff]

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_open_map_sigma_mk {i : ι} : is_open_map (@sigma.mk ι σ i) :=
begin
  intros [ident s, ident hs],
  rw [expr is_open_sigma_iff] [],
  intro [ident j],
  classical,
  by_cases [expr h, ":", expr «expr = »(i, j)],
  { subst [expr j],
    convert [] [expr hs] [],
    exact [expr set.preimage_image_eq _ sigma_mk_injective] },
  { convert [] [expr is_open_empty] [],
    apply [expr set.eq_empty_of_subset_empty],
    rintro [ident x, "⟨", ident y, ",", "_", ",", ident hy, "⟩"],
    have [] [":", expr «expr = »(i, j)] [],
    by cc,
    contradiction }
end

theorem is_open_range_sigma_mk {i : ι} : IsOpen (Set.Range (@Sigma.mk ι σ i)) :=
  by 
    rw [←Set.image_univ]
    exact is_open_map_sigma_mk _ is_open_univ

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_closed_map_sigma_mk {i : ι} : is_closed_map (@sigma.mk ι σ i) :=
begin
  intros [ident s, ident hs],
  rw [expr is_closed_sigma_iff] [],
  intro [ident j],
  classical,
  by_cases [expr h, ":", expr «expr = »(i, j)],
  { subst [expr j],
    convert [] [expr hs] [],
    exact [expr set.preimage_image_eq _ sigma_mk_injective] },
  { convert [] [expr is_closed_empty] [],
    apply [expr set.eq_empty_of_subset_empty],
    rintro [ident x, "⟨", ident y, ",", "_", ",", ident hy, "⟩"],
    have [] [":", expr «expr = »(i, j)] [],
    by cc,
    contradiction }
end

theorem is_closed_sigma_mk {i : ι} : IsClosed (Set.Range (@Sigma.mk ι σ i)) :=
  by 
    rw [←Set.image_univ]
    exact is_closed_map_sigma_mk _ is_closed_univ

theorem open_embedding_sigma_mk {i : ι} : OpenEmbedding (@Sigma.mk ι σ i) :=
  open_embedding_of_continuous_injective_open continuous_sigma_mk sigma_mk_injective is_open_map_sigma_mk

theorem closed_embedding_sigma_mk {i : ι} : ClosedEmbedding (@Sigma.mk ι σ i) :=
  closed_embedding_of_continuous_injective_closed continuous_sigma_mk sigma_mk_injective is_closed_map_sigma_mk

theorem embedding_sigma_mk {i : ι} : Embedding (@Sigma.mk ι σ i) :=
  closed_embedding_sigma_mk.1

/-- A map out of a sum type is continuous if its restriction to each summand is. -/
@[continuity]
theorem continuous_sigma [TopologicalSpace β] {f : Sigma σ → β} (h : ∀ i, Continuous fun a => f ⟨i, a⟩) :
  Continuous f :=
  continuous_supr_dom fun i => continuous_coinduced_dom (h i)

@[continuity]
theorem continuous_sigma_map {κ : Type _} {τ : κ → Type _} [∀ k, TopologicalSpace (τ k)] {f₁ : ι → κ}
  {f₂ : ∀ i, σ i → τ (f₁ i)} (hf : ∀ i, Continuous (f₂ i)) : Continuous (Sigma.map f₁ f₂) :=
  continuous_sigma$ fun i => show Continuous fun a => Sigma.mk (f₁ i) (f₂ i a) from continuous_sigma_mk.comp (hf i)

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_open_map_sigma
[topological_space β]
{f : sigma σ → β}
(h : ∀ i, is_open_map (λ a, f ⟨i, a⟩)) : is_open_map f :=
begin
  intros [ident s, ident hs],
  rw [expr is_open_sigma_iff] ["at", ident hs],
  have [] [":", expr «expr = »(s, «expr⋃ , »((i), «expr '' »(sigma.mk i, «expr ⁻¹' »(sigma.mk i, s))))] [],
  { rw [expr Union_image_preimage_sigma_mk_eq_self] [] },
  rw [expr this] [],
  rw ["[", expr image_Union, "]"] [],
  apply [expr is_open_Union],
  intro [ident i],
  rw ["[", expr image_image, "]"] [],
  exact [expr h i _ (hs i)]
end

-- error in Topology.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The sum of embeddings is an embedding. -/
theorem embedding_sigma_map
{τ : ι → Type*}
[∀ i, topological_space (τ i)]
{f : ∀ i, σ i → τ i}
(hf : ∀ i, embedding (f i)) : embedding (sigma.map id f) :=
begin
  refine [expr ⟨⟨_⟩, function.injective_id.sigma_map (λ i, (hf i).inj)⟩],
  refine [expr le_antisymm (continuous_iff_le_induced.mp (continuous_sigma_map (λ i, (hf i).continuous))) _],
  intros [ident s, ident hs],
  replace [ident hs] [] [":=", expr is_open_sigma_iff.mp hs],
  have [] [":", expr ∀
   i, «expr∃ , »((t), «expr ∧ »(is_open t, «expr = »(«expr ⁻¹' »(f i, t), «expr ⁻¹' »(sigma.mk i, s))))] [],
  { intro [ident i],
    apply [expr is_open_induced_iff.mp],
    convert [] [expr hs i] [],
    exact [expr (hf i).induced.symm] },
  choose [] [ident t] [ident ht] ["using", expr this],
  apply [expr is_open_induced_iff.mpr],
  refine [expr ⟨«expr⋃ , »((i), «expr '' »(sigma.mk i, t i)), is_open_Union (λ i, is_open_map_sigma_mk _ (ht i).1), _⟩],
  ext [] ["⟨", ident i, ",", ident x, "⟩"] [],
  change [expr «expr ↔ »(«expr ∈ »(sigma.mk i (f i x), «expr⋃ , »((i : ι), «expr '' »(sigma.mk i, t i))), «expr ∈ »(x, «expr ⁻¹' »(sigma.mk i, s)))] [] [],
  rw ["[", "<-", expr (ht i).2, ",", expr mem_Union, "]"] [],
  split,
  { rintro ["⟨", ident j, ",", ident hj, "⟩"],
    rw [expr mem_image] ["at", ident hj],
    rcases [expr hj, "with", "⟨", ident y, ",", ident hy₁, ",", ident hy₂, "⟩"],
    rcases [expr sigma.mk.inj_iff.mp hy₂, "with", "⟨", ident rfl, ",", ident hy, "⟩"],
    replace [ident hy] [] [":=", expr eq_of_heq hy],
    subst [expr y],
    exact [expr hy₁] },
  { intro [ident hx],
    use [expr i],
    rw [expr mem_image] [],
    exact [expr ⟨f i x, hx, rfl⟩] }
end

end Sigma

section Ulift

@[continuity]
theorem continuous_ulift_down [TopologicalSpace α] : Continuous (Ulift.down : Ulift.{v, u} α → α) :=
  continuous_induced_dom

@[continuity]
theorem continuous_ulift_up [TopologicalSpace α] : Continuous (Ulift.up : α → Ulift.{v, u} α) :=
  continuous_induced_rng continuous_id

end Ulift

theorem mem_closure_of_continuous [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {a : α} {s : Set α} {t : Set β}
  (hf : Continuous f) (ha : a ∈ Closure s) (h : maps_to f s (Closure t)) : f a ∈ Closure t :=
  calc f a ∈ f '' Closure s := mem_image_of_mem _ ha 
    _ ⊆ Closure (f '' s) := image_closure_subset_closure_image hf 
    _ ⊆ Closure t := closure_minimal h.image_subset is_closed_closure
    

theorem mem_closure_of_continuous2 [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] {f : α → β → γ}
  {a : α} {b : β} {s : Set α} {t : Set β} {u : Set γ} (hf : Continuous fun p : α × β => f p.1 p.2) (ha : a ∈ Closure s)
  (hb : b ∈ Closure t) (h : ∀ a _ : a ∈ s, ∀ b _ : b ∈ t, f a b ∈ Closure u) : f a b ∈ Closure u :=
  have  : (a, b) ∈ Closure (Set.Prod s t) :=
    by 
      simp [closure_prod_eq, ha, hb]
  show f (a, b).1 (a, b).2 ∈ Closure u from
    @mem_closure_of_continuous (α × β) _ _ _ (fun p : α × β => f p.1 p.2) (a, b) _ u hf this$
      fun ⟨p₁, p₂⟩ ⟨h₁, h₂⟩ => h p₁ h₁ p₂ h₂

