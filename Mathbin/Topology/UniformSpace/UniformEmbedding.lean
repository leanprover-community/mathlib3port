import Mathbin.Topology.UniformSpace.Cauchy 
import Mathbin.Topology.UniformSpace.Separation 
import Mathbin.Topology.DenseEmbedding

/-!
# Uniform embeddings of uniform spaces.

Extension of uniform continuous functions.
-/


open Filter TopologicalSpace Set Classical

open_locale Classical uniformity TopologicalSpace Filter

section 

variable{α : Type _}{β : Type _}{γ : Type _}[UniformSpace α][UniformSpace β][UniformSpace γ]

universe u

-- error in Topology.UniformSpace.UniformEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A map `f : α → β` between uniform spaces is called *uniform inducing* if the uniformity filter
on `α` is the pullback of the uniformity filter on `β` under `prod.map f f`. If `α` is a separated
space, then this implies that `f` is injective, hence it is a `uniform_embedding`. -/
structure uniform_inducing
(f : α → β) : exprProp() :=
  (comap_uniformity : «expr = »(comap (λ x : «expr × »(α, α), (f x.1, f x.2)) (expr𝓤() β), expr𝓤() α))

theorem UniformInducing.mk' {f : α → β}
  (h : ∀ s, s ∈ 𝓤 α ↔ ∃ (t : _)(_ : t ∈ 𝓤 β), ∀ (x y : α), (f x, f y) ∈ t → (x, y) ∈ s) : UniformInducing f :=
  ⟨by 
      simp [eq_comm, Filter.ext_iff, subset_def, h]⟩

-- error in Topology.UniformSpace.UniformEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem uniform_inducing.comp
{g : β → γ}
(hg : uniform_inducing g)
{f : α → β}
(hf : uniform_inducing f) : uniform_inducing «expr ∘ »(g, f) :=
⟨by rw ["[", expr show «expr = »(λ
   x : «expr × »(α, α), («expr ∘ »(g, f) x.1, «expr ∘ »(g, f) x.2), «expr ∘ »(λ
    y : «expr × »(β, β), (g y.1, g y.2), λ
    x : «expr × »(α, α), (f x.1, f x.2))), by ext [] [] []; simp [] [] [] [] [] [], ",", "<-", expr filter.comap_comap, ",", expr hg.1, ",", expr hf.1, "]"] []⟩

theorem UniformInducing.basis_uniformity {f : α → β} (hf : UniformInducing f) {ι : Sort _} {p : ι → Prop}
  {s : ι → Set (β × β)} (H : (𝓤 β).HasBasis p s) : (𝓤 α).HasBasis p fun i => Prod.mapₓ f f ⁻¹' s i :=
  hf.1 ▸ H.comap _

/-- A map `f : α → β` between uniform spaces is a *uniform embedding* if it is uniform inducing and
injective. If `α` is a separated space, then the latter assumption follows from the former. -/
structure UniformEmbedding(f : α → β) extends UniformInducing f : Prop where 
  inj : Function.Injective f

theorem uniform_embedding_subtype_val {p : α → Prop} : UniformEmbedding (Subtype.val : Subtype p → α) :=
  { comap_uniformity := rfl, inj := Subtype.val_injective }

theorem uniform_embedding_subtype_coe {p : α → Prop} : UniformEmbedding (coeₓ : Subtype p → α) :=
  uniform_embedding_subtype_val

theorem uniform_embedding_set_inclusion {s t : Set α} (hst : s ⊆ t) : UniformEmbedding (inclusion hst) :=
  { comap_uniformity :=
      by 
        erw [uniformity_subtype, uniformity_subtype, comap_comap]
        congr,
    inj := inclusion_injective hst }

theorem UniformEmbedding.comp {g : β → γ} (hg : UniformEmbedding g) {f : α → β} (hf : UniformEmbedding f) :
  UniformEmbedding (g ∘ f) :=
  { hg.to_uniform_inducing.comp hf.to_uniform_inducing with inj := hg.inj.comp hf.inj }

theorem uniform_embedding_def {f : α → β} :
  UniformEmbedding f ↔
    Function.Injective f ∧ ∀ s, s ∈ 𝓤 α ↔ ∃ (t : _)(_ : t ∈ 𝓤 β), ∀ (x y : α), (f x, f y) ∈ t → (x, y) ∈ s :=
  by 
    split 
    ·
      rintro ⟨⟨h⟩, h'⟩
      rw [eq_comm, Filter.ext_iff] at h 
      simp [subset_def]
    ·
      rintro ⟨h, h'⟩
      refine' UniformEmbedding.mk ⟨_⟩ h 
      rw [eq_comm, Filter.ext_iff]
      simp [subset_def]

theorem uniform_embedding_def' {f : α → β} :
  UniformEmbedding f ↔
    Function.Injective f ∧
      UniformContinuous f ∧ ∀ s, s ∈ 𝓤 α → ∃ (t : _)(_ : t ∈ 𝓤 β), ∀ (x y : α), (f x, f y) ∈ t → (x, y) ∈ s :=
  by 
    simp only [uniform_embedding_def, uniform_continuous_def] <;>
      exact
        ⟨fun ⟨I, H⟩ => ⟨I, fun s su => (H _).2 ⟨s, su, fun x y => id⟩, fun s => (H s).1⟩,
          fun ⟨I, H₁, H₂⟩ => ⟨I, fun s => ⟨H₂ s, fun ⟨t, tu, h⟩ => mem_of_superset (H₁ t tu) fun ⟨a, b⟩ => h a b⟩⟩⟩

/-- If the domain of a `uniform_inducing` map `f` is a `separated_space`, then `f` is injective,
hence it is a `uniform_embedding`. -/
protected theorem UniformInducing.uniform_embedding [SeparatedSpace α] {f : α → β} (hf : UniformInducing f) :
  UniformEmbedding f :=
  ⟨hf,
    fun x y h =>
      eq_of_uniformity_basis (hf.basis_uniformity (𝓤 β).basis_sets)$
        fun s hs => mem_preimage.2$ mem_uniformity_of_eq hs h⟩

/-- If a map `f : α → β` sends any two distinct points to point that are **not** related by a fixed
`s ∈ 𝓤 β`, then `f` is uniform inducing with respect to the discrete uniformity on `α`:
the preimage of `𝓤 β` under `prod.map f f` is the principal filter generated by the diagonal in
`α × α`. -/
theorem comap_uniformity_of_spaced_out {α} {f : α → β} {s : Set (β × β)} (hs : s ∈ 𝓤 β)
  (hf : Pairwise fun x y => (f x, f y) ∉ s) : comap (Prod.mapₓ f f) (𝓤 β) = 𝓟 IdRel :=
  by 
    refine' le_antisymmₓ _ (@refl_le_uniformity α (UniformSpace.comap f ‹_›))
    calc comap (Prod.mapₓ f f) (𝓤 β) ≤ comap (Prod.mapₓ f f) (𝓟 s) :=
      comap_mono (le_principal_iff.2 hs)_ = 𝓟 (Prod.mapₓ f f ⁻¹' s) := comap_principal _ ≤ 𝓟 IdRel :=
      principal_mono.2 _ 
    rintro ⟨x, y⟩
    simpa [not_imp_not] using hf x y

-- error in Topology.UniformSpace.UniformEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a map `f : α → β` sends any two distinct points to point that are **not** related by a fixed
`s ∈ 𝓤 β`, then `f` is a uniform embedding with respect to the discrete uniformity on `α`. -/
theorem uniform_embedding_of_spaced_out
{α}
{f : α → β}
{s : set «expr × »(β, β)}
(hs : «expr ∈ »(s, expr𝓤() β))
(hf : pairwise (λ x y, «expr ∉ »((f x, f y), s))) : @uniform_embedding α β «expr⊥»() «expr‹ ›»(_) f :=
begin
  letI [] [":", expr uniform_space α] [":=", expr «expr⊥»()],
  haveI [] [":", expr separated_space α] [":=", expr separated_iff_t2.2 infer_instance],
  exact [expr uniform_inducing.uniform_embedding ⟨comap_uniformity_of_spaced_out hs hf⟩]
end

theorem UniformInducing.uniform_continuous {f : α → β} (hf : UniformInducing f) : UniformContinuous f :=
  by 
    simp [UniformContinuous, hf.comap_uniformity.symm, tendsto_comap]

theorem UniformInducing.uniform_continuous_iff {f : α → β} {g : β → γ} (hg : UniformInducing g) :
  UniformContinuous f ↔ UniformContinuous (g ∘ f) :=
  by 
    dsimp only [UniformContinuous, tendsto]
    rw [←hg.comap_uniformity, ←map_le_iff_le_comap, Filter.map_map]

theorem UniformInducing.inducing {f : α → β} (h : UniformInducing f) : Inducing f :=
  by 
    refine' ⟨eq_of_nhds_eq_nhds$ fun a => _⟩
    rw [nhds_induced, nhds_eq_uniformity, nhds_eq_uniformity, ←h.comap_uniformity, comap_lift'_eq, comap_lift'_eq2] <;>
      ·
        first |
          rfl|
          exact monotone_preimage

-- error in Topology.UniformSpace.UniformEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem uniform_inducing.prod
{α' : Type*}
{β' : Type*}
[uniform_space α']
[uniform_space β']
{e₁ : α → α'}
{e₂ : β → β'}
(h₁ : uniform_inducing e₁)
(h₂ : uniform_inducing e₂) : uniform_inducing (λ p : «expr × »(α, β), (e₁ p.1, e₂ p.2)) :=
⟨by simp [] [] [] ["[", expr («expr ∘ »), ",", expr uniformity_prod, ",", expr h₁.comap_uniformity.symm, ",", expr h₂.comap_uniformity.symm, ",", expr comap_inf, ",", expr comap_comap, "]"] [] []⟩

theorem UniformInducing.dense_inducing {f : α → β} (h : UniformInducing f) (hd : DenseRange f) : DenseInducing f :=
  { dense := hd, induced := h.inducing.induced }

theorem UniformEmbedding.embedding {f : α → β} (h : UniformEmbedding f) : Embedding f :=
  { induced := h.to_uniform_inducing.inducing.induced, inj := h.inj }

theorem UniformEmbedding.dense_embedding {f : α → β} (h : UniformEmbedding f) (hd : DenseRange f) : DenseEmbedding f :=
  { dense := hd, inj := h.inj, induced := h.embedding.induced }

-- error in Topology.UniformSpace.UniformEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem closed_embedding_of_spaced_out
{α}
[topological_space α]
[discrete_topology α]
[separated_space β]
{f : α → β}
{s : set «expr × »(β, β)}
(hs : «expr ∈ »(s, expr𝓤() β))
(hf : pairwise (λ x y, «expr ∉ »((f x, f y), s))) : closed_embedding f :=
begin
  unfreezingI { rcases [expr discrete_topology.eq_bot α, "with", ident rfl] },
  letI [] [":", expr uniform_space α] [":=", expr «expr⊥»()],
  exact [expr { closed_range := is_closed_range_of_spaced_out hs hf,
     ..(uniform_embedding_of_spaced_out hs hf).embedding }]
end

-- error in Topology.UniformSpace.UniformEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem closure_image_mem_nhds_of_uniform_inducing
{s : set «expr × »(α, α)}
{e : α → β}
(b : β)
(he₁ : uniform_inducing e)
(he₂ : dense_inducing e)
(hs : «expr ∈ »(s, expr𝓤() α)) : «expr∃ , »((a), «expr ∈ »(closure «expr '' »(e, {a' | «expr ∈ »((a, a'), s)}), expr𝓝() b)) :=
have «expr ∈ »(s, comap (λ
  p : «expr × »(α, α), (e p.1, e p.2)) (expr𝓤() β)), from «expr ▸ »(he₁.comap_uniformity.symm, hs),
let ⟨t₁, ht₁u, ht₁⟩ := this in
have ht₁ : ∀ p : «expr × »(α, α), «expr ∈ »((e p.1, e p.2), t₁) → «expr ∈ »(p, s), from ht₁,
let ⟨t₂, ht₂u, ht₂s, ht₂c⟩ := comp_symm_of_uniformity ht₁u in
let ⟨t, htu, hts, htc⟩ := comp_symm_of_uniformity ht₂u in
have «expr ∈ »(preimage e {b' | «expr ∈ »((b, b'), t₂)}, comap e (expr𝓝() b)), from «expr $ »(preimage_mem_comap, mem_nhds_left b ht₂u),
let ⟨a, (ha : «expr ∈ »((b, e a), t₂))⟩ := (he₂.comap_nhds_ne_bot _).nonempty_of_mem this in
have ∀
(b')
(s' : set «expr × »(β, β)), «expr ∈ »((b, b'), t) → «expr ∈ »(s', expr𝓤() β) → «expr ∩ »({y : β | «expr ∈ »((b', y), s')}, «expr '' »(e, {a' : α | «expr ∈ »((a, a'), s)})).nonempty, from assume
b'
s'
hb'
hs', have «expr ∈ »(preimage e {b'' | «expr ∈ »((b', b''), «expr ∩ »(s', t))}, comap e (expr𝓝() b')), from «expr $ »(preimage_mem_comap, «expr $ »(mem_nhds_left b', inter_mem hs' htu)),
let ⟨a₂, ha₂s', ha₂t⟩ := (he₂.comap_nhds_ne_bot _).nonempty_of_mem this in
have «expr ∈ »((e a, e a₂), t₁), from «expr $ »(ht₂c, «expr $ »(prod_mk_mem_comp_rel (ht₂s ha), «expr $ »(htc, prod_mk_mem_comp_rel hb' ha₂t))),
have «expr ∈ »(e a₂, «expr ∩ »({b'' : β | «expr ∈ »((b', b''), s')}, «expr '' »(e, {a' | «expr ∈ »((a, a'), s)}))), from ⟨ha₂s', «expr $ »(mem_image_of_mem _, ht₁ (a, a₂) this)⟩,
⟨_, this⟩,
have ∀
b', «expr ∈ »((b, b'), t) → ne_bot «expr ⊓ »(expr𝓝() b', expr𝓟() «expr '' »(e, {a' | «expr ∈ »((a, a'), s)})), begin
  intros [ident b', ident hb'],
  rw ["[", expr nhds_eq_uniformity, ",", expr lift'_inf_principal_eq, ",", expr lift'_ne_bot_iff, "]"] [],
  exact [expr assume s, this b' s hb'],
  exact [expr monotone_inter monotone_preimage monotone_const]
end,
have ∀
b', «expr ∈ »((b, b'), t) → «expr ∈ »(b', closure «expr '' »(e, {a' | «expr ∈ »((a, a'), s)})), from assume
b' hb', by rw ["[", expr closure_eq_cluster_pts, "]"] []; exact [expr this b' hb'],
⟨a, (expr𝓝() b).sets_of_superset (mem_nhds_left b htu) this⟩

theorem uniform_embedding_subtype_emb (p : α → Prop) {e : α → β} (ue : UniformEmbedding e) (de : DenseEmbedding e) :
  UniformEmbedding (DenseEmbedding.subtypeEmb p e) :=
  { comap_uniformity :=
      by 
        simp [comap_comap, · ∘ ·, DenseEmbedding.subtypeEmb, uniformity_subtype, ue.comap_uniformity.symm],
    inj := (de.subtype p).inj }

-- error in Topology.UniformSpace.UniformEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem uniform_embedding.prod
{α' : Type*}
{β' : Type*}
[uniform_space α']
[uniform_space β']
{e₁ : α → α'}
{e₂ : β → β'}
(h₁ : uniform_embedding e₁)
(h₂ : uniform_embedding e₂) : uniform_embedding (λ p : «expr × »(α, β), (e₁ p.1, e₂ p.2)) :=
{ inj := h₁.inj.prod_map h₂.inj, ..h₁.to_uniform_inducing.prod h₂.to_uniform_inducing }

theorem is_complete_of_complete_image {m : α → β} {s : Set α} (hm : UniformInducing m) (hs : IsComplete (m '' s)) :
  IsComplete s :=
  by 
    intro f hf hfs 
    rw [le_principal_iff] at hfs 
    obtain ⟨_, ⟨x, hx, rfl⟩, hyf⟩ : ∃ (y : _)(_ : y ∈ m '' s), map m f ≤ 𝓝 y 
    exact hs (f.map m) (hf.map hm.uniform_continuous) (le_principal_iff.2 (image_mem_map hfs))
    rw [map_le_iff_le_comap, ←nhds_induced, ←hm.inducing.induced] at hyf 
    exact ⟨x, hx, hyf⟩

theorem IsComplete.complete_space_coe {s : Set α} (hs : IsComplete s) : CompleteSpace s :=
  complete_space_iff_is_complete_univ.2$
    is_complete_of_complete_image uniform_embedding_subtype_coe.to_uniform_inducing$
      by 
        simp [hs]

-- error in Topology.UniformSpace.UniformEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A set is complete iff its image under a uniform inducing map is complete. -/
theorem is_complete_image_iff
{m : α → β}
{s : set α}
(hm : uniform_inducing m) : «expr ↔ »(is_complete «expr '' »(m, s), is_complete s) :=
begin
  refine [expr ⟨is_complete_of_complete_image hm, λ c, _⟩],
  haveI [] [":", expr complete_space s] [":=", expr c.complete_space_coe],
  set [] [ident m'] [":", expr s → β] [":="] [expr «expr ∘ »(m, coe)] [],
  suffices [] [":", expr is_complete (range m')],
  by rwa ["[", expr range_comp, ",", expr subtype.range_coe, "]"] ["at", ident this],
  have [ident hm'] [":", expr uniform_inducing m'] [":=", expr hm.comp uniform_embedding_subtype_coe.to_uniform_inducing],
  intros [ident f, ident hf, ident hfm],
  rw [expr filter.le_principal_iff] ["at", ident hfm],
  have [ident cf'] [":", expr cauchy (comap m' f)] [":=", expr hf.comap' hm'.comap_uniformity.le (ne_bot.comap_of_range_mem hf.1 hfm)],
  rcases [expr complete_space.complete cf', "with", "⟨", ident x, ",", ident hx, "⟩"],
  rw ["[", expr hm'.inducing.nhds_eq_comap, ",", expr comap_le_comap_iff hfm, "]"] ["at", ident hx],
  use ["[", expr m' x, ",", expr mem_range_self _, ",", expr hx, "]"]
end

theorem complete_space_iff_is_complete_range {f : α → β} (hf : UniformInducing f) :
  CompleteSpace α ↔ IsComplete (range f) :=
  by 
    rw [complete_space_iff_is_complete_univ, ←is_complete_image_iff hf, image_univ]

theorem UniformInducing.is_complete_range [CompleteSpace α] {f : α → β} (hf : UniformInducing f) :
  IsComplete (range f) :=
  (complete_space_iff_is_complete_range hf).1 ‹_›

theorem complete_space_congr {e : α ≃ β} (he : UniformEmbedding e) : CompleteSpace α ↔ CompleteSpace β :=
  by 
    rw [complete_space_iff_is_complete_range he.to_uniform_inducing, e.range_eq_univ,
      complete_space_iff_is_complete_univ]

theorem complete_space_coe_iff_is_complete {s : Set α} : CompleteSpace s ↔ IsComplete s :=
  (complete_space_iff_is_complete_range uniform_embedding_subtype_coe.to_uniform_inducing).trans$
    by 
      rw [Subtype.range_coe]

theorem IsClosed.complete_space_coe [CompleteSpace α] {s : Set α} (hs : IsClosed s) : CompleteSpace s :=
  hs.is_complete.complete_space_coe

-- error in Topology.UniformSpace.UniformEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem complete_space_extension
{m : β → α}
(hm : uniform_inducing m)
(dense : dense_range m)
(h : ∀ f : filter β, cauchy f → «expr∃ , »((x : α), «expr ≤ »(map m f, expr𝓝() x))) : complete_space α :=
⟨assume
 f : filter α, assume
 hf : cauchy f, let p : set «expr × »(α, α) → set α → set α := λ
     s t, {y : α | «expr∃ , »((x : α), «expr ∧ »(«expr ∈ »(x, t), «expr ∈ »((x, y), s)))},
     g := (expr𝓤() α).lift (λ s, f.lift' (p s)) in
 have mp₀ : monotone p, from assume (a b h t s) ⟨x, xs, xa⟩, ⟨x, xs, h xa⟩,
 have mp₁ : ∀ {s}, monotone (p s), from assume (s a b h x) ⟨y, ya, yxs⟩, ⟨y, h ya, yxs⟩,
 have «expr ≤ »(f, g), from «expr $ »(le_infi, assume
  s, «expr $ »(le_infi, assume
   hs, «expr $ »(le_infi, assume
    t, «expr $ »(le_infi, assume
     ht, «expr $ »(le_principal_iff.mpr, «expr $ »(mem_of_superset ht, assume
       x hx, ⟨x, hx, refl_mem_uniformity hs⟩)))))),
 have ne_bot g, from hf.left.mono this,
 have ne_bot (comap m g), from «expr $ »(comap_ne_bot, assume
  t ht, let ⟨t', ht', ht_mem⟩ := «expr $ »(mem_lift_sets, monotone_lift' monotone_const mp₀).mp ht in
  let ⟨t'', ht'', ht'_sub⟩ := (mem_lift'_sets mp₁).mp ht_mem in
  let ⟨x, (hx : «expr ∈ »(x, t''))⟩ := hf.left.nonempty_of_mem ht'' in
  have h₀ : ne_bot «expr𝓝[ ] »(range m, x), from dense.nhds_within_ne_bot x,
  have h₁ : «expr ∈ »({y | «expr ∈ »((x, y), t')}, «expr𝓝[ ] »(range m, x)), from «expr $ »(@mem_inf_of_left α (expr𝓝() x) (expr𝓟() (range m)) _, mem_nhds_left x ht'),
  have h₂ : «expr ∈ »(range m, «expr𝓝[ ] »(range m, x)), from «expr $ »(@mem_inf_of_right α (expr𝓝() x) (expr𝓟() (range m)) _, subset.refl _),
  have «expr ∈ »(«expr ∩ »({y | «expr ∈ »((x, y), t')}, range m), «expr𝓝[ ] »(range m, x)), from @inter_mem α «expr𝓝[ ] »(range m, x) _ _ h₁ h₂,
  let ⟨y, xyt', b, b_eq⟩ := h₀.nonempty_of_mem this in
  ⟨b, «expr ▸ »(b_eq.symm, ht'_sub ⟨x, hx, xyt'⟩)⟩),
 have cauchy g, from ⟨«expr‹ ›»(ne_bot g), assume
  s
  hs, let ⟨s₁, hs₁, (comp_s₁ : «expr ⊆ »(comp_rel s₁ s₁, s))⟩ := comp_mem_uniformity_sets hs,
      ⟨s₂, hs₂, (comp_s₂ : «expr ⊆ »(comp_rel s₂ s₂, s₁))⟩ := comp_mem_uniformity_sets hs₁,
      ⟨t, ht, (prod_t : «expr ⊆ »(set.prod t t, s₂))⟩ := mem_prod_same_iff.mp (hf.right hs₂) in
  have hg₁ : «expr ∈ »(p (preimage prod.swap s₁) t, g), from «expr $ »(mem_lift (symm_le_uniformity hs₁), @mem_lift' α α f _ t ht),
  have hg₂ : «expr ∈ »(p s₂ t, g), from «expr $ »(mem_lift hs₂, @mem_lift' α α f _ t ht),
  have hg : «expr ∈ »(set.prod (p (preimage prod.swap s₁) t) (p s₂ t), «expr ×ᶠ »(g, g)), from @prod_mem_prod α α _ _ g g hg₁ hg₂,
  «expr ×ᶠ »(g, g).sets_of_superset hg (assume
   ⟨a, b⟩
   ⟨⟨c₁, c₁t, hc₁⟩, ⟨c₂, c₂t, hc₂⟩⟩, have «expr ∈ »((c₁, c₂), set.prod t t), from ⟨c₁t, c₂t⟩,
   «expr $ »(comp_s₁, «expr $ »(prod_mk_mem_comp_rel hc₁, «expr $ »(comp_s₂, prod_mk_mem_comp_rel (prod_t this) hc₂))))⟩,
 have cauchy (filter.comap m g), from «expr‹ ›»(cauchy g).comap' (le_of_eq hm.comap_uniformity) «expr‹ ›»(_),
 let ⟨x, (hx : «expr ≤ »(map m (filter.comap m g), expr𝓝() x))⟩ := h _ this in
 have cluster_pt x (map m (filter.comap m g)), from (le_nhds_iff_adhp_of_cauchy (this.map hm.uniform_continuous)).mp hx,
 have cluster_pt x g, from this.mono map_comap_le,
 ⟨x, calc «expr ≤ »(f, g) : by assumption «expr ≤ »(..., expr𝓝() x) : le_nhds_of_cauchy_adhp «expr‹ ›»(cauchy g) this⟩⟩

-- error in Topology.UniformSpace.UniformEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem totally_bounded_preimage
{f : α → β}
{s : set β}
(hf : uniform_embedding f)
(hs : totally_bounded s) : totally_bounded «expr ⁻¹' »(f, s) :=
λ t ht, begin
  rw ["<-", expr hf.comap_uniformity] ["at", ident ht],
  rcases [expr mem_comap.2 ht, "with", "⟨", ident t', ",", ident ht', ",", ident ts, "⟩"],
  rcases [expr totally_bounded_iff_subset.1 (totally_bounded_subset (image_preimage_subset f s) hs) _ ht', "with", "⟨", ident c, ",", ident cs, ",", ident hfc, ",", ident hct, "⟩"],
  refine [expr ⟨«expr ⁻¹' »(f, c), hfc.preimage (hf.inj.inj_on _), λ x h, _⟩],
  have [] [] [":=", expr hct (mem_image_of_mem f h)],
  simp [] [] [] [] [] ["at", ident this, "⊢"],
  rcases [expr this, "with", "⟨", ident z, ",", ident zc, ",", ident zt, "⟩"],
  rcases [expr cs zc, "with", "⟨", ident y, ",", ident yc, ",", ident rfl, "⟩"],
  exact [expr ⟨y, zc, ts (by exact [expr zt])⟩]
end

end 

theorem uniform_embedding_comap {α : Type _} {β : Type _} {f : α → β} [u : UniformSpace β] (hf : Function.Injective f) :
  @UniformEmbedding α β (UniformSpace.comap f u) u f :=
  @UniformEmbedding.mk _ _ (UniformSpace.comap f u) _ _ (@UniformInducing.mk _ _ (UniformSpace.comap f u) _ _ rfl) hf

section UniformExtension

variable{α :
    Type
      _}{β :
    Type
      _}{γ :
    Type
      _}[UniformSpace
      α][UniformSpace
      β][UniformSpace
      γ]{e : β → α}(h_e : UniformInducing e)(h_dense : DenseRange e){f : β → γ}(h_f : UniformContinuous f)

local notation "ψ" => (h_e.dense_inducing h_dense).extend f

theorem uniformly_extend_exists [CompleteSpace γ] (a : α) : ∃ c, tendsto f (comap e (𝓝 a)) (𝓝 c) :=
  let de := h_e.dense_inducing h_dense 
  have  : Cauchy (𝓝 a) := cauchy_nhds 
  have  : Cauchy (comap e (𝓝 a)) := this.comap' (le_of_eqₓ h_e.comap_uniformity) (de.comap_nhds_ne_bot _)
  have  : Cauchy (map f (comap e (𝓝 a))) := this.map h_f 
  CompleteSpace.complete this

-- error in Topology.UniformSpace.UniformEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem uniform_extend_subtype
[complete_space γ]
{p : α → exprProp()}
{e : α → β}
{f : α → γ}
{b : β}
{s : set α}
(hf : uniform_continuous (λ x : subtype p, f x.val))
(he : uniform_embedding e)
(hd : ∀ x : β, «expr ∈ »(x, closure (range e)))
(hb : «expr ∈ »(closure «expr '' »(e, s), expr𝓝() b))
(hs : is_closed s)
(hp : ∀ x «expr ∈ » s, p x) : «expr∃ , »((c), tendsto f (comap e (expr𝓝() b)) (expr𝓝() c)) :=
have de : dense_embedding e, from he.dense_embedding hd,
have de' : dense_embedding (dense_embedding.subtype_emb p e), by exact [expr de.subtype p],
have ue' : uniform_embedding (dense_embedding.subtype_emb p e), from uniform_embedding_subtype_emb _ he de,
have «expr ∈ »(b, closure «expr '' »(e, {x | p x})), from «expr $ »(closure_mono, «expr $ »(monotone_image, hp)) (mem_of_mem_nhds hb),
let ⟨c, (hc : tendsto «expr ∘ »(f, subtype.val) (comap (dense_embedding.subtype_emb p e) (expr𝓝() ⟨b, this⟩)) (expr𝓝() c))⟩ := uniformly_extend_exists ue'.to_uniform_inducing de'.dense hf _ in
begin
  rw ["[", expr nhds_subtype_eq_comap, "]"] ["at", ident hc],
  simp [] [] [] ["[", expr comap_comap, "]"] [] ["at", ident hc],
  change [expr tendsto «expr ∘ »(f, @subtype.val α p) (comap «expr ∘ »(e, @subtype.val α p) (expr𝓝() b)) (expr𝓝() c)] [] ["at", ident hc],
  rw ["[", "<-", expr comap_comap, ",", expr tendsto_comap'_iff, "]"] ["at", ident hc],
  exact [expr ⟨c, hc⟩],
  exact [expr ⟨_, hb, assume x, begin
      change [expr «expr ∈ »(e x, closure «expr '' »(e, s)) → «expr ∈ »(x, range subtype.val)] [] [],
      rw ["[", "<-", expr closure_induced, ",", expr mem_closure_iff_cluster_pt, ",", expr cluster_pt, ",", expr ne_bot_iff, ",", expr nhds_induced, ",", "<-", expr de.to_dense_inducing.nhds_eq_comap, ",", "<-", expr mem_closure_iff_nhds_ne_bot, ",", expr hs.closure_eq, "]"] [],
      exact [expr assume hxs, ⟨⟨x, hp x hxs⟩, rfl⟩]
    end⟩]
end

variable[SeparatedSpace γ]

theorem uniformly_extend_of_ind (b : β) : ψ (e b) = f b :=
  DenseInducing.extend_eq_at _ h_f.continuous.continuous_at

theorem uniformly_extend_unique {g : α → γ} (hg : ∀ b, g (e b) = f b) (hc : Continuous g) : ψ = g :=
  DenseInducing.extend_unique _ hg hc

include h_f

theorem uniformly_extend_spec [CompleteSpace γ] (a : α) : tendsto f (comap e (𝓝 a)) (𝓝 (ψ a)) :=
  let de := h_e.dense_inducing h_dense 
  by 
    byCases' ha : a ∈ range e
    ·
      rcases ha with ⟨b, rfl⟩
      rw [uniformly_extend_of_ind _ _ h_f, ←de.nhds_eq_comap]
      exact h_f.continuous.tendsto _
    ·
      simp only [DenseInducing.extend, dif_neg ha]
      exact tendsto_nhds_lim (uniformly_extend_exists h_e h_dense h_f _)

-- error in Topology.UniformSpace.UniformEmbedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem uniform_continuous_uniformly_extend [cγ : complete_space γ] : uniform_continuous exprψ() :=
assume
d
hd, let ⟨s, hs, hs_comp⟩ := «expr $ »(mem_lift'_sets, «expr $ »(monotone_comp_rel monotone_id, monotone_comp_rel monotone_id monotone_id)).mp (comp_le_uniformity3 hd) in
have h_pnt : ∀
{a
 m}, «expr ∈ »(m, expr𝓝() a) → «expr∃ , »((c), «expr ∧ »(«expr ∈ »(c, «expr '' »(f, preimage e m)), «expr ∧ »(«expr ∈ »((c, exprψ() a), s), «expr ∈ »((exprψ() a, c), s)))), from assume
a m hm, have nb : ne_bot (map f (comap e (expr𝓝() a))), from ((h_e.dense_inducing h_dense).comap_nhds_ne_bot _).map _,
have «expr ∈ »(«expr ∩ »(«expr '' »(f, preimage e m), «expr ∩ »({c | «expr ∈ »((c, exprψ() a), s)}, {c | «expr ∈ »((exprψ() a, c), s)})), map f (comap e (expr𝓝() a))), from inter_mem «expr $ »(image_mem_map, «expr $ »(preimage_mem_comap, hm)) (uniformly_extend_spec h_e h_dense h_f _ (inter_mem (mem_nhds_right _ hs) (mem_nhds_left _ hs))),
nb.nonempty_of_mem this,
have «expr ∈ »(preimage (λ p : «expr × »(β, β), (f p.1, f p.2)) s, expr𝓤() β), from h_f hs,
have «expr ∈ »(preimage (λ
  p : «expr × »(β, β), (f p.1, f p.2)) s, comap (λ
  x : «expr × »(β, β), (e x.1, e x.2)) (expr𝓤() α)), by rwa ["[", expr h_e.comap_uniformity.symm, "]"] ["at", ident this],
let ⟨t, ht, ts⟩ := this in
show «expr ∈ »(preimage (λ
  p : «expr × »(α, α), (exprψ() p.1, exprψ() p.2)) d, expr𝓤() α), from «expr $ »((expr𝓤() α).sets_of_superset (interior_mem_uniformity ht), assume
 ⟨x₁, x₂⟩
 (hx_t), have «expr ≤ »(expr𝓝() (x₁, x₂), expr𝓟() (interior t)), from is_open_iff_nhds.mp is_open_interior (x₁, x₂) hx_t,
 have «expr ∈ »(interior t, «expr ×ᶠ »(expr𝓝() x₁, expr𝓝() x₂)), by rwa ["[", expr nhds_prod_eq, ",", expr le_principal_iff, "]"] ["at", ident this],
 let ⟨m₁, hm₁, m₂, hm₂, (hm : «expr ⊆ »(set.prod m₁ m₂, interior t))⟩ := mem_prod_iff.mp this in
 let ⟨a, ha₁, _, ha₂⟩ := h_pnt hm₁ in
 let ⟨b, hb₁, hb₂, _⟩ := h_pnt hm₂ in
 have «expr ⊆ »(set.prod (preimage e m₁) (preimage e m₂), preimage (λ p : «expr × »(β, β), (f p.1, f p.2)) s), from calc
   «expr ⊆ »(_, preimage (λ p : «expr × »(β, β), (e p.1, e p.2)) (interior t)) : preimage_mono hm
   «expr ⊆ »(..., preimage (λ p : «expr × »(β, β), (e p.1, e p.2)) t) : preimage_mono interior_subset
   «expr ⊆ »(..., preimage (λ p : «expr × »(β, β), (f p.1, f p.2)) s) : ts,
 have «expr ⊆ »(set.prod «expr '' »(f, preimage e m₁) «expr '' »(f, preimage e m₂), s), from calc
   «expr = »(set.prod «expr '' »(f, preimage e m₁) «expr '' »(f, preimage e m₂), «expr '' »(λ
     p : «expr × »(β, β), (f p.1, f p.2), set.prod (preimage e m₁) (preimage e m₂))) : prod_image_image_eq
   «expr ⊆ »(..., «expr '' »(λ
     p : «expr × »(β, β), (f p.1, f p.2), preimage (λ p : «expr × »(β, β), (f p.1, f p.2)) s)) : monotone_image this
   «expr ⊆ »(..., s) : «expr $ »(image_subset_iff.mpr, subset.refl _),
 have «expr ∈ »((a, b), s), from @this (a, b) ⟨ha₁, hb₁⟩,
 «expr $ »(hs_comp, show «expr ∈ »((exprψ() x₁, exprψ() x₂), comp_rel s (comp_rel s s)), from ⟨a, ha₂, ⟨b, this, hb₂⟩⟩))

end UniformExtension

