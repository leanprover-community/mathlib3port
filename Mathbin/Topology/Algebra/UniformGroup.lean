import Mathbin.Topology.UniformSpace.UniformEmbedding 
import Mathbin.Topology.UniformSpace.CompleteSeparated 
import Mathbin.Topology.Algebra.Group 
import Mathbin.Tactic.Abel

/-!
# Uniform structure on topological groups

* `topological_add_group.to_uniform_space` and `topological_add_group_is_uniform` can be used to
  construct a canonical uniformity for a topological add group.

* extension of ℤ-bilinear maps to complete groups (useful for ring completions)
-/


noncomputable theory

open_locale Classical uniformity TopologicalSpace Filter

section UniformAddGroup

open Filter Set

variable{α : Type _}{β : Type _}

/-- A uniform (additive) group is a group in which the addition and negation are
  uniformly continuous. -/
class UniformAddGroup(α : Type _)[UniformSpace α][AddGroupₓ α] : Prop where 
  uniform_continuous_sub : UniformContinuous fun p : α × α => p.1 - p.2

theorem UniformAddGroup.mk' {α} [UniformSpace α] [AddGroupₓ α] (h₁ : UniformContinuous fun p : α × α => p.1+p.2)
  (h₂ : UniformContinuous fun p : α => -p) : UniformAddGroup α :=
  ⟨by 
      simpa only [sub_eq_add_neg] using h₁.comp (uniform_continuous_fst.prod_mk (h₂.comp uniform_continuous_snd))⟩

variable[UniformSpace α][AddGroupₓ α][UniformAddGroup α]

theorem uniform_continuous_sub : UniformContinuous fun p : α × α => p.1 - p.2 :=
  UniformAddGroup.uniform_continuous_sub

theorem UniformContinuous.sub [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
  (hg : UniformContinuous g) : UniformContinuous fun x => f x - g x :=
  uniform_continuous_sub.comp (hf.prod_mk hg)

theorem UniformContinuous.neg [UniformSpace β] {f : β → α} (hf : UniformContinuous f) :
  UniformContinuous fun x => -f x :=
  have  : UniformContinuous fun x => 0 - f x := uniform_continuous_const.sub hf 
  by 
    simp_all 

theorem uniform_continuous_neg : UniformContinuous fun x : α => -x :=
  uniform_continuous_id.neg

theorem UniformContinuous.add [UniformSpace β] {f : β → α} {g : β → α} (hf : UniformContinuous f)
  (hg : UniformContinuous g) : UniformContinuous fun x => f x+g x :=
  have  : UniformContinuous fun x => f x - -g x := hf.sub hg.neg 
  by 
    simp_all [sub_eq_add_neg]

theorem uniform_continuous_add : UniformContinuous fun p : α × α => p.1+p.2 :=
  uniform_continuous_fst.add uniform_continuous_snd

instance (priority := 10)UniformAddGroup.to_topological_add_group : TopologicalAddGroup α :=
  { continuous_add := uniform_continuous_add.Continuous, continuous_neg := uniform_continuous_neg.Continuous }

instance  [UniformSpace β] [AddGroupₓ β] [UniformAddGroup β] : UniformAddGroup (α × β) :=
  ⟨((uniform_continuous_fst.comp uniform_continuous_fst).sub
          (uniform_continuous_fst.comp uniform_continuous_snd)).prod_mk
      ((uniform_continuous_snd.comp uniform_continuous_fst).sub (uniform_continuous_snd.comp uniform_continuous_snd))⟩

theorem uniformity_translate (a : α) : ((𝓤 α).map fun x : α × α => (x.1+a, x.2+a)) = 𝓤 α :=
  le_antisymmₓ (uniform_continuous_id.add uniform_continuous_const)
    (calc 𝓤 α = ((𝓤 α).map fun x : α × α => (x.1+-a, x.2+-a)).map fun x : α × α => (x.1+a, x.2+a) :=
      by 
        simp [Filter.map_map, · ∘ ·] <;> exact filter.map_id.symm 
      _ ≤ (𝓤 α).map fun x : α × α => (x.1+a, x.2+a) :=
      Filter.map_mono (uniform_continuous_id.add uniform_continuous_const)
      )

-- error in Topology.Algebra.UniformGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem uniform_embedding_translate (a : α) : uniform_embedding (λ x : α, «expr + »(x, a)) :=
{ comap_uniformity := begin
    rw ["[", "<-", expr uniformity_translate a, ",", expr comap_map, "]"] [] { occs := occurrences.pos «expr[ , ]»([1]) },
    rintros ["⟨", ident p₁, ",", ident p₂, "⟩", "⟨", ident q₁, ",", ident q₂, "⟩"],
    simp [] [] [] ["[", expr prod.eq_iff_fst_eq_snd_eq, "]"] [] [] { contextual := tt }
  end,
  inj := add_left_injective a }

section 

variable(α)

theorem uniformity_eq_comap_nhds_zero : 𝓤 α = comap (fun x : α × α => x.2 - x.1) (𝓝 (0 : α)) :=
  by 
    rw [nhds_eq_comap_uniformity, Filter.comap_comap]
    refine' le_antisymmₓ (Filter.map_le_iff_le_comap.1 _) _
    ·
      intro s hs 
      rcases mem_uniformity_of_uniform_continuous_invariant uniform_continuous_sub hs with ⟨t, ht, hts⟩
      refine' mem_map.2 (mem_of_superset ht _)
      rintro ⟨a, b⟩
      simpa [subset_def] using hts a b a
    ·
      intro s hs 
      rcases mem_uniformity_of_uniform_continuous_invariant uniform_continuous_add hs with ⟨t, ht, hts⟩
      refine' ⟨_, ht, _⟩
      rintro ⟨a, b⟩
      simpa [subset_def] using hts 0 (b - a) a

end 

theorem group_separation_rel (x y : α) : (x, y) ∈ SeparationRel α ↔ x - y ∈ Closure ({0} : Set α) :=
  have  : Embedding fun a => a+y - x := (uniform_embedding_translate (y - x)).Embedding 
  show (x, y) ∈ ⋂₀(𝓤 α).Sets ↔ x - y ∈ Closure ({0} : Set α)by 
    rw [this.closure_eq_preimage_closure_image, uniformity_eq_comap_nhds_zero α, sInter_comap_sets]
    simp [mem_closure_iff_nhds, inter_singleton_nonempty, sub_eq_add_neg, add_assocₓ]

-- error in Topology.Algebra.UniformGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem uniform_continuous_of_tendsto_zero
[uniform_space β]
[add_group β]
[uniform_add_group β]
{f : «expr →+ »(α, β)}
(h : tendsto f (expr𝓝() 0) (expr𝓝() 0)) : uniform_continuous f :=
begin
  have [] [":", expr «expr = »(«expr ∘ »(λ
     x : «expr × »(β, β), «expr - »(x.2, x.1), λ
     x : «expr × »(α, α), (f x.1, f x.2)), λ x : «expr × »(α, α), f «expr - »(x.2, x.1))] [],
  { simp [] [] ["only"] ["[", expr f.map_sub, "]"] [] [] },
  rw ["[", expr uniform_continuous, ",", expr uniformity_eq_comap_nhds_zero α, ",", expr uniformity_eq_comap_nhds_zero β, ",", expr tendsto_comap_iff, ",", expr this, "]"] [],
  exact [expr tendsto.comp h tendsto_comap]
end

theorem AddMonoidHom.uniform_continuous_of_continuous_at_zero [UniformSpace β] [AddGroupₓ β] [UniformAddGroup β]
  (f : α →+ β) (hf : ContinuousAt f 0) : UniformContinuous f :=
  uniform_continuous_of_tendsto_zero
    (by 
      simpa using hf.tendsto)

theorem uniform_continuous_of_continuous [UniformSpace β] [AddGroupₓ β] [UniformAddGroup β] {f : α →+ β}
  (h : Continuous f) : UniformContinuous f :=
  uniform_continuous_of_tendsto_zero$
    suffices tendsto f (𝓝 0) (𝓝 (f 0))by 
      rwa [f.map_zero] at this 
    h.tendsto 0

theorem CauchySeq.add {ι : Type _} [SemilatticeSup ι] {u v : ι → α} (hu : CauchySeq u) (hv : CauchySeq v) :
  CauchySeq (u+v) :=
  uniform_continuous_add.comp_cauchy_seq (hu.prod hv)

end UniformAddGroup

section TopologicalAddCommGroup

universe u v w x

open Filter

variable{G : Type u}[AddCommGroupₓ G][TopologicalSpace G][TopologicalAddGroup G]

variable(G)

-- error in Topology.Algebra.UniformGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The right uniformity on a topological group. -/ def topological_add_group.to_uniform_space : uniform_space G :=
{ uniformity := comap (λ p : «expr × »(G, G), «expr - »(p.2, p.1)) (expr𝓝() 0),
  refl := by refine [expr map_le_iff_le_comap.1 (le_trans _ (pure_le_nhds 0))]; simp [] [] [] ["[", expr set.subset_def, "]"] [] [] { contextual := tt },
  symm := begin
    suffices [] [":", expr tendsto «expr ∘ »(λ
      p, «expr- »(p), λ
      p : «expr × »(G, G), «expr - »(p.2, p.1)) (comap (λ
       p : «expr × »(G, G), «expr - »(p.2, p.1)) (expr𝓝() 0)) (expr𝓝() «expr- »(0))],
    { simpa [] [] [] ["[", expr («expr ∘ »), ",", expr tendsto_comap_iff, "]"] [] [] },
    exact [expr tendsto.comp (tendsto.neg tendsto_id) tendsto_comap]
  end,
  comp := begin
    intros [ident D, ident H],
    rw [expr mem_lift'_sets] [],
    { rcases [expr H, "with", "⟨", ident U, ",", ident U_nhds, ",", ident U_sub, "⟩"],
      rcases [expr exists_nhds_zero_half U_nhds, "with", "⟨", ident V, ",", "⟨", ident V_nhds, ",", ident V_sum, "⟩", "⟩"],
      existsi [expr «expr ⁻¹' »(λ p : «expr × »(G, G), «expr - »(p.2, p.1), V)],
      have [ident H] [":", expr «expr ∈ »(«expr ⁻¹' »(λ
         p : «expr × »(G, G), «expr - »(p.2, p.1), V), comap (λ
         p : «expr × »(G, G), «expr - »(p.2, p.1)) (expr𝓝() (0 : G)))] [],
      by existsi ["[", expr V, ",", expr V_nhds, "]"]; refl,
      existsi [expr H],
      have [ident comp_rel_sub] [":", expr «expr ⊆ »(comp_rel «expr ⁻¹' »(λ
         p : «expr × »(G, G), «expr - »(p.2, p.1), V) «expr ⁻¹' »(λ
         p, «expr - »(p.2, p.1), V), «expr ⁻¹' »(λ p : «expr × »(G, G), «expr - »(p.2, p.1), U))] [],
      begin
        intros [ident p, ident p_comp_rel],
        rcases [expr p_comp_rel, "with", "⟨", ident z, ",", "⟨", ident Hz1, ",", ident Hz2, "⟩", "⟩"],
        simpa [] [] [] ["[", expr sub_eq_add_neg, ",", expr add_comm, ",", expr add_left_comm, "]"] [] ["using", expr V_sum _ Hz1 _ Hz2]
      end,
      exact [expr set.subset.trans comp_rel_sub U_sub] },
    { exact [expr monotone_comp_rel monotone_id monotone_id] }
  end,
  is_open_uniformity := begin
    intro [ident S],
    let [ident S'] [] [":=", expr λ x, {p : «expr × »(G, G) | «expr = »(p.1, x) → «expr ∈ »(p.2, S)}],
    show [expr «expr ↔ »(is_open S, ∀
      x : G, «expr ∈ »(x, S) → «expr ∈ »(S' x, comap (λ p : «expr × »(G, G), «expr - »(p.2, p.1)) (expr𝓝() (0 : G))))],
    rw ["[", expr is_open_iff_mem_nhds, "]"] [],
    refine [expr forall_congr (assume a, forall_congr (assume ha, _))],
    rw ["[", "<-", expr nhds_translation_sub, ",", expr mem_comap, ",", expr mem_comap, "]"] [],
    refine [expr exists_congr (assume t, exists_congr (assume ht, _))],
    show [expr «expr ↔ »(«expr ⊆ »(«expr ⁻¹' »(λ
        y : G, «expr - »(y, a), t), S), «expr ⊆ »(«expr ⁻¹' »(λ
        p : «expr × »(G, G), «expr - »(p.snd, p.fst), t), S' a))],
    split,
    { rintros [ident h, "⟨", ident x, ",", ident y, "⟩", ident hx, ident rfl],
      exact [expr h hx] },
    { rintros [ident h, ident x, ident hx],
      exact [expr @h (a, x) hx rfl] }
  end }

section 

attribute [local instance] TopologicalAddGroup.toUniformSpace

theorem uniformity_eq_comap_nhds_zero' : 𝓤 G = comap (fun p : G × G => p.2 - p.1) (𝓝 (0 : G)) :=
  rfl

variable{G}

theorem topological_add_group_is_uniform : UniformAddGroup G :=
  have  :
    tendsto ((fun p : G × G => p.1 - p.2) ∘ fun p : (G × G) × G × G => (p.1.2 - p.1.1, p.2.2 - p.2.1))
      (comap (fun p : (G × G) × G × G => (p.1.2 - p.1.1, p.2.2 - p.2.1)) ((𝓝 0).Prod (𝓝 0))) (𝓝 (0 - 0)) :=
    (tendsto_fst.sub tendsto_snd).comp tendsto_comap 
  by 
    constructor 
    rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff, uniformity_eq_comap_nhds_zero' G,
      tendsto_comap_iff, prod_comap_comap_eq]
    simpa [· ∘ ·, sub_eq_add_neg, add_commₓ, add_left_commₓ] using this

attribute [local instance] topological_add_group_is_uniform

open Set

-- error in Topology.Algebra.UniformGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem topological_add_group.separated_iff_zero_closed : «expr ↔ »(separated_space G, is_closed ({0} : set G)) :=
begin
  rw ["[", expr separated_space_iff, ",", "<-", expr closure_eq_iff_is_closed, "]"] [],
  split; intro [ident h],
  { apply [expr subset.antisymm],
    { intros [ident x, ident x_in],
      have [] [] [":=", expr group_separation_rel x 0],
      rw [expr sub_zero] ["at", ident this],
      rw ["[", "<-", expr this, ",", expr h, "]"] ["at", ident x_in],
      change [expr «expr = »(x, 0)] [] ["at", ident x_in],
      simp [] [] [] ["[", expr x_in, "]"] [] [] },
    { exact [expr subset_closure] } },
  { ext [] [ident p] [],
    cases [expr p] ["with", ident x, ident y],
    rw ["[", expr group_separation_rel x, ",", expr h, ",", expr mem_singleton_iff, ",", expr sub_eq_zero, "]"] [],
    refl }
end

-- error in Topology.Algebra.UniformGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem topological_add_group.separated_of_zero_sep
(H : ∀ x : G, «expr ≠ »(x, 0) → «expr∃ , »((U «expr ∈ » nhds (0 : G)), «expr ∉ »(x, U))) : separated_space G :=
begin
  rw ["[", expr topological_add_group.separated_iff_zero_closed, ",", "<-", expr is_open_compl_iff, ",", expr is_open_iff_mem_nhds, "]"] [],
  intros [ident x, ident x_not],
  have [] [":", expr «expr ≠ »(x, 0)] [],
  from [expr mem_compl_singleton_iff.mp x_not],
  rcases [expr H x this, "with", "⟨", ident U, ",", ident U_in, ",", ident xU, "⟩"],
  rw ["<-", expr nhds_zero_symm G] ["at", ident U_in],
  rcases [expr U_in, "with", "⟨", ident W, ",", ident W_in, ",", ident UW, "⟩"],
  rw ["<-", expr nhds_translation_add_neg] [],
  use ["[", expr W, ",", expr W_in, "]"],
  rw [expr subset_compl_comm] [],
  suffices [] [":", expr «expr ∉ »(«expr- »(x), W)],
  by simpa [] [] [] [] [] [],
  exact [expr λ h, xU (UW h)]
end

end 

theorem to_uniform_space_eq {G : Type _} [u : UniformSpace G] [AddCommGroupₓ G] [UniformAddGroup G] :
  TopologicalAddGroup.toUniformSpace G = u :=
  by 
    ext : 1
    show @uniformity G (TopologicalAddGroup.toUniformSpace G) = 𝓤 G 
    rw [uniformity_eq_comap_nhds_zero' G, uniformity_eq_comap_nhds_zero G]

end TopologicalAddCommGroup

open AddCommGroupₓ Filter Set Function

section 

variable{α : Type _}{β : Type _}

variable[TopologicalSpace α][AddCommGroupₓ α][TopologicalAddGroup α]

variable[TopologicalSpace β][AddCommGroupₓ β]

variable{e : β →+ α}(de : DenseInducing e)

include de

-- error in Topology.Algebra.UniformGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_sub_comap_self
(x₀ : α) : tendsto (λ
 t : «expr × »(β, β), «expr - »(t.2, t.1)) «expr $ »(comap (λ
  p : «expr × »(β, β), (e p.1, e p.2)), expr𝓝() (x₀, x₀)) (expr𝓝() 0) :=
begin
  have [ident comm] [":", expr «expr = »(«expr ∘ »(λ
     x : «expr × »(α, α), «expr - »(x.2, x.1), λ
     t : «expr × »(β, β), (e t.1, e t.2)), «expr ∘ »(e, λ t : «expr × »(β, β), «expr - »(t.2, t.1)))] [],
  { ext [] [ident t] [],
    change [expr «expr = »(«expr - »(e t.2, e t.1), e «expr - »(t.2, t.1))] [] [],
    rwa ["<-", expr e.map_sub t.2 t.1] [] },
  have [ident lim] [":", expr tendsto (λ
    x : «expr × »(α, α), «expr - »(x.2, x.1)) (expr𝓝() (x₀, x₀)) (expr𝓝() (e 0))] [],
  { simpa [] [] [] [] [] ["using", expr (continuous_sub.comp (@continuous_swap α α _ _)).tendsto (x₀, x₀)] },
  simpa [] [] [] [] [] ["using", expr de.tendsto_comap_nhds_nhds lim comm]
end

end 

namespace DenseInducing

variable{α : Type _}{β : Type _}{γ : Type _}{δ : Type _}

variable{G : Type _}

variable[TopologicalSpace α][AddCommGroupₓ α][TopologicalAddGroup α]

variable[TopologicalSpace β][AddCommGroupₓ β][TopologicalAddGroup β]

variable[TopologicalSpace γ][AddCommGroupₓ γ][TopologicalAddGroup γ]

variable[TopologicalSpace δ][AddCommGroupₓ δ][TopologicalAddGroup δ]

variable[UniformSpace G][AddCommGroupₓ G][UniformAddGroup G][SeparatedSpace G][CompleteSpace G]

variable{e : β →+ α}(de : DenseInducing e)

variable{f : δ →+ γ}(df : DenseInducing f)

variable{φ : β →+ δ →+ G}

local notation "Φ" => fun p : β × δ => φ p.1 p.2

variable(hφ : Continuous Φ)

include de df hφ

variable{W' : Set G}(W'_nhd : W' ∈ 𝓝 (0 : G))

include W'_nhd

-- error in Topology.Algebra.UniformGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem extend_Z_bilin_aux
(x₀ : α)
(y₁ : δ) : «expr∃ , »((U₂ «expr ∈ » comap e (expr𝓝() x₀)), ∀
 x x' «expr ∈ » U₂, «expr ∈ »(exprΦ() («expr - »(x', x), y₁), W')) :=
begin
  let [ident Nx] [] [":=", expr expr𝓝() x₀],
  let [ident ee] [] [":=", expr λ u : «expr × »(β, β), (e u.1, e u.2)],
  have [ident lim1] [":", expr tendsto (λ
    a : «expr × »(β, β), («expr - »(a.2, a.1), y₁)) «expr ×ᶠ »(comap e Nx, comap e Nx) (expr𝓝() (0, y₁))] [],
  { have [] [] [":=", expr tendsto.prod_mk (tendsto_sub_comap_self de x₀) (tendsto_const_nhds : tendsto (λ
      p : «expr × »(β, β), y₁) «expr $ »(comap ee, expr𝓝() (x₀, x₀)) (expr𝓝() y₁))],
    rw ["[", expr nhds_prod_eq, ",", expr prod_comap_comap_eq, ",", "<-", expr nhds_prod_eq, "]"] [],
    exact [expr (this : _)] },
  have [ident lim2] [":", expr tendsto exprΦ() (expr𝓝() (0, y₁)) (expr𝓝() 0)] [],
  by simpa [] [] [] [] [] ["using", expr hφ.tendsto (0, y₁)],
  have [ident lim] [] [":=", expr lim2.comp lim1],
  rw [expr tendsto_prod_self_iff] ["at", ident lim],
  exact [expr lim W' W'_nhd]
end

-- error in Topology.Algebra.UniformGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem extend_Z_bilin_key
(x₀ : α)
(y₀ : γ) : «expr∃ , »((U «expr ∈ » comap e (expr𝓝() x₀)), «expr∃ , »((V «expr ∈ » comap f (expr𝓝() y₀)), ∀
  x x' «expr ∈ » U, ∀ y y' «expr ∈ » V, «expr ∈ »(«expr - »(exprΦ() (x', y'), exprΦ() (x, y)), W'))) :=
begin
  let [ident Nx] [] [":=", expr expr𝓝() x₀],
  let [ident Ny] [] [":=", expr expr𝓝() y₀],
  let [ident dp] [] [":=", expr dense_inducing.prod de df],
  let [ident ee] [] [":=", expr λ u : «expr × »(β, β), (e u.1, e u.2)],
  let [ident ff] [] [":=", expr λ u : «expr × »(δ, δ), (f u.1, f u.2)],
  have [ident lim_φ] [":", expr filter.tendsto exprΦ() (expr𝓝() (0, 0)) (expr𝓝() 0)] [],
  { simpa [] [] [] [] [] ["using", expr hφ.tendsto (0, 0)] },
  have [ident lim_φ_sub_sub] [":", expr tendsto (λ
    p : «expr × »(«expr × »(β, β), «expr × »(δ, δ)), exprΦ() («expr - »(p.1.2, p.1.1), «expr - »(p.2.2, p.2.1))) «expr ×ᶠ »(«expr $ »(comap ee, expr𝓝() (x₀, x₀)), «expr $ »(comap ff, expr𝓝() (y₀, y₀))) (expr𝓝() 0)] [],
  { have [ident lim_sub_sub] [":", expr tendsto (λ
      p : «expr × »(«expr × »(β, β), «expr × »(δ, δ)), («expr - »(p.1.2, p.1.1), «expr - »(p.2.2, p.2.1))) «expr ×ᶠ »(comap ee (expr𝓝() (x₀, x₀)), comap ff (expr𝓝() (y₀, y₀))) «expr ×ᶠ »(expr𝓝() 0, expr𝓝() 0)] [],
    { have [] [] [":=", expr filter.prod_mono (tendsto_sub_comap_self de x₀) (tendsto_sub_comap_self df y₀)],
      rwa [expr prod_map_map_eq] ["at", ident this] },
    rw ["<-", expr nhds_prod_eq] ["at", ident lim_sub_sub],
    exact [expr tendsto.comp lim_φ lim_sub_sub] },
  rcases [expr exists_nhds_zero_quarter W'_nhd, "with", "⟨", ident W, ",", ident W_nhd, ",", ident W4, "⟩"],
  have [] [":", expr «expr∃ , »((U₁ «expr ∈ » comap e (expr𝓝() x₀)), «expr∃ , »((V₁ «expr ∈ » comap f (expr𝓝() y₀)), ∀
     x x' «expr ∈ » U₁, ∀ y y' «expr ∈ » V₁, «expr ∈ »(exprΦ() («expr - »(x', x), «expr - »(y', y)), W)))] [],
  { have [] [] [":=", expr tendsto_prod_iff.1 lim_φ_sub_sub W W_nhd],
    repeat { rw ["[", expr nhds_prod_eq, ",", "<-", expr prod_comap_comap_eq, "]"] ["at", ident this] },
    rcases [expr this, "with", "⟨", ident U, ",", ident U_in, ",", ident V, ",", ident V_in, ",", ident H, "⟩"],
    rw ["[", expr mem_prod_same_iff, "]"] ["at", ident U_in, ident V_in],
    rcases [expr U_in, "with", "⟨", ident U₁, ",", ident U₁_in, ",", ident HU₁, "⟩"],
    rcases [expr V_in, "with", "⟨", ident V₁, ",", ident V₁_in, ",", ident HV₁, "⟩"],
    existsi ["[", expr U₁, ",", expr U₁_in, ",", expr V₁, ",", expr V₁_in, "]"],
    intros [ident x, ident x', ident x_in, ident x'_in, ident y, ident y', ident y_in, ident y'_in],
    exact [expr H _ _ (HU₁ (mk_mem_prod x_in x'_in)) (HV₁ (mk_mem_prod y_in y'_in))] },
  rcases [expr this, "with", "⟨", ident U₁, ",", ident U₁_nhd, ",", ident V₁, ",", ident V₁_nhd, ",", ident H, "⟩"],
  obtain ["⟨", ident x₁, ",", ident x₁_in, "⟩", ":", expr U₁.nonempty, ":=", expr (de.comap_nhds_ne_bot _).nonempty_of_mem U₁_nhd],
  obtain ["⟨", ident y₁, ",", ident y₁_in, "⟩", ":", expr V₁.nonempty, ":=", expr (df.comap_nhds_ne_bot _).nonempty_of_mem V₁_nhd],
  have [ident cont_flip] [":", expr continuous (λ p : «expr × »(δ, β), φ.flip p.1 p.2)] [],
  { show [expr continuous «expr ∘ »(exprΦ(), prod.swap)],
    from [expr hφ.comp continuous_swap] },
  rcases [expr extend_Z_bilin_aux de df hφ W_nhd x₀ y₁, "with", "⟨", ident U₂, ",", ident U₂_nhd, ",", ident HU, "⟩"],
  rcases [expr extend_Z_bilin_aux df de cont_flip W_nhd y₀ x₁, "with", "⟨", ident V₂, ",", ident V₂_nhd, ",", ident HV, "⟩"],
  existsi ["[", expr «expr ∩ »(U₁, U₂), ",", expr inter_mem U₁_nhd U₂_nhd, ",", expr «expr ∩ »(V₁, V₂), ",", expr inter_mem V₁_nhd V₂_nhd, "]"],
  rintros [ident x, ident x', "⟨", ident xU₁, ",", ident xU₂, "⟩", "⟨", ident x'U₁, ",", ident x'U₂, "⟩", ident y, ident y', "⟨", ident yV₁, ",", ident yV₂, "⟩", "⟨", ident y'V₁, ",", ident y'V₂, "⟩"],
  have [ident key_formula] [":", expr «expr = »(«expr - »(φ x' y', φ x y), «expr + »(«expr + »(«expr + »(φ «expr - »(x', x) y₁, φ «expr - »(x', x) «expr - »(y', y₁)), φ x₁ «expr - »(y', y)), φ «expr - »(x, x₁) «expr - »(y', y)))] [],
  { simp [] [] [] [] [] [],
    abel [] [] [] },
  rw [expr key_formula] [],
  have [ident h₁] [] [":=", expr HU x x' xU₂ x'U₂],
  have [ident h₂] [] [":=", expr H x x' xU₁ x'U₁ y₁ y' y₁_in y'V₁],
  have [ident h₃] [] [":=", expr HV y y' yV₂ y'V₂],
  have [ident h₄] [] [":=", expr H x₁ x x₁_in xU₁ y y' yV₁ y'V₁],
  exact [expr W4 h₁ h₂ h₃ h₄]
end

omit W'_nhd

open DenseInducing

-- error in Topology.Algebra.UniformGroup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Bourbaki GT III.6.5 Theorem I:
ℤ-bilinear continuous maps from dense images into a complete Hausdorff group extend by continuity.
Note: Bourbaki assumes that α and β are also complete Hausdorff, but this is not necessary. -/
theorem extend_Z_bilin : continuous (extend (de.prod df) exprΦ()) :=
begin
  refine [expr continuous_extend_of_cauchy _ _],
  rintro ["⟨", ident x₀, ",", ident y₀, "⟩"],
  split,
  { apply [expr ne_bot.map],
    apply [expr comap_ne_bot],
    intros [ident U, ident h],
    rcases [expr mem_closure_iff_nhds.1 ((de.prod df).dense (x₀, y₀)) U h, "with", "⟨", ident x, ",", ident x_in, ",", "⟨", ident z, ",", ident z_x, "⟩", "⟩"],
    existsi [expr z],
    cc },
  { suffices [] [":", expr «expr ≤ »(map (λ
       p : «expr × »(«expr × »(β, δ), «expr × »(β, δ)), «expr - »(exprΦ() p.2, exprΦ() p.1)) (comap (λ
        p : «expr × »(«expr × »(β, δ), «expr × »(β, δ)), ((e p.1.1, f p.1.2), (e p.2.1, f p.2.2))) «expr ×ᶠ »(expr𝓝() (x₀, y₀), expr𝓝() (x₀, y₀))), expr𝓝() 0)],
    by rwa ["[", expr uniformity_eq_comap_nhds_zero G, ",", expr prod_map_map_eq, ",", "<-", expr map_le_iff_le_comap, ",", expr filter.map_map, ",", expr prod_comap_comap_eq, "]"] [],
    intros [ident W', ident W'_nhd],
    have [ident key] [] [":=", expr extend_Z_bilin_key de df hφ W'_nhd x₀ y₀],
    rcases [expr key, "with", "⟨", ident U, ",", ident U_nhd, ",", ident V, ",", ident V_nhd, ",", ident h, "⟩"],
    rw [expr mem_comap] ["at", ident U_nhd],
    rcases [expr U_nhd, "with", "⟨", ident U', ",", ident U'_nhd, ",", ident U'_sub, "⟩"],
    rw [expr mem_comap] ["at", ident V_nhd],
    rcases [expr V_nhd, "with", "⟨", ident V', ",", ident V'_nhd, ",", ident V'_sub, "⟩"],
    rw ["[", expr mem_map, ",", expr mem_comap, ",", expr nhds_prod_eq, "]"] [],
    existsi [expr set.prod (set.prod U' V') (set.prod U' V')],
    rw [expr mem_prod_same_iff] [],
    simp [] [] ["only"] ["[", expr exists_prop, "]"] [] [],
    split,
    { change [expr «expr ∈ »(U', expr𝓝() x₀)] [] ["at", ident U'_nhd],
      change [expr «expr ∈ »(V', expr𝓝() y₀)] [] ["at", ident V'_nhd],
      have [] [] [":=", expr prod_mem_prod U'_nhd V'_nhd],
      tauto [] },
    { intros [ident p, ident h'],
      simp [] [] ["only"] ["[", expr set.mem_preimage, ",", expr set.prod_mk_mem_set_prod_eq, "]"] [] ["at", ident h'],
      rcases [expr p, "with", "⟨", "⟨", ident x, ",", ident y, "⟩", ",", "⟨", ident x', ",", ident y', "⟩", "⟩"],
      apply [expr h]; tauto [] } }
end

end DenseInducing

