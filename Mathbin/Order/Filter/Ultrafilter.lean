import Mathbin.Order.Filter.Cofinite 
import Mathbin.Order.Zorn

/-!
# Ultrafilters

An ultrafilter is a minimal (maximal in the set order) proper filter.
In this file we define

* `ultrafilter.of`: an ultrafilter that is less than or equal to a given filter;
* `ultrafilter`: subtype of ultrafilters;
* `ultrafilter.pure`: `pure x` as an `ultrafiler`;
* `ultrafilter.map`, `ultrafilter.bind`, `ultrafilter.comap` : operations on ultrafilters;
* `hyperfilter`: the ultrafilter extending the cofinite filter.
-/


universe u v

variable {α : Type u} {β : Type v}

open Set Zorn Filter Function

open_locale Classical Filter

/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
@[protectProj]
structure Ultrafilter (α : Type _) extends Filter α where 
  ne_bot' : ne_bot to_filter 
  le_of_le : ∀ g, Filter.NeBot g → g ≤ to_filter → to_filter ≤ g

namespace Ultrafilter

variable {f g : Ultrafilter α} {s t : Set α} {p q : α → Prop}

instance : CoeTₓ (Ultrafilter α) (Filter α) :=
  ⟨Ultrafilter.toFilter⟩

instance : HasMem (Set α) (Ultrafilter α) :=
  ⟨fun s f => s ∈ (f : Filter α)⟩

theorem Unique (f : Ultrafilter α) {g : Filter α} (h : g ≤ f)
  (hne : ne_bot g :=  by 
    runTac 
      tactic.apply_instance) :
  g = f :=
  le_antisymmₓ h$ f.le_of_le g hne h

instance ne_bot (f : Ultrafilter α) : ne_bot (f : Filter α) :=
  f.ne_bot'

@[simp, normCast]
theorem mem_coe : s ∈ (f : Filter α) ↔ s ∈ f :=
  Iff.rfl

theorem coe_injective : injective (coeₓ : Ultrafilter α → Filter α)
| ⟨f, h₁, h₂⟩, ⟨g, h₃, h₄⟩, rfl =>
  by 
    congr

@[simp, normCast]
theorem coe_le_coe {f g : Ultrafilter α} : (f : Filter α) ≤ g ↔ f = g :=
  ⟨fun h => coe_injective$ g.unique h, fun h => h ▸ le_rfl⟩

@[simp, normCast]
theorem coe_inj : (f : Filter α) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
theorem ext ⦃f g : Ultrafilter α⦄ (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g :=
  coe_injective$ Filter.ext h

theorem le_of_inf_ne_bot (f : Ultrafilter α) {g : Filter α} (hg : ne_bot («expr↑ » f⊓g)) : «expr↑ » f ≤ g :=
  le_of_inf_eq (f.unique inf_le_left hg)

theorem le_of_inf_ne_bot' (f : Ultrafilter α) {g : Filter α} (hg : ne_bot (g⊓f)) : «expr↑ » f ≤ g :=
  f.le_of_inf_ne_bot$
    by 
      rwa [inf_comm]

@[simp]
theorem compl_not_mem_iff : «expr ᶜ» s ∉ f ↔ s ∈ f :=
  ⟨fun hsc =>
      le_principal_iff.1$
        f.le_of_inf_ne_bot
          ⟨fun h =>
              hsc$
                mem_of_eq_bot$
                  by 
                    rwa [compl_compl]⟩,
    compl_not_mem⟩

@[simp]
theorem frequently_iff_eventually : (∃ᶠx in f, p x) ↔ ∀ᶠx in f, p x :=
  compl_not_mem_iff

alias frequently_iff_eventually ↔ Filter.Frequently.eventually _

theorem compl_mem_iff_not_mem : «expr ᶜ» s ∈ f ↔ s ∉ f :=
  by 
    rw [←compl_not_mem_iff, compl_compl]

theorem diff_mem_iff (f : Ultrafilter α) : s \ t ∈ f ↔ s ∈ f ∧ t ∉ f :=
  inter_mem_iff.trans$ and_congr Iff.rfl compl_mem_iff_not_mem

/-- If `sᶜ ∉ f ↔ s ∈ f`, then `f` is an ultrafilter. The other implication is given by
`ultrafilter.compl_not_mem_iff`.  -/
def of_compl_not_mem_iff (f : Filter α) (h : ∀ s, «expr ᶜ» s ∉ f ↔ s ∈ f) : Ultrafilter α :=
  { toFilter := f,
    ne_bot' :=
      ⟨fun hf =>
          by 
            simpa [hf] using h⟩,
    le_of_le :=
      fun g hg hgf s hs =>
        (h s).1$
          fun hsc =>
            by 
              exact compl_not_mem hs (hgf hsc) }

theorem nonempty_of_mem (hs : s ∈ f) : s.nonempty :=
  nonempty_of_mem hs

theorem ne_empty_of_mem (hs : s ∈ f) : s ≠ ∅ :=
  (nonempty_of_mem hs).ne_empty

@[simp]
theorem empty_not_mem : ∅ ∉ f :=
  empty_not_mem f

theorem mem_or_compl_mem (f : Ultrafilter α) (s : Set α) : s ∈ f ∨ «expr ᶜ» s ∈ f :=
  or_iff_not_imp_left.2 compl_mem_iff_not_mem.2

protected theorem em (f : Ultrafilter α) (p : α → Prop) : (∀ᶠx in f, p x) ∨ ∀ᶠx in f, ¬p x :=
  f.mem_or_compl_mem { x | p x }

theorem eventually_or : (∀ᶠx in f, p x ∨ q x) ↔ (∀ᶠx in f, p x) ∨ ∀ᶠx in f, q x :=
  ⟨fun H => (f.em p).imp_right$ fun hp => (H.and hp).mono$ fun x ⟨hx, hnx⟩ => hx.resolve_left hnx,
    fun H => H.elim (fun hp => hp.mono$ fun x => Or.inl) fun hp => hp.mono$ fun x => Or.inr⟩

theorem union_mem_iff : s ∪ t ∈ f ↔ s ∈ f ∨ t ∈ f :=
  eventually_or

theorem eventually_not : (∀ᶠx in f, ¬p x) ↔ ¬∀ᶠx in f, p x :=
  compl_mem_iff_not_mem

theorem eventually_imp : (∀ᶠx in f, p x → q x) ↔ (∀ᶠx in f, p x) → ∀ᶠx in f, q x :=
  by 
    simp only [imp_iff_not_or, eventually_or, eventually_not]

theorem finite_sUnion_mem_iff {s : Set (Set α)} (hs : finite s) : ⋃₀s ∈ f ↔ ∃ (t : _)(_ : t ∈ s), t ∈ f :=
  finite.induction_on hs
      (by 
        simp )$
    fun a s ha hs his =>
      by 
        simp [union_mem_iff, his, or_and_distrib_right, exists_or_distrib]

theorem finite_bUnion_mem_iff {is : Set β} {s : β → Set α} (his : finite is) :
  (⋃(i : _)(_ : i ∈ is), s i) ∈ f ↔ ∃ (i : _)(_ : i ∈ is), s i ∈ f :=
  by 
    simp only [←sUnion_image, finite_sUnion_mem_iff (his.image s), bex_image_iff]

/-- Pushforward for ultrafilters. -/
def map (m : α → β) (f : Ultrafilter α) : Ultrafilter β :=
  of_compl_not_mem_iff (map m f)$ fun s => @compl_not_mem_iff _ f (m ⁻¹' s)

@[simp, normCast]
theorem coe_map (m : α → β) (f : Ultrafilter α) : (map m f : Filter β) = Filter.map m («expr↑ » f) :=
  rfl

@[simp]
theorem mem_map {m : α → β} {f : Ultrafilter α} {s : Set β} : s ∈ map m f ↔ m ⁻¹' s ∈ f :=
  Iff.rfl

/-- The pullback of an ultrafilter along an injection whose range is large with respect to the given
ultrafilter. -/
def comap {m : α → β} (u : Ultrafilter β) (inj : injective m) (large : Set.Range m ∈ u) : Ultrafilter α :=
  { toFilter := comap m u, ne_bot' := u.ne_bot'.comap_of_range_mem large,
    le_of_le :=
      fun g hg hgu =>
        by 
          skip 
          simp only [←u.unique (map_le_iff_le_comap.2 hgu), comap_map inj, le_rfl] }

@[simp]
theorem mem_comap {m : α → β} (u : Ultrafilter β) (inj : injective m) (large : Set.Range m ∈ u) {s : Set α} :
  s ∈ u.comap inj large ↔ m '' s ∈ u :=
  mem_comap_iff inj large

@[simp]
theorem coe_comap {m : α → β} (u : Ultrafilter β) (inj : injective m) (large : Set.Range m ∈ u) :
  (u.comap inj large : Filter α) = Filter.comap m u :=
  rfl

/-- The principal ultrafilter associated to a point `x`. -/
instance : Pure Ultrafilter :=
  ⟨fun α a =>
      of_compl_not_mem_iff (pure a)$
        fun s =>
          by 
            simp ⟩

@[simp]
theorem mem_pure {a : α} {s : Set α} : s ∈ (pure a : Ultrafilter α) ↔ a ∈ s :=
  Iff.rfl

instance [Inhabited α] : Inhabited (Ultrafilter α) :=
  ⟨pure (default _)⟩

instance [Nonempty α] : Nonempty (Ultrafilter α) :=
  Nonempty.map pure inferInstance

/-- Monadic bind for ultrafilters, coming from the one on filters
defined in terms of map and join.-/
def bind (f : Ultrafilter α) (m : α → Ultrafilter β) : Ultrafilter β :=
  of_compl_not_mem_iff (bind («expr↑ » f) fun x => «expr↑ » (m x))$
    fun s =>
      by 
        simp only [mem_bind', mem_coe, ←compl_mem_iff_not_mem, compl_set_of, compl_compl]

instance ultrafilter.has_bind : Bind Ultrafilter :=
  ⟨@Ultrafilter.bind⟩

instance ultrafilter.functor : Functor Ultrafilter :=
  { map := @Ultrafilter.map }

instance ultrafilter.monad : Monadₓ Ultrafilter :=
  { map := @Ultrafilter.map }

section 

attribute [local instance] Filter.monad Filter.is_lawful_monad

instance ultrafilter.is_lawful_monad : IsLawfulMonad Ultrafilter :=
  { id_map := fun α f => coe_injective (id_map f.1), pure_bind := fun α β a f => coe_injective (pure_bind a (coeₓ ∘ f)),
    bind_assoc := fun α β γ f m₁ m₂ => coe_injective (filter_eq rfl),
    bind_pure_comp_eq_map := fun α β f x => coe_injective (bind_pure_comp_eq_map f x.1) }

end 

-- error in Order.Filter.Ultrafilter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The ultrafilter lemma: Any proper filter is contained in an ultrafilter. -/
theorem exists_le (f : filter α) [h : ne_bot f] : «expr∃ , »((u : ultrafilter α), «expr ≤ »(«expr↑ »(u), f)) :=
begin
  let [ident τ] [] [":=", expr {f' // «expr ∧ »(ne_bot f', «expr ≤ »(f', f))}],
  let [ident r] [":", expr τ → τ → exprProp()] [":=", expr λ t₁ t₂, «expr ≤ »(t₂.val, t₁.val)],
  haveI [] [] [":=", expr nonempty_of_ne_bot f],
  let [ident top] [":", expr τ] [":=", expr ⟨f, h, le_refl f⟩],
  let [ident sup] [":", expr ∀
   c : set τ, chain r c → τ] [":=", expr λ
   c
   hc, ⟨«expr⨅ , »((a : {a : τ // «expr ∈ »(a, insert top c)}), a.1), infi_ne_bot_of_directed «expr $ »(directed_of_chain, «expr $ »(chain_insert hc, λ
      ⟨b, _, hb⟩
      (_ _), or.inl hb)) (assume ⟨⟨a, ha, _⟩, _⟩, ha), infi_le_of_le ⟨top, mem_insert _ _⟩ (le_refl _)⟩],
  have [] [":", expr ∀ (c) (hc : chain r c) (a) (ha : «expr ∈ »(a, c)), r a (sup c hc)] [],
  from [expr assume c hc a ha, infi_le_of_le ⟨a, mem_insert_of_mem _ ha⟩ (le_refl _)],
  have [] [":", expr «expr∃ , »((u : τ), ∀ a : τ, r u a → r a u)] [],
  from [expr exists_maximal_of_chains_bounded (assume
    c hc, ⟨sup c hc, this c hc⟩) (assume f₁ f₂ f₃ h₁ h₂, le_trans h₂ h₁)],
  cases [expr this] ["with", ident uτ, ident hmin],
  exact [expr ⟨⟨uτ.val, uτ.property.left, assume
     g hg₁ hg₂, hmin ⟨g, hg₁, le_trans hg₂ uτ.property.right⟩ hg₂⟩, uτ.property.right⟩]
end

alias exists_le ← Filter.exists_ultrafilter_le

/-- Construct an ultrafilter extending a given filter.
  The ultrafilter lemma is the assertion that such a filter exists;
  we use the axiom of choice to pick one. -/
noncomputable def of (f : Filter α) [ne_bot f] : Ultrafilter α :=
  Classical.some (exists_le f)

theorem of_le (f : Filter α) [ne_bot f] : «expr↑ » (of f) ≤ f :=
  Classical.some_spec (exists_le f)

theorem of_coe (f : Ultrafilter α) : of («expr↑ » f) = f :=
  coe_inj.1$ f.unique (of_le f)

theorem exists_ultrafilter_of_finite_inter_nonempty (S : Set (Set α))
  (cond : ∀ T : Finset (Set α), («expr↑ » T : Set (Set α)) ⊆ S → (⋂₀(«expr↑ » T : Set (Set α))).Nonempty) :
  ∃ F : Ultrafilter α, S ⊆ F.sets :=
  by 
    suffices  : ∃ F : Filter α, ne_bot F ∧ S ⊆ F.sets
    ·
      rcases this with ⟨F, cond, hF⟩
      skip 
      obtain ⟨G : Ultrafilter α, h1 : «expr↑ » G ≤ F⟩ := exists_le F 
      exact ⟨G, fun T hT => h1 (hF hT)⟩
    use Filter.generate S 
    refine' ⟨_, fun T hT => Filter.GenerateSets.basic hT⟩
    rw [←forall_mem_nonempty_iff_ne_bot]
    intro T hT 
    rcases mem_generate_iff.mp hT with ⟨A, h1, h2, h3⟩
    let B := Set.Finite.toFinset h2 
    rw
      [show A = «expr↑ » B by 
        simp ] at
      *
    rcases cond B h1 with ⟨x, hx⟩
    exact ⟨x, h3 hx⟩

end Ultrafilter

namespace Filter

open Ultrafilter

-- error in Order.Filter.Ultrafilter: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_iff_ultrafilter
{s : set α}
{f : filter α} : «expr ↔ »(«expr ∈ »(s, f), ∀ g : ultrafilter α, «expr ≤ »(«expr↑ »(g), f) → «expr ∈ »(s, g)) :=
begin
  refine [expr ⟨λ hf g hg, hg hf, λ H, «expr $ »(by_contra, λ hf, _)⟩],
  set [] [ident g] [":", expr filter «expr↥ »(«expr ᶜ»(s))] [":="] [expr comap coe f] [],
  haveI [] [":", expr ne_bot g] [":=", expr comap_ne_bot_iff_compl_range.2 (by simpa [] [] [] ["[", expr compl_set_of, "]"] [] [])],
  simpa [] [] [] [] [] ["using", expr H ((of g).map coe) (map_le_iff_le_comap.mpr (of_le g))]
end

theorem le_iff_ultrafilter {f₁ f₂ : Filter α} : f₁ ≤ f₂ ↔ ∀ g : Ultrafilter α, «expr↑ » g ≤ f₁ → «expr↑ » g ≤ f₂ :=
  ⟨fun h g h₁ => h₁.trans h, fun h s hs => mem_iff_ultrafilter.2$ fun g hg => h g hg hs⟩

/-- A filter equals the intersection of all the ultrafilters which contain it. -/
theorem supr_ultrafilter_le_eq (f : Filter α) : (⨆(g : Ultrafilter α)(hg : «expr↑ » g ≤ f), (g : Filter α)) = f :=
  eq_of_forall_ge_iff$
    fun f' =>
      by 
        simp only [supr_le_iff, ←le_iff_ultrafilter]

/-- The `tendsto` relation can be checked on ultrafilters. -/
theorem tendsto_iff_ultrafilter (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :
  tendsto f l₁ l₂ ↔ ∀ g : Ultrafilter α, «expr↑ » g ≤ l₁ → tendsto f g l₂ :=
  by 
    simpa only [tendsto_iff_comap] using le_iff_ultrafilter

theorem exists_ultrafilter_iff {f : Filter α} : (∃ u : Ultrafilter α, «expr↑ » u ≤ f) ↔ ne_bot f :=
  ⟨fun ⟨u, uf⟩ => ne_bot_of_le uf, fun h => @exists_ultrafilter_le _ _ h⟩

theorem forall_ne_bot_le_iff {g : Filter α} {p : Filter α → Prop} (hp : Monotone p) :
  (∀ f : Filter α, ne_bot f → f ≤ g → p f) ↔ ∀ f : Ultrafilter α, «expr↑ » f ≤ g → p f :=
  by 
    refine' ⟨fun H f hf => H f f.ne_bot hf, _⟩
    intros H f hf hfg 
    exact hp (of_le f) (H _ ((of_le f).trans hfg))

section Hyperfilter

variable (α) [Infinite α]

/-- The ultrafilter extending the cofinite filter. -/
noncomputable def hyperfilter : Ultrafilter α :=
  Ultrafilter.of cofinite

variable {α}

theorem hyperfilter_le_cofinite : «expr↑ » (hyperfilter α) ≤ @cofinite α :=
  Ultrafilter.of_le cofinite

@[simp]
theorem bot_ne_hyperfilter : (⊥ : Filter α) ≠ hyperfilter α :=
  (by 
        infer_instance :
      ne_bot («expr↑ » (hyperfilter α))).1.symm

theorem nmem_hyperfilter_of_finite {s : Set α} (hf : s.finite) : s ∉ hyperfilter α :=
  fun hy => compl_not_mem hy$ hyperfilter_le_cofinite hf.compl_mem_cofinite

alias nmem_hyperfilter_of_finite ← Set.Finite.nmem_hyperfilter

theorem compl_mem_hyperfilter_of_finite {s : Set α} (hf : Set.Finite s) : «expr ᶜ» s ∈ hyperfilter α :=
  compl_mem_iff_not_mem.2 hf.nmem_hyperfilter

alias compl_mem_hyperfilter_of_finite ← Set.Finite.compl_mem_hyperfilter

theorem mem_hyperfilter_of_finite_compl {s : Set α} (hf : Set.Finite («expr ᶜ» s)) : s ∈ hyperfilter α :=
  compl_compl s ▸ hf.compl_mem_hyperfilter

end Hyperfilter

end Filter

