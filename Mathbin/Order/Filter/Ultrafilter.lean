/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
import Mathbin.Order.Filter.Cofinite
import Mathbin.Order.ZornAtoms

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

variable {α : Type u} {β : Type v} {γ : Type _}

open Set Filter Function

open Classical Filter

/-- `filter α` is an atomic type: for every filter there exists an ultrafilter that is less than or
equal to this filter. -/
instance : IsAtomic (Filter α) :=
  IsAtomic.of_is_chain_bounded $ fun c hc hne hb =>
    ⟨inf c, (infNeBotOfDirected' hne (show IsChain (· ≥ ·) c from hc.symm).DirectedOn hb).Ne, fun x hx => Inf_le hx⟩

/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
@[protect_proj]
structure Ultrafilter (α : Type _) extends Filter α where
  neBot' : NeBot to_filter
  le_of_le : ∀ g, Filter.NeBot g → g ≤ to_filter → to_filter ≤ g
#align ultrafilter Ultrafilter

namespace Ultrafilter

variable {f g : Ultrafilter α} {s t : Set α} {p q : α → Prop}

instance : CoeTC (Ultrafilter α) (Filter α) :=
  ⟨Ultrafilter.toFilter⟩

instance : Membership (Set α) (Ultrafilter α) :=
  ⟨fun s f => s ∈ (f : Filter α)⟩

theorem unique (f : Ultrafilter α) {g : Filter α} (h : g ≤ f) (hne : NeBot g := by infer_instance) : g = f :=
  le_antisymm h $ f.le_of_le g hne h
#align ultrafilter.unique Ultrafilter.unique

instance neBot (f : Ultrafilter α) : NeBot (f : Filter α) :=
  f.neBot'
#align ultrafilter.ne_bot Ultrafilter.neBot

protected theorem is_atom (f : Ultrafilter α) : IsAtom (f : Filter α) :=
  ⟨f.ne_bot.Ne, fun g hgf => by_contra $ fun hg => hgf.Ne $ f.unique hgf.le ⟨hg⟩⟩
#align ultrafilter.is_atom Ultrafilter.is_atom

@[simp, norm_cast]
theorem mem_coe : s ∈ (f : Filter α) ↔ s ∈ f :=
  Iff.rfl
#align ultrafilter.mem_coe Ultrafilter.mem_coe

theorem coe_injective : Injective (coe : Ultrafilter α → Filter α)
  | ⟨f, h₁, h₂⟩, ⟨g, h₃, h₄⟩, rfl => by congr
#align ultrafilter.coe_injective Ultrafilter.coe_injective

theorem eq_of_le {f g : Ultrafilter α} (h : (f : Filter α) ≤ g) : f = g :=
  coe_injective (g.unique h)
#align ultrafilter.eq_of_le Ultrafilter.eq_of_le

@[simp, norm_cast]
theorem coe_le_coe {f g : Ultrafilter α} : (f : Filter α) ≤ g ↔ f = g :=
  ⟨fun h => eq_of_le h, fun h => h ▸ le_rfl⟩
#align ultrafilter.coe_le_coe Ultrafilter.coe_le_coe

@[simp, norm_cast]
theorem coe_inj : (f : Filter α) = g ↔ f = g :=
  coe_injective.eq_iff
#align ultrafilter.coe_inj Ultrafilter.coe_inj

@[ext.1]
theorem ext ⦃f g : Ultrafilter α⦄ (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g :=
  coe_injective $ Filter.ext h
#align ultrafilter.ext Ultrafilter.ext

theorem le_of_inf_ne_bot (f : Ultrafilter α) {g : Filter α} (hg : NeBot (↑f ⊓ g)) : ↑f ≤ g :=
  le_of_inf_eq (f.unique inf_le_left hg)
#align ultrafilter.le_of_inf_ne_bot Ultrafilter.le_of_inf_ne_bot

theorem le_of_inf_ne_bot' (f : Ultrafilter α) {g : Filter α} (hg : NeBot (g ⊓ f)) : ↑f ≤ g :=
  f.le_of_inf_ne_bot $ by rwa [inf_comm]
#align ultrafilter.le_of_inf_ne_bot' Ultrafilter.le_of_inf_ne_bot'

theorem inf_ne_bot_iff {f : Ultrafilter α} {g : Filter α} : NeBot (↑f ⊓ g) ↔ ↑f ≤ g :=
  ⟨le_of_inf_ne_bot f, fun h => (inf_of_le_left h).symm ▸ f.ne_bot⟩
#align ultrafilter.inf_ne_bot_iff Ultrafilter.inf_ne_bot_iff

theorem disjoint_iff_not_le {f : Ultrafilter α} {g : Filter α} : Disjoint (↑f) g ↔ ¬↑f ≤ g := by
  rw [← inf_ne_bot_iff, ne_bot_iff, Ne.def, not_not, disjoint_iff]
#align ultrafilter.disjoint_iff_not_le Ultrafilter.disjoint_iff_not_le

@[simp]
theorem compl_not_mem_iff : sᶜ ∉ f ↔ s ∈ f :=
  ⟨fun hsc => le_principal_iff.1 $ f.le_of_inf_ne_bot ⟨fun h => hsc $ mem_of_eq_bot $ by rwa [compl_compl]⟩,
    compl_not_mem⟩
#align ultrafilter.compl_not_mem_iff Ultrafilter.compl_not_mem_iff

@[simp]
theorem frequently_iff_eventually : (∃ᶠ x in f, p x) ↔ ∀ᶠ x in f, p x :=
  compl_not_mem_iff
#align ultrafilter.frequently_iff_eventually Ultrafilter.frequently_iff_eventually

alias frequently_iff_eventually ↔ _root_.filter.frequently.eventually _

theorem compl_mem_iff_not_mem : sᶜ ∈ f ↔ s ∉ f := by rw [← compl_not_mem_iff, compl_compl]
#align ultrafilter.compl_mem_iff_not_mem Ultrafilter.compl_mem_iff_not_mem

theorem diff_mem_iff (f : Ultrafilter α) : s \ t ∈ f ↔ s ∈ f ∧ t ∉ f :=
  inter_mem_iff.trans $ and_congr Iff.rfl compl_mem_iff_not_mem
#align ultrafilter.diff_mem_iff Ultrafilter.diff_mem_iff

/-- If `sᶜ ∉ f ↔ s ∈ f`, then `f` is an ultrafilter. The other implication is given by
`ultrafilter.compl_not_mem_iff`.  -/
def ofComplNotMemIff (f : Filter α) (h : ∀ s, sᶜ ∉ f ↔ s ∈ f) : Ultrafilter α where
  toFilter := f
  neBot' := ⟨fun hf => by simpa [hf] using h⟩
  le_of_le g hg hgf s hs := (h s).1 $ fun hsc => compl_not_mem hs (hgf hsc)
#align ultrafilter.of_compl_not_mem_iff Ultrafilter.ofComplNotMemIff

/-- If `f : filter α` is an atom, then it is an ultrafilter. -/
def ofAtom (f : Filter α) (hf : IsAtom f) : Ultrafilter α where
  toFilter := f
  neBot' := ⟨hf.1⟩
  le_of_le g hg := (is_atom_iff.1 hf).2 g hg.Ne
#align ultrafilter.of_atom Ultrafilter.ofAtom

theorem nonempty_of_mem (hs : s ∈ f) : s.Nonempty :=
  nonempty_of_mem hs
#align ultrafilter.nonempty_of_mem Ultrafilter.nonempty_of_mem

theorem ne_empty_of_mem (hs : s ∈ f) : s ≠ ∅ :=
  (nonempty_of_mem hs).ne_empty
#align ultrafilter.ne_empty_of_mem Ultrafilter.ne_empty_of_mem

@[simp]
theorem empty_not_mem : ∅ ∉ f :=
  empty_not_mem f
#align ultrafilter.empty_not_mem Ultrafilter.empty_not_mem

@[simp]
theorem le_sup_iff {u : Ultrafilter α} {f g : Filter α} : ↑u ≤ f ⊔ g ↔ ↑u ≤ f ∨ ↑u ≤ g :=
  not_iff_not.1 $ by simp only [← disjoint_iff_not_le, not_or, disjoint_sup_right]
#align ultrafilter.le_sup_iff Ultrafilter.le_sup_iff

@[simp]
theorem union_mem_iff : s ∪ t ∈ f ↔ s ∈ f ∨ t ∈ f := by
  simp only [← mem_coe, ← le_principal_iff, ← sup_principal, le_sup_iff]
#align ultrafilter.union_mem_iff Ultrafilter.union_mem_iff

theorem mem_or_compl_mem (f : Ultrafilter α) (s : Set α) : s ∈ f ∨ sᶜ ∈ f :=
  or_iff_not_imp_left.2 compl_mem_iff_not_mem.2
#align ultrafilter.mem_or_compl_mem Ultrafilter.mem_or_compl_mem

protected theorem em (f : Ultrafilter α) (p : α → Prop) : (∀ᶠ x in f, p x) ∨ ∀ᶠ x in f, ¬p x :=
  f.mem_or_compl_mem { x | p x }
#align ultrafilter.em Ultrafilter.em

theorem eventually_or : (∀ᶠ x in f, p x ∨ q x) ↔ (∀ᶠ x in f, p x) ∨ ∀ᶠ x in f, q x :=
  union_mem_iff
#align ultrafilter.eventually_or Ultrafilter.eventually_or

theorem eventually_not : (∀ᶠ x in f, ¬p x) ↔ ¬∀ᶠ x in f, p x :=
  compl_mem_iff_not_mem
#align ultrafilter.eventually_not Ultrafilter.eventually_not

theorem eventually_imp : (∀ᶠ x in f, p x → q x) ↔ (∀ᶠ x in f, p x) → ∀ᶠ x in f, q x := by
  simp only [imp_iff_not_or, eventually_or, eventually_not]
#align ultrafilter.eventually_imp Ultrafilter.eventually_imp

theorem finite_sUnion_mem_iff {s : Set (Set α)} (hs : s.Finite) : ⋃₀ s ∈ f ↔ ∃ t ∈ s, t ∈ f :=
  Finite.induction_on hs (by simp) $ fun a s ha hs his => by simp [union_mem_iff, his, or_and_right, exists_or]
#align ultrafilter.finite_sUnion_mem_iff Ultrafilter.finite_sUnion_mem_iff

theorem finite_bUnion_mem_iff {is : Set β} {s : β → Set α} (his : is.Finite) :
    (⋃ i ∈ is, s i) ∈ f ↔ ∃ i ∈ is, s i ∈ f := by
  simp only [← sUnion_image, finite_sUnion_mem_iff (his.image s), bex_image_iff]
#align ultrafilter.finite_bUnion_mem_iff Ultrafilter.finite_bUnion_mem_iff

/-- Pushforward for ultrafilters. -/
def map (m : α → β) (f : Ultrafilter α) : Ultrafilter β :=
  ofComplNotMemIff (map m f) $ fun s => @compl_not_mem_iff _ f (m ⁻¹' s)
#align ultrafilter.map Ultrafilter.map

@[simp, norm_cast]
theorem coe_map (m : α → β) (f : Ultrafilter α) : (map m f : Filter β) = Filter.map m ↑f :=
  rfl
#align ultrafilter.coe_map Ultrafilter.coe_map

@[simp]
theorem mem_map {m : α → β} {f : Ultrafilter α} {s : Set β} : s ∈ map m f ↔ m ⁻¹' s ∈ f :=
  Iff.rfl
#align ultrafilter.mem_map Ultrafilter.mem_map

@[simp]
theorem map_id (f : Ultrafilter α) : f.map id = f :=
  coe_injective map_id
#align ultrafilter.map_id Ultrafilter.map_id

@[simp]
theorem map_id' (f : Ultrafilter α) : (f.map fun x => x) = f :=
  map_id _
#align ultrafilter.map_id' Ultrafilter.map_id'

@[simp]
theorem map_map (f : Ultrafilter α) (m : α → β) (n : β → γ) : (f.map m).map n = f.map (n ∘ m) :=
  coe_injective map_map
#align ultrafilter.map_map Ultrafilter.map_map

/-- The pullback of an ultrafilter along an injection whose range is large with respect to the given
ultrafilter. -/
def comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m ∈ u) : Ultrafilter α where
  toFilter := comap m u
  neBot' := u.neBot'.comapOfRangeMem large
  le_of_le g hg hgu := by
    skip
    simp only [← u.unique (map_le_iff_le_comap.2 hgu), comap_map inj, le_rfl]
#align ultrafilter.comap Ultrafilter.comap

@[simp]
theorem mem_comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m ∈ u) {s : Set α} :
    s ∈ u.comap inj large ↔ m '' s ∈ u :=
  mem_comap_iff inj large
#align ultrafilter.mem_comap Ultrafilter.mem_comap

@[simp, norm_cast]
theorem coe_comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m ∈ u) :
    (u.comap inj large : Filter α) = Filter.comap m u :=
  rfl
#align ultrafilter.coe_comap Ultrafilter.coe_comap

@[simp]
theorem comap_id (f : Ultrafilter α) (h₀ : Injective (id : α → α) := injective_id)
    (h₁ : range id ∈ f := by
      rw [range_id]
      exact univ_mem) :
    f.comap h₀ h₁ = f :=
  coe_injective comap_id
#align ultrafilter.comap_id Ultrafilter.comap_id

@[simp]
theorem comap_comap (f : Ultrafilter γ) {m : α → β} {n : β → γ} (inj₀ : Injective n) (large₀ : range n ∈ f)
    (inj₁ : Injective m) (large₁ : range m ∈ f.comap inj₀ large₀) (inj₂ : Injective (n ∘ m) := inj₀.comp inj₁)
    (large₂ : range (n ∘ m) ∈ f := by
      rw [range_comp]
      exact image_mem_of_mem_comap large₀ large₁) :
    (f.comap inj₀ large₀).comap inj₁ large₁ = f.comap inj₂ large₂ :=
  coe_injective comap_comap
#align ultrafilter.comap_comap Ultrafilter.comap_comap

/-- The principal ultrafilter associated to a point `x`. -/
instance : Pure Ultrafilter :=
  ⟨fun α a => ofComplNotMemIff (pure a) $ fun s => by simp⟩

@[simp]
theorem mem_pure {a : α} {s : Set α} : s ∈ (pure a : Ultrafilter α) ↔ a ∈ s :=
  Iff.rfl
#align ultrafilter.mem_pure Ultrafilter.mem_pure

@[simp]
theorem coe_pure (a : α) : ↑(pure a : Ultrafilter α) = (pure a : Filter α) :=
  rfl
#align ultrafilter.coe_pure Ultrafilter.coe_pure

@[simp]
theorem map_pure (m : α → β) (a : α) : map m (pure a) = pure (m a) :=
  rfl
#align ultrafilter.map_pure Ultrafilter.map_pure

@[simp]
theorem comap_pure {m : α → β} (a : α) (inj : Injective m) (large) : comap (pure $ m a) inj large = pure a :=
  coe_injective $ comap_pure.trans $ by rw [coe_pure, ← principal_singleton, ← image_singleton, preimage_image_eq _ inj]
#align ultrafilter.comap_pure Ultrafilter.comap_pure

theorem pure_injective : Injective (pure : α → Ultrafilter α) := fun a b h =>
  Filter.pure_injective (congr_arg Ultrafilter.toFilter h : _)
#align ultrafilter.pure_injective Ultrafilter.pure_injective

instance [Inhabited α] : Inhabited (Ultrafilter α) :=
  ⟨pure default⟩

instance [Nonempty α] : Nonempty (Ultrafilter α) :=
  Nonempty.map pure inferInstance

theorem eq_pure_of_finite_mem (h : s.Finite) (h' : s ∈ f) : ∃ x ∈ s, f = pure x := by
  rw [← bUnion_of_singleton s] at h'
  rcases(Ultrafilter.finite_bUnion_mem_iff h).mp h' with ⟨a, has, haf⟩
  exact ⟨a, has, eq_of_le (Filter.le_pure_iff.2 haf)⟩
#align ultrafilter.eq_pure_of_finite_mem Ultrafilter.eq_pure_of_finite_mem

theorem eq_pure_of_finite [Finite α] (f : Ultrafilter α) : ∃ a, f = pure a :=
  (eq_pure_of_finite_mem finite_univ univ_mem).imp $ fun a ⟨_, ha⟩ => ha
#align ultrafilter.eq_pure_of_finite Ultrafilter.eq_pure_of_finite

theorem le_cofinite_or_eq_pure (f : Ultrafilter α) : (f : Filter α) ≤ cofinite ∨ ∃ a, f = pure a :=
  or_iff_not_imp_left.2 $ fun h =>
    let ⟨s, hs, hfin⟩ := Filter.disjoint_cofinite_right.1 (disjoint_iff_not_le.2 h)
    let ⟨a, has, hf⟩ := eq_pure_of_finite_mem hfin hs
    ⟨a, hf⟩
#align ultrafilter.le_cofinite_or_eq_pure Ultrafilter.le_cofinite_or_eq_pure

/-- Monadic bind for ultrafilters, coming from the one on filters
defined in terms of map and join.-/
def bind (f : Ultrafilter α) (m : α → Ultrafilter β) : Ultrafilter β :=
  ofComplNotMemIff (bind (↑f) fun x => ↑(m x)) $ fun s => by
    simp only [mem_bind', mem_coe, ← compl_mem_iff_not_mem, compl_set_of, compl_compl]
#align ultrafilter.bind Ultrafilter.bind

instance hasBind : Bind Ultrafilter :=
  ⟨@Ultrafilter.bind⟩
#align ultrafilter.has_bind Ultrafilter.hasBind

instance functor : Functor Ultrafilter where map := @Ultrafilter.map
#align ultrafilter.functor Ultrafilter.functor

instance monad : Monad Ultrafilter where map := @Ultrafilter.map
#align ultrafilter.monad Ultrafilter.monad

section

attribute [local instance] Filter.monad Filter.is_lawful_monad

instance is_lawful_monad : LawfulMonad Ultrafilter where
  id_map α f := coe_injective (id_map f.1)
  pure_bind α β a f := coe_injective (pure_bind a (coe ∘ f))
  bind_assoc α β γ f m₁ m₂ := coe_injective (filter_eq rfl)
  bind_pure_comp_eq_map α β f x := coe_injective (bind_pure_comp_eq_map f x.1)
#align ultrafilter.is_lawful_monad Ultrafilter.is_lawful_monad

end

/-- The ultrafilter lemma: Any proper filter is contained in an ultrafilter. -/
theorem exists_le (f : Filter α) [h : NeBot f] : ∃ u : Ultrafilter α, ↑u ≤ f :=
  let ⟨u, hu, huf⟩ := (eq_bot_or_exists_atom_le f).resolve_left h.Ne
  ⟨ofAtom u hu, huf⟩
#align ultrafilter.exists_le Ultrafilter.exists_le

alias exists_le ← _root_.filter.exists_ultrafilter_le

/-- Construct an ultrafilter extending a given filter.
  The ultrafilter lemma is the assertion that such a filter exists;
  we use the axiom of choice to pick one. -/
noncomputable def of (f : Filter α) [NeBot f] : Ultrafilter α :=
  Classical.choose (exists_le f)
#align ultrafilter.of Ultrafilter.of

theorem of_le (f : Filter α) [NeBot f] : ↑(of f) ≤ f :=
  Classical.choose_spec (exists_le f)
#align ultrafilter.of_le Ultrafilter.of_le

theorem of_coe (f : Ultrafilter α) : of ↑f = f :=
  coe_inj.1 $ f.unique (of_le f)
#align ultrafilter.of_coe Ultrafilter.of_coe

theorem exists_ultrafilter_of_finite_inter_nonempty (S : Set (Set α))
    (cond : ∀ T : Finset (Set α), (↑T : Set (Set α)) ⊆ S → (⋂₀ (↑T : Set (Set α))).Nonempty) :
    ∃ F : Ultrafilter α, S ⊆ F.sets :=
  haveI : ne_bot (generate S) :=
    generate_ne_bot_iff.2 fun t hts ht => ht.coe_to_finset ▸ cond ht.toFinset (ht.coe_to_finset.symm ▸ hts)
  ⟨of (generate S), fun t ht => (of_le $ generate S) $ generate_sets.basic ht⟩
#align ultrafilter.exists_ultrafilter_of_finite_inter_nonempty Ultrafilter.exists_ultrafilter_of_finite_inter_nonempty

end Ultrafilter

namespace Filter

variable {f : Filter α} {s : Set α} {a : α}

open Ultrafilter

theorem is_atom_pure : IsAtom (pure a : Filter α) :=
  (pure a : Ultrafilter α).IsAtom
#align filter.is_atom_pure Filter.is_atom_pure

protected theorem NeBot.le_pure_iff (hf : f.ne_bot) : f ≤ pure a ↔ f = pure a :=
  ⟨Ultrafilter.unique (pure a), le_of_eq⟩
#align filter.ne_bot.le_pure_iff Filter.NeBot.le_pure_iff

@[simp]
theorem lt_pure_iff : f < pure a ↔ f = ⊥ :=
  is_atom_pure.lt_iff
#align filter.lt_pure_iff Filter.lt_pure_iff

theorem le_pure_iff' : f ≤ pure a ↔ f = ⊥ ∨ f = pure a :=
  is_atom_pure.le_iff
#align filter.le_pure_iff' Filter.le_pure_iff'

@[simp]
theorem Iic_pure (a : α) : iic (pure a : Filter α) = {⊥, pure a} :=
  is_atom_pure.Iic_eq
#align filter.Iic_pure Filter.Iic_pure

theorem mem_iff_ultrafilter : s ∈ f ↔ ∀ g : Ultrafilter α, ↑g ≤ f → s ∈ g := by
  refine' ⟨fun hf g hg => hg hf, fun H => by_contra $ fun hf => _⟩
  set g : Filter ↥(sᶜ) := comap coe f
  haveI : ne_bot g := comap_ne_bot_iff_compl_range.2 (by simpa [compl_set_of] )
  simpa using H ((of g).map coe) (map_le_iff_le_comap.mpr (of_le g))
#align filter.mem_iff_ultrafilter Filter.mem_iff_ultrafilter

theorem le_iff_ultrafilter {f₁ f₂ : Filter α} : f₁ ≤ f₂ ↔ ∀ g : Ultrafilter α, ↑g ≤ f₁ → ↑g ≤ f₂ :=
  ⟨fun h g h₁ => h₁.trans h, fun h s hs => mem_iff_ultrafilter.2 $ fun g hg => h g hg hs⟩
#align filter.le_iff_ultrafilter Filter.le_iff_ultrafilter

/-- A filter equals the intersection of all the ultrafilters which contain it. -/
theorem supr_ultrafilter_le_eq (f : Filter α) : (⨆ (g : Ultrafilter α) (hg : ↑g ≤ f), (g : Filter α)) = f :=
  eq_of_forall_ge_iff $ fun f' => by simp only [supr_le_iff, ← le_iff_ultrafilter]
#align filter.supr_ultrafilter_le_eq Filter.supr_ultrafilter_le_eq

/-- The `tendsto` relation can be checked on ultrafilters. -/
theorem tendsto_iff_ultrafilter (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :
    Tendsto f l₁ l₂ ↔ ∀ g : Ultrafilter α, ↑g ≤ l₁ → Tendsto f g l₂ := by
  simpa only [tendsto_iff_comap] using le_iff_ultrafilter
#align filter.tendsto_iff_ultrafilter Filter.tendsto_iff_ultrafilter

theorem exists_ultrafilter_iff {f : Filter α} : (∃ u : Ultrafilter α, ↑u ≤ f) ↔ NeBot f :=
  ⟨fun ⟨u, uf⟩ => neBotOfLe uf, fun h => @exists_ultrafilter_le _ _ h⟩
#align filter.exists_ultrafilter_iff Filter.exists_ultrafilter_iff

theorem forall_ne_bot_le_iff {g : Filter α} {p : Filter α → Prop} (hp : Monotone p) :
    (∀ f : Filter α, NeBot f → f ≤ g → p f) ↔ ∀ f : Ultrafilter α, ↑f ≤ g → p f := by
  refine' ⟨fun H f hf => H f f.ne_bot hf, _⟩
  intro H f hf hfg
  exact hp (of_le f) (H _ ((of_le f).trans hfg))
#align filter.forall_ne_bot_le_iff Filter.forall_ne_bot_le_iff

section Hyperfilter

variable (α) [Infinite α]

/-- The ultrafilter extending the cofinite filter. -/
noncomputable def hyperfilter : Ultrafilter α :=
  Ultrafilter.of cofinite
#align filter.hyperfilter Filter.hyperfilter

variable {α}

theorem hyperfilter_le_cofinite : ↑(hyperfilter α) ≤ @cofinite α :=
  Ultrafilter.of_le cofinite
#align filter.hyperfilter_le_cofinite Filter.hyperfilter_le_cofinite

@[simp]
theorem bot_ne_hyperfilter : (⊥ : Filter α) ≠ hyperfilter α :=
  (by infer_instance : NeBot ↑(hyperfilter α)).1.symm
#align filter.bot_ne_hyperfilter Filter.bot_ne_hyperfilter

theorem nmem_hyperfilter_of_finite {s : Set α} (hf : s.Finite) : s ∉ hyperfilter α := fun hy =>
  compl_not_mem hy $ hyperfilter_le_cofinite hf.compl_mem_cofinite
#align filter.nmem_hyperfilter_of_finite Filter.nmem_hyperfilter_of_finite

alias nmem_hyperfilter_of_finite ← _root_.set.finite.nmem_hyperfilter

theorem compl_mem_hyperfilter_of_finite {s : Set α} (hf : Set.Finite s) : sᶜ ∈ hyperfilter α :=
  compl_mem_iff_not_mem.2 hf.nmem_hyperfilter
#align filter.compl_mem_hyperfilter_of_finite Filter.compl_mem_hyperfilter_of_finite

alias compl_mem_hyperfilter_of_finite ← _root_.set.finite.compl_mem_hyperfilter

theorem mem_hyperfilter_of_finite_compl {s : Set α} (hf : Set.Finite (sᶜ)) : s ∈ hyperfilter α :=
  compl_compl s ▸ hf.compl_mem_hyperfilter
#align filter.mem_hyperfilter_of_finite_compl Filter.mem_hyperfilter_of_finite_compl

end Hyperfilter

end Filter

namespace Ultrafilter

open Filter

variable {m : α → β} {s : Set α} {g : Ultrafilter β}

theorem comapInfPrincipalNeBotOfImageMem (h : m '' s ∈ g) : (Filter.comap m g ⊓ 𝓟 s).ne_bot :=
  Filter.comapInfPrincipalNeBotOfImageMem g.ne_bot h
#align ultrafilter.comap_inf_principal_ne_bot_of_image_mem Ultrafilter.comapInfPrincipalNeBotOfImageMem

/-- Ultrafilter extending the inf of a comapped ultrafilter and a principal ultrafilter. -/
noncomputable def ofComapInfPrincipal (h : m '' s ∈ g) : Ultrafilter α :=
  @of _ (Filter.comap m g ⊓ 𝓟 s) (comapInfPrincipalNeBotOfImageMem h)
#align ultrafilter.of_comap_inf_principal Ultrafilter.ofComapInfPrincipal

theorem of_comap_inf_principal_mem (h : m '' s ∈ g) : s ∈ ofComapInfPrincipal h := by
  let f := Filter.comap m g ⊓ 𝓟 s
  haveI : f.ne_bot := comap_inf_principal_ne_bot_of_image_mem h
  have : s ∈ f := mem_inf_of_right (mem_principal_self s)
  exact le_def.mp (of_le _) s this
#align ultrafilter.of_comap_inf_principal_mem Ultrafilter.of_comap_inf_principal_mem

theorem of_comap_inf_principal_eq_of_map (h : m '' s ∈ g) : (ofComapInfPrincipal h).map m = g := by
  let f := Filter.comap m g ⊓ 𝓟 s
  haveI : f.ne_bot := comap_inf_principal_ne_bot_of_image_mem h
  apply eq_of_le
  calc
    Filter.map m (of f) ≤ Filter.map m f := map_mono (of_le _)
    _ ≤ (Filter.map m $ Filter.comap m g) ⊓ Filter.map m (𝓟 s) := map_inf_le
    _ = (Filter.map m $ Filter.comap m g) ⊓ (𝓟 $ m '' s) := by rw [map_principal]
    _ ≤ g ⊓ (𝓟 $ m '' s) := inf_le_inf_right _ map_comap_le
    _ = g := inf_of_le_left (le_principal_iff.mpr h)
    
#align ultrafilter.of_comap_inf_principal_eq_of_map Ultrafilter.of_comap_inf_principal_eq_of_map

end Ultrafilter

