/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
import Mathbin.Order.Filter.AtTopBot
import Mathbin.Order.Filter.Pi

/-!
# The cofinite filter

In this file we define

`cofinite`: the filter of sets with finite complement

and prove its basic properties. In particular, we prove that for `ℕ` it is equal to `at_top`.

## TODO

Define filters for other cardinalities of the complement.
-/


open Set Function

open_locale Classical

variable {α : Type _}

namespace Filter

/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite : Filter α where
  Sets := { s | Finite (sᶜ) }
  univ_sets := by
    simp only [compl_univ, finite_empty, mem_set_of_eq]
  sets_of_superset := fun st : s ⊆ t => hs.Subset <| compl_subset_compl.2 st
  inter_sets := fun ht : Finite (tᶜ) => by
    simp only [compl_inter, finite.union, ht, hs, mem_set_of_eq]

@[simp]
theorem mem_cofinite {s : Set α} : s ∈ @cofinite α ↔ Finite (sᶜ) :=
  Iff.rfl

@[simp]
theorem eventually_cofinite {p : α → Prop} : (∀ᶠ x in cofinite, p x) ↔ Finite { x | ¬p x } :=
  Iff.rfl

theorem has_basis_cofinite : HasBasis cofinite (fun s : Set α => s.Finite) compl :=
  ⟨fun s => ⟨fun h => ⟨sᶜ, h, (compl_compl s).Subset⟩, fun ⟨t, htf, hts⟩ => htf.Subset <| compl_subset_comm.2 hts⟩⟩

instance cofinite_ne_bot [Infinite α] : NeBot (@cofinite α) :=
  has_basis_cofinite.ne_bot_iff.2 fun s hs => hs.infinite_compl.Nonempty

theorem frequently_cofinite_iff_infinite {p : α → Prop} : (∃ᶠ x in cofinite, p x) ↔ Set.Infinite { x | p x } := by
  simp only [Filter.Frequently, Filter.Eventually, mem_cofinite, compl_set_of, not_not, Set.Infinite]

/-- The coproduct of the cofinite filters on two types is the cofinite filter on their product. -/
theorem coprod_cofinite {β : Type _} : (cofinite : Filter α).coprod (cofinite : Filter β) = cofinite := by
  ext S
  simp only [mem_coprod_iff, exists_prop, mem_comap, mem_cofinite]
  constructor
  · rintro ⟨⟨A, hAf, hAS⟩, B, hBf, hBS⟩
    rw [← compl_subset_compl, ← preimage_compl] at hAS hBS
    exact (hAf.prod hBf).Subset (subset_inter hAS hBS)
    
  · intro hS
    refine' ⟨⟨(Prod.fst '' Sᶜ)ᶜ, _, _⟩, ⟨(Prod.snd '' Sᶜ)ᶜ, _, _⟩⟩
    · simpa using hS.image Prod.fst
      
    · simpa [compl_subset_comm] using subset_preimage_image Prod.fst (Sᶜ)
      
    · simpa using hS.image Prod.snd
      
    · simpa [compl_subset_comm] using subset_preimage_image Prod.snd (Sᶜ)
      
    

/-- Finite product of finite sets is finite -/
theorem Coprod_cofinite {δ : Type _} {κ : δ → Type _} [Fintype δ] :
    (Filter.coprodₓ fun d => (cofinite : Filter (κ d))) = cofinite := by
  ext S
  rcases compl_surjective S with ⟨S, rfl⟩
  simp_rw [compl_mem_Coprod_iff, mem_cofinite, compl_compl]
  constructor
  · rintro ⟨t, htf, hsub⟩
    exact (finite.pi htf).Subset hsub
    
  · exact fun hS => ⟨fun i => eval i '' S, fun i => hS.Image _, subset_pi_eval_image _ _⟩
    

end Filter

open Filter

theorem Set.Finite.compl_mem_cofinite {s : Set α} (hs : s.Finite) : sᶜ ∈ @cofinite α :=
  mem_cofinite.2 <| (compl_compl s).symm ▸ hs

theorem Set.Finite.eventually_cofinite_nmem {s : Set α} (hs : s.Finite) : ∀ᶠ x in cofinite, x ∉ s :=
  hs.compl_mem_cofinite

theorem Finset.eventually_cofinite_nmem (s : Finset α) : ∀ᶠ x in cofinite, x ∉ s :=
  s.finite_to_set.eventually_cofinite_nmem

theorem Set.infinite_iff_frequently_cofinite {s : Set α} : Set.Infinite s ↔ ∃ᶠ x in cofinite, x ∈ s :=
  frequently_cofinite_iff_infinite.symm

theorem Filter.eventually_cofinite_ne (x : α) : ∀ᶠ a in cofinite, a ≠ x :=
  (Set.finite_singleton x).eventually_cofinite_nmem

/-- If `α` is a sup-semilattice with no maximal element, then `at_top ≤ cofinite`. -/
theorem at_top_le_cofinite [SemilatticeSup α] [NoMaxOrder α] : (atTop : Filter α) ≤ cofinite := by
  refine' compl_surjective.forall.2 fun s hs => _
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [compl_empty, univ_mem]
    
  rw [mem_cofinite, compl_compl] at hs
  lift s to Finset α using hs
  rcases exists_gt (s.sup' hne id) with ⟨y, hy⟩
  filter_upwards [mem_at_top y] with x hx hxs
  exact (Finset.le_sup' id hxs).not_lt (hy.trans_le hx)

/-- For natural numbers the filters `cofinite` and `at_top` coincide. -/
theorem Nat.cofinite_eq_at_top : @cofinite ℕ = at_top := by
  refine' le_antisymmₓ _ at_top_le_cofinite
  refine' at_top_basis.ge_iff.2 fun N hN => _
  simpa only [mem_cofinite, compl_Ici] using finite_lt_nat N

theorem Nat.frequently_at_top_iff_infinite {p : ℕ → Prop} : (∃ᶠ n in at_top, p n) ↔ Set.Infinite { n | p n } := by
  simp only [← Nat.cofinite_eq_at_top, frequently_cofinite_iff_infinite]

theorem Filter.Tendsto.exists_within_forall_le {α β : Type _} [LinearOrderₓ β] {s : Set α} (hs : s.Nonempty) {f : α → β}
    (hf : Filter.Tendsto f Filter.cofinite Filter.atTop) : ∃ a₀ ∈ s, ∀, ∀ a ∈ s, ∀, f a₀ ≤ f a := by
  rcases em (∃ y ∈ s, ∃ x, f y < x) with (⟨y, hys, x, hx⟩ | not_all_top)
  · -- the set of points `{y | f y < x}` is nonempty and finite, so we take `min` over this set
    have : finite { y | ¬x ≤ f y } := filter.eventually_cofinite.mp (tendsto_at_top.1 hf x)
    simp only [not_leₓ] at this
    obtain ⟨a₀, ⟨ha₀ : f a₀ < x, ha₀s⟩, others_bigger⟩ := exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩
    refine' ⟨a₀, ha₀s, fun a has => (lt_or_leₓ (f a) x).elim _ (le_transₓ ha₀.le)⟩
    exact fun h => others_bigger a ⟨h, has⟩
    
  · -- in this case, f is constant because all values are at top
    push_neg  at not_all_top
    obtain ⟨a₀, ha₀s⟩ := hs
    exact ⟨a₀, ha₀s, fun a ha => not_all_top a ha (f a₀)⟩
    

theorem Filter.Tendsto.exists_forall_le {α β : Type _} [Nonempty α] [LinearOrderₓ β] {f : α → β}
    (hf : Tendsto f cofinite atTop) : ∃ a₀, ∀ a, f a₀ ≤ f a :=
  let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty
  ⟨a₀, fun a => ha₀ a (mem_univ _)⟩

theorem Filter.Tendsto.exists_within_forall_ge {α β : Type _} [LinearOrderₓ β] {s : Set α} (hs : s.Nonempty) {f : α → β}
    (hf : Filter.Tendsto f Filter.cofinite Filter.atBot) : ∃ a₀ ∈ s, ∀, ∀ a ∈ s, ∀, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_within_forall_le _ (OrderDual β) _ _ hs _ hf

theorem Filter.Tendsto.exists_forall_ge {α β : Type _} [Nonempty α] [LinearOrderₓ β] {f : α → β}
    (hf : Tendsto f cofinite atBot) : ∃ a₀, ∀ a, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_forall_le _ (OrderDual β) _ _ _ hf

/-- For an injective function `f`, inverse images of finite sets are finite. -/
theorem Function.Injective.tendsto_cofinite {α β : Type _} {f : α → β} (hf : Injective f) :
    Tendsto f cofinite cofinite := fun s h => h.Preimage (hf.InjOn _)

/-- An injective sequence `f : ℕ → ℕ` tends to infinity at infinity. -/
theorem Function.Injective.nat_tendsto_at_top {f : ℕ → ℕ} (hf : Injective f) : Tendsto f atTop atTop :=
  Nat.cofinite_eq_at_top ▸ hf.tendsto_cofinite

