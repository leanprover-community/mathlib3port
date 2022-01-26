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


open Set

open_locale Classical

variable {α : Type _}

namespace Filter

/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite : Filter α where
  Sets := { s | finite (sᶜ) }
  univ_sets := by
    simp only [compl_univ, finite_empty, mem_set_of_eq]
  sets_of_superset := fun s t hs : finite (sᶜ) st : s ⊆ t => hs.subset <| compl_subset_compl.2 st
  inter_sets := fun s t hs : finite (sᶜ) ht : finite (tᶜ) => by
    simp only [compl_inter, finite.union, ht, hs, mem_set_of_eq]

@[simp]
theorem mem_cofinite {s : Set α} : s ∈ @cofinite α ↔ finite (sᶜ) :=
  Iff.rfl

@[simp]
theorem eventually_cofinite {p : α → Prop} : (∀ᶠ x in cofinite, p x) ↔ finite { x | ¬p x } :=
  Iff.rfl

theorem has_basis_cofinite : has_basis cofinite (fun s : Set α => s.finite) compl :=
  ⟨fun s => ⟨fun h => ⟨sᶜ, h, (compl_compl s).Subset⟩, fun ⟨t, htf, hts⟩ => htf.subset <| compl_subset_comm.2 hts⟩⟩

instance cofinite_ne_bot [Infinite α] : ne_bot (@cofinite α) :=
  has_basis_cofinite.ne_bot_iff.2 fun s hs => hs.infinite_compl.nonempty

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
    
  · exact fun hS => ⟨fun i => Function.eval i '' S, fun i => hS.image _, subset_pi_eval_image _ _⟩
    

end Filter

open Filter

theorem Set.Finite.compl_mem_cofinite {s : Set α} (hs : s.finite) : sᶜ ∈ @cofinite α :=
  mem_cofinite.2 <| (compl_compl s).symm ▸ hs

theorem Set.Finite.eventually_cofinite_nmem {s : Set α} (hs : s.finite) : ∀ᶠ x in cofinite, x ∉ s :=
  hs.compl_mem_cofinite

theorem Finset.eventually_cofinite_nmem (s : Finset α) : ∀ᶠ x in cofinite, x ∉ s :=
  s.finite_to_set.eventually_cofinite_nmem

theorem Set.infinite_iff_frequently_cofinite {s : Set α} : Set.Infinite s ↔ ∃ᶠ x in cofinite, x ∈ s :=
  frequently_cofinite_iff_infinite.symm

theorem Filter.eventually_cofinite_ne (x : α) : ∀ᶠ a in cofinite, a ≠ x :=
  (Set.finite_singleton x).eventually_cofinite_nmem

/-- For natural numbers the filters `cofinite` and `at_top` coincide. -/
theorem Nat.cofinite_eq_at_top : @cofinite ℕ = at_top := by
  ext s
  simp only [mem_cofinite, mem_at_top_sets]
  constructor
  · intro hs
    use hs.to_finset.sup id + 1
    intro b hb
    by_contra hbs
    have := hs.to_finset.subset_range_sup_succ (hs.mem_to_finset.2 hbs)
    exact not_lt_of_le hb (Finset.mem_range.1 this)
    
  · rintro ⟨N, hN⟩
    apply (finite_lt_nat N).Subset
    intro n hn
    change n < N
    exact lt_of_not_geₓ fun hn' => hn <| hN n hn'
    

theorem Nat.frequently_at_top_iff_infinite {p : ℕ → Prop} : (∃ᶠ n in at_top, p n) ↔ Set.Infinite { n | p n } := by
  simp only [← Nat.cofinite_eq_at_top, frequently_cofinite_iff_infinite]

theorem Filter.Tendsto.exists_within_forall_le {α β : Type _} [LinearOrderₓ β] {s : Set α} (hs : s.nonempty) {f : α → β}
    (hf : Filter.Tendsto f Filter.cofinite Filter.atTop) : ∃ a₀ ∈ s, ∀, ∀ a ∈ s, ∀, f a₀ ≤ f a := by
  rcases em (∃ y ∈ s, ∃ x, f y < x) with (⟨y, hys, x, hx⟩ | not_all_top)
  · have : finite { y | ¬x ≤ f y } := filter.eventually_cofinite.mp (tendsto_at_top.1 hf x)
    simp only [not_leₓ] at this
    obtain ⟨a₀, ⟨ha₀ : f a₀ < x, ha₀s⟩, others_bigger⟩ := exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩
    refine' ⟨a₀, ha₀s, fun a has => (lt_or_leₓ (f a) x).elim _ (le_transₓ ha₀.le)⟩
    exact fun h => others_bigger a ⟨h, has⟩
    
  · push_neg  at not_all_top
    obtain ⟨a₀, ha₀s⟩ := hs
    exact ⟨a₀, ha₀s, fun a ha => not_all_top a ha (f a₀)⟩
    

theorem Filter.Tendsto.exists_forall_le {α β : Type _} [Nonempty α] [LinearOrderₓ β] {f : α → β}
    (hf : tendsto f cofinite at_top) : ∃ a₀, ∀ a, f a₀ ≤ f a :=
  let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty
  ⟨a₀, fun a => ha₀ a (mem_univ _)⟩

theorem Filter.Tendsto.exists_within_forall_ge {α β : Type _} [LinearOrderₓ β] {s : Set α} (hs : s.nonempty) {f : α → β}
    (hf : Filter.Tendsto f Filter.cofinite Filter.atBot) : ∃ a₀ ∈ s, ∀, ∀ a ∈ s, ∀, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_within_forall_le _ (OrderDual β) _ _ hs _ hf

theorem Filter.Tendsto.exists_forall_ge {α β : Type _} [Nonempty α] [LinearOrderₓ β] {f : α → β}
    (hf : tendsto f cofinite at_bot) : ∃ a₀, ∀ a, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_forall_le _ (OrderDual β) _ _ _ hf

/-- For an injective function `f`, inverse images of finite sets are finite. -/
theorem Function.Injective.tendsto_cofinite {α β : Type _} {f : α → β} (hf : Function.Injective f) :
    tendsto f cofinite cofinite := fun s h => h.preimage (hf.inj_on _)

