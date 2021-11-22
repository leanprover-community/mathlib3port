import Mathbin.Order.Filter.AtTopBot

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

variable{α : Type _}

namespace Filter

/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite : Filter α :=
  { Sets := { s | finite («expr ᶜ» s) },
    univ_sets :=
      by 
        simp only [compl_univ, finite_empty, mem_set_of_eq],
    sets_of_superset := fun s t hs : finite («expr ᶜ» s) st : s ⊆ t => hs.subset$ compl_subset_compl.2 st,
    inter_sets :=
      fun s t hs : finite («expr ᶜ» s) ht : finite («expr ᶜ» t) =>
        by 
          simp only [compl_inter, finite.union, ht, hs, mem_set_of_eq] }

@[simp]
theorem mem_cofinite {s : Set α} : s ∈ @cofinite α ↔ finite («expr ᶜ» s) :=
  Iff.rfl

@[simp]
theorem eventually_cofinite {p : α → Prop} : (∀ᶠx in cofinite, p x) ↔ finite { x | ¬p x } :=
  Iff.rfl

instance cofinite_ne_bot [Infinite α] : ne_bot (@cofinite α) :=
  ⟨mt empty_mem_iff_bot.mpr$
      by 
        simp only [mem_cofinite, compl_empty]
        exact infinite_univ⟩

theorem frequently_cofinite_iff_infinite {p : α → Prop} : (∃ᶠx in cofinite, p x) ↔ Set.Infinite { x | p x } :=
  by 
    simp only [Filter.Frequently, Filter.Eventually, mem_cofinite, compl_set_of, not_not, Set.Infinite]

/-- The coproduct of the cofinite filters on two types is the cofinite filter on their product. -/
theorem coprod_cofinite {β : Type _} : (cofinite : Filter α).coprod (cofinite : Filter β) = cofinite :=
  by 
    ext S 
    simp only [mem_coprod_iff, exists_prop, mem_comap, mem_cofinite]
    split 
    ·
      rintro ⟨⟨A, hAf, hAS⟩, B, hBf, hBS⟩
      rw [←compl_subset_compl, ←preimage_compl] at hAS hBS 
      exact (hAf.prod hBf).Subset (subset_inter hAS hBS)
    ·
      intro hS 
      refine' ⟨⟨«expr ᶜ» (Prod.fst '' «expr ᶜ» S), _, _⟩, ⟨«expr ᶜ» (Prod.snd '' «expr ᶜ» S), _, _⟩⟩
      ·
        simpa using hS.image Prod.fst
      ·
        simpa [compl_subset_comm] using subset_preimage_image Prod.fst («expr ᶜ» S)
      ·
        simpa using hS.image Prod.snd
      ·
        simpa [compl_subset_comm] using subset_preimage_image Prod.snd («expr ᶜ» S)

/-- Finite product of finite sets is finite -/
theorem Coprod_cofinite {δ : Type _} {κ : δ → Type _} [Fintype δ] :
  (Filter.coprodₓ fun d => (cofinite : Filter (κ d))) = cofinite :=
  by 
    ext S 
    simp only [mem_coprod_iff, exists_prop, mem_comap, mem_cofinite]
    split 
    ·
      rintro h 
      rw [mem_Coprod_iff] at h 
      choose t ht1 ht2 using h 
      have ht1d : ∀ d : δ, («expr ᶜ» (t d)).Finite := fun d => mem_cofinite.mp (ht1 d)
      refine' (Set.Finite.pi ht1d).Subset _ 
      have ht2d : ∀ d : δ, «expr ᶜ» S ⊆ (fun k : ∀ d1 : δ, (fun d2 : δ => κ d2) d1 => k d) ⁻¹' «expr ᶜ» (t d) :=
        fun d => compl_subset_compl.mpr (ht2 d)
      convert Set.subset_Inter ht2d 
      ext 
      simp 
    ·
      intro hS 
      rw [mem_Coprod_iff]
      intro d 
      refine' ⟨«expr ᶜ» ((fun k : ∀ d1 : δ, κ d1 => k d) '' «expr ᶜ» S), _, _⟩
      ·
        rw [mem_cofinite, compl_compl]
        exact Set.Finite.image _ hS
      ·
        intro x 
        contrapose 
        intro hx 
        simp only [not_not, mem_preimage, mem_compl_eq, not_forall]
        exact ⟨x, hx, rfl⟩

end Filter

open Filter

theorem Set.Finite.compl_mem_cofinite {s : Set α} (hs : s.finite) : «expr ᶜ» s ∈ @cofinite α :=
  mem_cofinite.2$ (compl_compl s).symm ▸ hs

theorem Set.Finite.eventually_cofinite_nmem {s : Set α} (hs : s.finite) : ∀ᶠx in cofinite, x ∉ s :=
  hs.compl_mem_cofinite

theorem Finset.eventually_cofinite_nmem (s : Finset α) : ∀ᶠx in cofinite, x ∉ s :=
  s.finite_to_set.eventually_cofinite_nmem

theorem Set.infinite_iff_frequently_cofinite {s : Set α} : Set.Infinite s ↔ ∃ᶠx in cofinite, x ∈ s :=
  frequently_cofinite_iff_infinite.symm

theorem Filter.eventually_cofinite_ne (x : α) : ∀ᶠa in cofinite, a ≠ x :=
  (Set.finite_singleton x).eventually_cofinite_nmem

-- error in Order.Filter.Cofinite: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contradiction: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- For natural numbers the filters `cofinite` and `at_top` coincide. -/
theorem nat.cofinite_eq_at_top : «expr = »(@cofinite exprℕ(), at_top) :=
begin
  ext [] [ident s] [],
  simp [] [] ["only"] ["[", expr mem_cofinite, ",", expr mem_at_top_sets, "]"] [] [],
  split,
  { assume [binders (hs)],
    use [expr «expr + »(hs.to_finset.sup id, 1)],
    assume [binders (b hb)],
    by_contradiction [ident hbs],
    have [] [] [":=", expr hs.to_finset.subset_range_sup_succ (hs.mem_to_finset.2 hbs)],
    exact [expr not_lt_of_le hb (finset.mem_range.1 this)] },
  { rintros ["⟨", ident N, ",", ident hN, "⟩"],
    apply [expr (finite_lt_nat N).subset],
    assume [binders (n hn)],
    change [expr «expr < »(n, N)] [] [],
    exact [expr lt_of_not_ge (λ hn', «expr $ »(hn, hN n hn'))] }
end

theorem Nat.frequently_at_top_iff_infinite {p : ℕ → Prop} : (∃ᶠn in at_top, p n) ↔ Set.Infinite { n | p n } :=
  by 
    simp only [←Nat.cofinite_eq_at_top, frequently_cofinite_iff_infinite]

theorem Filter.Tendsto.exists_within_forall_le {α β : Type _} [LinearOrderₓ β] {s : Set α} (hs : s.nonempty) {f : α → β}
  (hf : Filter.Tendsto f Filter.cofinite Filter.atTop) : ∃ (a₀ : _)(_ : a₀ ∈ s), ∀ a _ : a ∈ s, f a₀ ≤ f a :=
  by 
    rcases em (∃ (y : _)(_ : y ∈ s), ∃ x, f y < x) with (⟨y, hys, x, hx⟩ | not_all_top)
    ·
      have  : finite { y | ¬x ≤ f y } := filter.eventually_cofinite.mp (tendsto_at_top.1 hf x)
      simp only [not_leₓ] at this 
      obtain ⟨a₀, ⟨ha₀ : f a₀ < x, ha₀s⟩, others_bigger⟩ := exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩
      refine' ⟨a₀, ha₀s, fun a has => (lt_or_leₓ (f a) x).elim _ (le_transₓ ha₀.le)⟩
      exact fun h => others_bigger a ⟨h, has⟩
    ·
      pushNeg  at not_all_top 
      obtain ⟨a₀, ha₀s⟩ := hs 
      exact ⟨a₀, ha₀s, fun a ha => not_all_top a ha (f a₀)⟩

theorem Filter.Tendsto.exists_forall_le {α β : Type _} [Nonempty α] [LinearOrderₓ β] {f : α → β}
  (hf : tendsto f cofinite at_top) : ∃ a₀, ∀ a, f a₀ ≤ f a :=
  let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty
  ⟨a₀, fun a => ha₀ a (mem_univ _)⟩

theorem Filter.Tendsto.exists_within_forall_ge {α β : Type _} [LinearOrderₓ β] {s : Set α} (hs : s.nonempty) {f : α → β}
  (hf : Filter.Tendsto f Filter.cofinite Filter.atBot) : ∃ (a₀ : _)(_ : a₀ ∈ s), ∀ a _ : a ∈ s, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_within_forall_le _ (OrderDual β) _ _ hs _ hf

theorem Filter.Tendsto.exists_forall_ge {α β : Type _} [Nonempty α] [LinearOrderₓ β] {f : α → β}
  (hf : tendsto f cofinite at_bot) : ∃ a₀, ∀ a, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_forall_le _ (OrderDual β) _ _ _ hf

/-- For an injective function `f`, inverse images of finite sets are finite. -/
theorem Function.Injective.tendsto_cofinite {α β : Type _} {f : α → β} (hf : Function.Injective f) :
  tendsto f cofinite cofinite :=
  fun s h => h.preimage (hf.inj_on _)

