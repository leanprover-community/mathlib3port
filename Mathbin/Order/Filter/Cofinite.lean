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

variable{α : Type _}

namespace Filter

-- error in Order.Filter.Cofinite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The cofinite filter is the filter of subsets whose complements are finite. -/ def cofinite : filter α :=
{ sets := {s | finite «expr ᶜ»(s)},
  univ_sets := by simp [] [] ["only"] ["[", expr compl_univ, ",", expr finite_empty, ",", expr mem_set_of_eq, "]"] [] [],
  sets_of_superset := assume
  (s t)
  (hs : finite «expr ᶜ»(s))
  (st : «expr ⊆ »(s, t)), «expr $ »(hs.subset, compl_subset_compl.2 st),
  inter_sets := assume
  (s t)
  (hs : finite «expr ᶜ»(s))
  (ht : finite «expr ᶜ»(t)), by simp [] [] ["only"] ["[", expr compl_inter, ",", expr finite.union, ",", expr ht, ",", expr hs, ",", expr mem_set_of_eq, "]"] [] [] }

@[simp]
theorem mem_cofinite {s : Set α} : s ∈ @cofinite α ↔ finite («expr ᶜ» s) :=
  Iff.rfl

@[simp]
theorem eventually_cofinite {p : α → Prop} : (∀ᶠx in cofinite, p x) ↔ finite { x | ¬p x } :=
  Iff.rfl

-- error in Order.Filter.Cofinite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_basis_cofinite : has_basis cofinite (λ s : set α, s.finite) compl :=
⟨λ s, ⟨λ h, ⟨«expr ᶜ»(s), h, (compl_compl s).subset⟩, λ ⟨t, htf, hts⟩, «expr $ »(htf.subset, compl_subset_comm.2 hts)⟩⟩

instance cofinite_ne_bot [Infinite α] : ne_bot (@cofinite α) :=
  has_basis_cofinite.ne_bot_iff.2$ fun s hs => hs.infinite_compl.nonempty

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
    rcases compl_surjective S with ⟨S, rfl⟩
    simpRw [compl_mem_Coprod_iff, mem_cofinite, compl_compl]
    split 
    ·
      rintro ⟨t, htf, hsub⟩
      exact (finite.pi htf).Subset hsub
    ·
      exact fun hS => ⟨fun i => Function.eval i '' S, fun i => hS.image _, subset_pi_eval_image _ _⟩

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

-- error in Order.Filter.Cofinite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
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

-- error in Order.Filter.Cofinite: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem filter.tendsto.exists_within_forall_le
{α β : Type*}
[linear_order β]
{s : set α}
(hs : s.nonempty)
{f : α → β}
(hf : filter.tendsto f filter.cofinite filter.at_top) : «expr∃ , »((a₀ «expr ∈ » s), ∀
 a «expr ∈ » s, «expr ≤ »(f a₀, f a)) :=
begin
  rcases [expr em «expr∃ , »((y «expr ∈ » s), «expr∃ , »((x), «expr < »(f y, x))), "with", "⟨", ident y, ",", ident hys, ",", ident x, ",", ident hx, "⟩", "|", ident not_all_top],
  { have [] [":", expr finite {y | «expr¬ »(«expr ≤ »(x, f y))}] [":=", expr filter.eventually_cofinite.mp (tendsto_at_top.1 hf x)],
    simp [] [] ["only"] ["[", expr not_le, "]"] [] ["at", ident this],
    obtain ["⟨", ident a₀, ",", "⟨", ident ha₀, ":", expr «expr < »(f a₀, x), ",", ident ha₀s, "⟩", ",", ident others_bigger, "⟩", ":=", expr exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩],
    refine [expr ⟨a₀, ha₀s, λ a has, (lt_or_le (f a) x).elim _ (le_trans ha₀.le)⟩],
    exact [expr λ h, others_bigger a ⟨h, has⟩] },
  { push_neg ["at", ident not_all_top],
    obtain ["⟨", ident a₀, ",", ident ha₀s, "⟩", ":=", expr hs],
    exact [expr ⟨a₀, ha₀s, λ a ha, not_all_top a ha (f a₀)⟩] }
end

theorem Filter.Tendsto.exists_forall_le {α β : Type _} [Nonempty α] [LinearOrderₓ β] {f : α → β}
  (hf : tendsto f cofinite at_top) : ∃ a₀, ∀ a, f a₀ ≤ f a :=
  let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty
  ⟨a₀, fun a => ha₀ a (mem_univ _)⟩

theorem Filter.Tendsto.exists_within_forall_ge {α β : Type _} [LinearOrderₓ β] {s : Set α} (hs : s.nonempty) {f : α → β}
  (hf : Filter.Tendsto f Filter.cofinite Filter.atBot) : ∃ (a₀ : _)(_ : a₀ ∈ s), ∀ a (_ : a ∈ s), f a ≤ f a₀ :=
  @Filter.Tendsto.exists_within_forall_le _ (OrderDual β) _ _ hs _ hf

theorem Filter.Tendsto.exists_forall_ge {α β : Type _} [Nonempty α] [LinearOrderₓ β] {f : α → β}
  (hf : tendsto f cofinite at_bot) : ∃ a₀, ∀ a, f a ≤ f a₀ :=
  @Filter.Tendsto.exists_forall_le _ (OrderDual β) _ _ _ hf

/-- For an injective function `f`, inverse images of finite sets are finite. -/
theorem Function.Injective.tendsto_cofinite {α β : Type _} {f : α → β} (hf : Function.Injective f) :
  tendsto f cofinite cofinite :=
  fun s h => h.preimage (hf.inj_on _)

