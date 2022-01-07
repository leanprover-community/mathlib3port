import Mathbin.Algebra.IndicatorFunction
import Mathbin.Order.Filter.AtTopBot

/-!
# Indicator function and filters

Properties of indicator functions involving `=ᶠ` and `≤ᶠ`.

## Tags
indicator, characteristic, filter
-/


variable {α β M E : Type _}

open Set Filter Classical

open_locale Filter Classical

section HasZero

variable [HasZero M] {s t : Set α} {f g : α → M} {a : α} {l : Filter α}

theorem indicator_eventually_eq (hf : f =ᶠ[l⊓𝓟 s] g) (hs : s =ᶠ[l] t) : indicator s f =ᶠ[l] indicator t g :=
  (eventually_inf_principal.1 hf).mp $
    hs.mem_iff.mono $ fun x hst hfg =>
      by_cases
        (fun hxs : x ∈ s => by
          simp only [*, hst.1 hxs, indicator_of_mem])
        fun hxs => by
        simp only [indicator_of_not_mem hxs, indicator_of_not_mem (mt hst.2 hxs)]

end HasZero

section AddMonoidₓ

variable [AddMonoidₓ M] {s t : Set α} {f g : α → M} {a : α} {l : Filter α}

theorem indicator_union_eventually_eq (h : ∀ᶠ a in l, a ∉ s ∩ t) :
    indicator (s ∪ t) f =ᶠ[l] indicator s f + indicator t f :=
  h.mono $ fun a ha => indicator_union_of_not_mem_inter ha _

end AddMonoidₓ

section Order

variable [HasZero β] [Preorderₓ β] {s t : Set α} {f g : α → β} {a : α} {l : Filter α}

theorem indicator_eventually_le_indicator (h : f ≤ᶠ[l⊓𝓟 s] g) : indicator s f ≤ᶠ[l] indicator s g :=
  (eventually_inf_principal.1 h).mono $ fun a h => indicator_rel_indicator (le_reflₓ _) h

end Order

theorem Monotone.tendsto_indicator {ι} [Preorderₓ ι] [HasZero β] (s : ι → Set α) (hs : Monotone s) (f : α → β) (a : α) :
    tendsto (fun i => indicator (s i) f a) at_top (pure $ indicator (⋃ i, s i) f a) := by
  by_cases' h : ∃ i, a ∈ s i
  · rcases h with ⟨i, hi⟩
    refine' tendsto_pure.2 ((eventually_ge_at_top i).mono $ fun n hn => _)
    rw [indicator_of_mem (hs hn hi) _, indicator_of_mem ((subset_Union _ _) hi) _]
    
  · rw [not_exists] at h
    simp only [indicator_of_not_mem (h _)]
    convert tendsto_const_pure
    apply indicator_of_not_mem
    simpa only [not_exists, mem_Union]
    

theorem Antitone.tendsto_indicator {ι} [Preorderₓ ι] [HasZero β] (s : ι → Set α) (hs : Antitone s) (f : α → β) (a : α) :
    tendsto (fun i => indicator (s i) f a) at_top (pure $ indicator (⋂ i, s i) f a) := by
  by_cases' h : ∃ i, a ∉ s i
  · rcases h with ⟨i, hi⟩
    refine' tendsto_pure.2 ((eventually_ge_at_top i).mono $ fun n hn => _)
    rw [indicator_of_not_mem _ _, indicator_of_not_mem _ _]
    · simp only [mem_Inter, not_forall]
      exact ⟨i, hi⟩
      
    · intro h
      have := hs hn h
      contradiction
      
    
  · push_neg  at h
    simp only [indicator_of_mem, h, mem_Inter.2 h, tendsto_const_pure]
    

theorem tendsto_indicator_bUnion_finset {ι} [HasZero β] (s : ι → Set α) (f : α → β) (a : α) :
    tendsto (fun n : Finset ι => indicator (⋃ i ∈ n, s i) f a) at_top (pure $ indicator (Union s) f a) := by
  rw [Union_eq_Union_finset s]
  refine' Monotone.tendsto_indicator (fun n : Finset ι => ⋃ i ∈ n, s i) _ f a
  exact fun t₁ t₂ => bUnion_subset_bUnion_left

