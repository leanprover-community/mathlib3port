import Mathbin.Algebra.IndicatorFunction 
import Mathbin.Order.Filter.AtTopBot

/-!
# Indicator function and filters

Properties of indicator functions involving `=ᶠ` and `≤ᶠ`.

## Tags
indicator, characteristic, filter
-/


variable{α β M E : Type _}

open Set Filter Classical

open_locale Filter Classical

section HasZero

variable[HasZero M]{s t : Set α}{f g : α → M}{a : α}{l : Filter α}

-- error in Order.Filter.IndicatorFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem indicator_eventually_eq
(hf : «expr =ᶠ[ ] »(f, «expr ⊓ »(l, expr𝓟() s), g))
(hs : «expr =ᶠ[ ] »(s, l, t)) : «expr =ᶠ[ ] »(indicator s f, l, indicator t g) :=
«expr $ »((eventually_inf_principal.1 hf).mp, «expr $ »(hs.mem_iff.mono, λ
  x
  hst
  hfg, by_cases (λ
   hxs : «expr ∈ »(x, s), by simp [] [] ["only"] ["[", "*", ",", expr hst.1 hxs, ",", expr indicator_of_mem, "]"] [] []) (λ
   hxs, by simp [] [] ["only"] ["[", expr indicator_of_not_mem hxs, ",", expr indicator_of_not_mem (mt hst.2 hxs), "]"] [] [])))

end HasZero

section AddMonoidₓ

variable[AddMonoidₓ M]{s t : Set α}{f g : α → M}{a : α}{l : Filter α}

theorem indicator_union_eventually_eq (h : ∀ᶠa in l, a ∉ s ∩ t) :
  indicator (s ∪ t) f =ᶠ[l] indicator s f+indicator t f :=
  h.mono$ fun a ha => indicator_union_of_not_mem_inter ha _

end AddMonoidₓ

section Order

variable[HasZero β][Preorderₓ β]{s t : Set α}{f g : α → β}{a : α}{l : Filter α}

theorem indicator_eventually_le_indicator (h : f ≤ᶠ[l⊓𝓟 s] g) : indicator s f ≤ᶠ[l] indicator s g :=
  (eventually_inf_principal.1 h).mono$ fun a h => indicator_rel_indicator (le_reflₓ _) h

end Order

theorem Monotone.tendsto_indicator {ι} [Preorderₓ ι] [HasZero β] (s : ι → Set α) (hs : Monotone s) (f : α → β) (a : α) :
  tendsto (fun i => indicator (s i) f a) at_top (pure$ indicator (⋃i, s i) f a) :=
  by 
    byCases' h : ∃ i, a ∈ s i
    ·
      rcases h with ⟨i, hi⟩
      refine' tendsto_pure.2 ((eventually_ge_at_top i).mono$ fun n hn => _)
      rw [indicator_of_mem (hs hn hi) _, indicator_of_mem ((subset_Union _ _) hi) _]
    ·
      rw [not_exists] at h 
      simp only [indicator_of_not_mem (h _)]
      convert tendsto_const_pure 
      apply indicator_of_not_mem 
      simpa only [not_exists, mem_Union]

-- error in Order.Filter.IndicatorFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem antitone.tendsto_indicator
{ι}
[preorder ι]
[has_zero β]
(s : ι → set α)
(hs : antitone s)
(f : α → β)
(a : α) : tendsto (λ i, indicator (s i) f a) at_top «expr $ »(pure, indicator «expr⋂ , »((i), s i) f a) :=
begin
  by_cases [expr h, ":", expr «expr∃ , »((i), «expr ∉ »(a, s i))],
  { rcases [expr h, "with", "⟨", ident i, ",", ident hi, "⟩"],
    refine [expr tendsto_pure.2 «expr $ »((eventually_ge_at_top i).mono, assume n hn, _)],
    rw ["[", expr indicator_of_not_mem _ _, ",", expr indicator_of_not_mem _ _, "]"] [],
    { simp [] [] ["only"] ["[", expr mem_Inter, ",", expr not_forall, "]"] [] [],
      exact [expr ⟨i, hi⟩] },
    { assume [binders (h)],
      have [] [] [":=", expr hs hn h],
      contradiction } },
  { push_neg ["at", ident h],
    simp [] [] ["only"] ["[", expr indicator_of_mem, ",", expr h, ",", expr mem_Inter.2 h, ",", expr tendsto_const_pure, "]"] [] [] }
end

-- error in Order.Filter.IndicatorFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_indicator_bUnion_finset
{ι}
[has_zero β]
(s : ι → set α)
(f : α → β)
(a : α) : tendsto (λ
 n : finset ι, indicator «expr⋃ , »((i «expr ∈ » n), s i) f a) at_top «expr $ »(pure, indicator (Union s) f a) :=
begin
  rw [expr Union_eq_Union_finset s] [],
  refine [expr monotone.tendsto_indicator (λ n : finset ι, «expr⋃ , »((i «expr ∈ » n), s i)) _ f a],
  exact [expr λ t₁ t₂, bUnion_subset_bUnion_left]
end

