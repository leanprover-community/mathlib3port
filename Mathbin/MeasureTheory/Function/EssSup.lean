import Mathbin.MeasureTheory.Measure.MeasureSpace 
import Mathbin.Order.Filter.Ennreal

/-!
# Essential supremum and infimum
We define the essential supremum and infimum of a function `f : α → β` with respect to a measure
`μ` on `α`. The essential supremum is the infimum of the constants `c : β` such that `f x ≤ c`
almost everywhere.

TODO: The essential supremum of functions `α → ℝ≥0∞` is used in particular to define the norm in
the `L∞` space (see measure_theory/lp_space.lean).

There is a different quantity which is sometimes also called essential supremum: the least
upper-bound among measurable functions of a family of measurable functions (in an almost-everywhere
sense). We do not define that quantity here, which is simply the supremum of a map with values in
`α →ₘ[μ] β` (see measure_theory/ae_eq_fun.lean).

## Main definitions

* `ess_sup f μ := μ.ae.limsup f`
* `ess_inf f μ := μ.ae.liminf f`
-/


open MeasureTheory Filter

open_locale Ennreal MeasureTheory

variable {α β : Type _} {m : MeasurableSpace α} {μ ν : Measureₓ α}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice β]

/-- Essential supremum of `f` with respect to measure `μ`: the smallest `c : β` such that
`f x ≤ c` a.e. -/
def essSup {m : MeasurableSpace α} (f : α → β) (μ : Measureₓ α) :=
  μ.ae.limsup f

/-- Essential infimum of `f` with respect to measure `μ`: the greatest `c : β` such that
`c ≤ f x` a.e. -/
def essInf {m : MeasurableSpace α} (f : α → β) (μ : Measureₓ α) :=
  μ.ae.liminf f

theorem ess_sup_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : essSup f μ = essSup g μ :=
  limsup_congr hfg

theorem ess_inf_congr_ae {f g : α → β} (hfg : f =ᵐ[μ] g) : essInf f μ = essInf g μ :=
  @ess_sup_congr_ae α (OrderDual β) _ _ _ _ _ hfg

end ConditionallyCompleteLattice

section CompleteLattice

variable [CompleteLattice β]

@[simp]
theorem ess_sup_measure_zero {m : MeasurableSpace α} {f : α → β} : essSup f (0 : Measureₓ α) = ⊥ :=
  le_bot_iff.mp
    (Inf_le
      (by 
        simp [Set.mem_set_of_eq, eventually_le, ae_iff]))

@[simp]
theorem ess_inf_measure_zero {m : MeasurableSpace α} {f : α → β} : essInf f (0 : Measureₓ α) = ⊤ :=
  @ess_sup_measure_zero α (OrderDual β) _ _ _

theorem ess_sup_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : essSup f μ ≤ essSup g μ :=
  limsup_le_limsup hfg

theorem ess_inf_mono_ae {f g : α → β} (hfg : f ≤ᵐ[μ] g) : essInf f μ ≤ essInf g μ :=
  liminf_le_liminf hfg

-- error in MeasureTheory.Function.EssSup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ess_sup_const (c : β) (hμ : «expr ≠ »(μ, 0)) : «expr = »(ess_sup (λ x : α, c) μ, c) :=
begin
  haveI [ident hμ_ne_bot] [":", expr μ.ae.ne_bot] [],
  { rwa ["[", expr ne_bot_iff, ",", expr ne.def, ",", expr ae_eq_bot, "]"] [] },
  exact [expr limsup_const c]
end

theorem ess_sup_le_of_ae_le {f : α → β} (c : β) (hf : f ≤ᵐ[μ] fun _ => c) : essSup f μ ≤ c :=
  by 
    refine' (ess_sup_mono_ae hf).trans _ 
    byCases' hμ : μ = 0
    ·
      simp [hμ]
    ·
      rwa [ess_sup_const]

theorem ess_inf_const (c : β) (hμ : μ ≠ 0) : essInf (fun x : α => c) μ = c :=
  @ess_sup_const α (OrderDual β) _ _ _ _ hμ

theorem le_ess_inf_of_ae_le {f : α → β} (c : β) (hf : (fun _ => c) ≤ᵐ[μ] f) : c ≤ essInf f μ :=
  @ess_sup_le_of_ae_le α (OrderDual β) _ _ _ _ c hf

theorem ess_sup_const_bot : essSup (fun x : α => (⊥ : β)) μ = (⊥ : β) :=
  limsup_const_bot

theorem ess_inf_const_top : essInf (fun x : α => (⊤ : β)) μ = (⊤ : β) :=
  liminf_const_top

theorem OrderIso.ess_sup_apply {m : MeasurableSpace α} {γ} [CompleteLattice γ] (f : α → β) (μ : Measureₓ α)
  (g : β ≃o γ) : g (essSup f μ) = essSup (fun x => g (f x)) μ :=
  by 
    refine' OrderIso.limsup_apply g _ _ _ _ 
    all_goals 
      runTac 
        is_bounded_default

theorem OrderIso.ess_inf_apply {m : MeasurableSpace α} {γ} [CompleteLattice γ] (f : α → β) (μ : Measureₓ α)
  (g : β ≃o γ) : g (essInf f μ) = essInf (fun x => g (f x)) μ :=
  @OrderIso.ess_sup_apply α (OrderDual β) _ _ (OrderDual γ) _ _ _ g.dual

theorem ess_sup_mono_measure {f : α → β} (hμν : ν ≪ μ) : essSup f ν ≤ essSup f μ :=
  by 
    refine' limsup_le_limsup_of_le (measure.ae_le_iff_absolutely_continuous.mpr hμν) _ _ 
    all_goals 
      runTac 
        is_bounded_default

theorem ess_inf_antitone_measure {f : α → β} (hμν : μ ≪ ν) : essInf f ν ≤ essInf f μ :=
  by 
    refine' liminf_le_liminf_of_le (measure.ae_le_iff_absolutely_continuous.mpr hμν) _ _ 
    all_goals 
      runTac 
        is_bounded_default

theorem ess_sup_smul_measure {f : α → β} {c : ℝ≥0∞} (hc : c ≠ 0) : essSup f (c • μ) = essSup f μ :=
  by 
    simpRw [essSup]
    suffices h_smul : (c • μ).ae = μ.ae
    ·
      rw [h_smul]
    ext1 
    simpRw [mem_ae_iff]
    simp [hc]

end CompleteLattice

section CompleteLinearOrder

variable [CompleteLinearOrder β]

theorem ae_lt_of_ess_sup_lt {f : α → β} {x : β} (hf : essSup f μ < x) : ∀ᵐy ∂μ, f y < x :=
  Filter.eventually_lt_of_limsup_lt hf

theorem ae_lt_of_lt_ess_inf {f : α → β} {x : β} (hf : x < essInf f μ) : ∀ᵐy ∂μ, x < f y :=
  @ae_lt_of_ess_sup_lt α (OrderDual β) _ _ _ _ _ hf

-- error in MeasureTheory.Function.EssSup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ess_sup_indicator_eq_ess_sup_restrict
[has_zero β]
{s : set α}
{f : α → β}
(hf : «expr ≤ᵐ[ ] »(0, μ.restrict s, f))
(hs : measurable_set s)
(hs_not_null : «expr ≠ »(μ s, 0)) : «expr = »(ess_sup (s.indicator f) μ, ess_sup f (μ.restrict s)) :=
begin
  refine [expr le_antisymm _ (Limsup_le_Limsup_of_le (map_restrict_ae_le_map_indicator_ae hs) (by is_bounded_default) (by is_bounded_default))],
  refine [expr Limsup_le_Limsup (by is_bounded_default) (by is_bounded_default) (λ c h_restrict_le, _)],
  rw [expr eventually_map] ["at", ident h_restrict_le, "⊢"],
  rw [expr ae_restrict_iff' hs] ["at", ident h_restrict_le],
  have [ident hc] [":", expr «expr ≤ »(0, c)] [],
  { suffices [] [":", expr «expr∃ , »((x), «expr ∧ »(«expr ≤ »(0, f x), «expr ≤ »(f x, c)))],
    by { obtain ["⟨", ident x, ",", ident hx, "⟩", ":=", expr this],
      exact [expr hx.1.trans hx.2] },
    refine [expr frequently.exists _],
    { exact [expr μ.ae] },
    rw ["[", expr eventually_le, ",", expr ae_restrict_iff' hs, "]"] ["at", ident hf],
    have [ident hs'] [":", expr «expr∃ᵐ ∂ , »((x), μ, «expr ∈ »(x, s))] [],
    { contrapose ["!"] [ident hs_not_null],
      rw ["[", expr not_frequently, ",", expr ae_iff, "]"] ["at", ident hs_not_null],
      suffices [] [":", expr «expr = »({a : α | «expr¬ »(«expr ∉ »(a, s))}, s)],
      by rwa ["<-", expr this] [],
      simp [] [] [] [] [] [] },
    refine [expr hs'.mp (hf.mp (h_restrict_le.mono (λ x hxs_imp_c hxf_nonneg hxs, _)))],
    rw [expr pi.zero_apply] ["at", ident hxf_nonneg],
    exact [expr ⟨hxf_nonneg hxs, hxs_imp_c hxs⟩] },
  refine [expr h_restrict_le.mono (λ x hxc, _)],
  by_cases [expr hxs, ":", expr «expr ∈ »(x, s)],
  { simpa [] [] [] ["[", expr hxs, "]"] [] ["using", expr hxc hxs] },
  { simpa [] [] [] ["[", expr hxs, "]"] [] ["using", expr hc] }
end

end CompleteLinearOrder

namespace Ennreal

variable {f : α → ℝ≥0∞}

theorem ae_le_ess_sup (f : α → ℝ≥0∞) : ∀ᵐy ∂μ, f y ≤ essSup f μ :=
  eventually_le_limsup f

@[simp]
theorem ess_sup_eq_zero_iff : essSup f μ = 0 ↔ f =ᵐ[μ] 0 :=
  limsup_eq_zero_iff

theorem ess_sup_const_mul {a : ℝ≥0∞} : essSup (fun x : α => a*f x) μ = a*essSup f μ :=
  limsup_const_mul

theorem ess_sup_add_le (f g : α → ℝ≥0∞) : essSup (f+g) μ ≤ essSup f μ+essSup g μ :=
  limsup_add_le f g

theorem ess_sup_liminf_le {ι} [Encodable ι] [LinearOrderₓ ι] (f : ι → α → ℝ≥0∞) :
  essSup (fun x => at_top.liminf fun n => f n x) μ ≤ at_top.liminf fun n => essSup (fun x => f n x) μ :=
  by 
    simpRw [essSup]
    exact Ennreal.limsup_liminf_le_liminf_limsup fun a b => f b a

end Ennreal

