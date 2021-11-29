import Mathbin.MeasureTheory.Integral.IntervalIntegral 
import Mathbin.Order.Filter.AtTopBot

/-!
# Links between an integral and its "improper" version

In its current state, mathlib only knows how to talk about definite ("proper") integrals,
in the sense that it treats integrals over `[x, +∞)` the same as it treats integrals over
`[y, z]`. For example, the integral over `[1, +∞)` is **not** defined to be the limit of
the integral over `[1, x]` as `x` tends to `+∞`, which is known as an **improper integral**.

Indeed, the "proper" definition is stronger than the "improper" one. The usual counterexample
is `x ↦ sin(x)/x`, which has an improper integral over `[1, +∞)` but no definite integral.

Although definite integrals have better properties, they are hardly usable when it comes to
computing integrals on unbounded sets, which is much easier using limits. Thus, in this file,
we prove various ways of studying the proper integral by studying the improper one.

## Definitions

The main definition of this file is `measure_theory.ae_cover`. It is a rather technical
definition whose sole purpose is generalizing and factoring proofs. Given an index type `ι`, a
countably generated filter `l` over `ι`, and an `ι`-indexed family `φ` of subsets of a measurable
space `α` equipped with a measure `μ`, one should think of a hypothesis `hφ : ae_cover μ l φ` as
a sufficient condition for being able to interpret `∫ x, f x ∂μ` (if it exists) as the limit
of `∫ x in φ i, f x ∂μ` as `i` tends to `l`.

When using this definition with a measure restricted to a set `s`, which happens fairly often,
one should not try too hard to use a `ae_cover` of subsets of `s`, as it often makes proofs
more complicated than necessary. See for example the proof of
`measure_theory.integrable_on_Iic_of_interval_integral_norm_tendsto` where we use `(λ x, Ioi x)`
as an `ae_cover` w.r.t. `μ.restrict (Iic b)`, instead of using `(λ x, Ioc x b)`.

## Main statements

- `measure_theory.ae_cover.lintegral_tendsto_of_countably_generated` : if `φ` is a `ae_cover μ l`,
  where `l` is a countably generated filter, and if `f` is a measurable `ennreal`-valued function,
  then `∫⁻ x in φ n, f x ∂μ` tends to `∫⁻ x, f x ∂μ` as `n` tends to `l`
- `measure_theory.ae_cover.integrable_of_integral_norm_tendsto` : if `φ` is a `ae_cover μ l`,
  where `l` is a countably generated filter, if `f` is measurable and integrable on each `φ n`,
  and if `∫ x in φ n, ∥f x∥ ∂μ` tends to some `I : ℝ` as n tends to `l`, then `f` is integrable
- `measure_theory.ae_cover.integral_tendsto_of_countably_generated` : if `φ` is a `ae_cover μ l`,
  where `l` is a countably generated filter, and if `f` is measurable and integrable (globally),
  then `∫ x in φ n, f x ∂μ` tends to `∫ x, f x ∂μ` as `n` tends to `+∞`.

We then specialize these lemmas to various use cases involving intervals, which are frequent
in analysis.
-/


open MeasureTheory Filter Set TopologicalSpace

open_locale Ennreal Nnreal TopologicalSpace

namespace MeasureTheory

section AeCover

variable{α ι : Type _}[MeasurableSpace α](μ : Measureₓ α)(l : Filter ι)

/-- A sequence `φ` of subsets of `α` is a `ae_cover` w.r.t. a measure `μ` and a filter `l`
    if almost every point (w.r.t. `μ`) of `α` eventually belongs to `φ n` (w.r.t. `l`), and if
    each `φ n` is measurable.
    This definition is a technical way to avoid duplicating a lot of proofs.
    It should be thought of as a sufficient condition for being able to interpret
    `∫ x, f x ∂μ` (if it exists) as the limit of `∫ x in φ n, f x ∂μ` as `n` tends to `l`.

    See for example `measure_theory.ae_cover.lintegral_tendsto_of_countably_generated`,
    `measure_theory.ae_cover.integrable_of_integral_norm_tendsto` and
    `measure_theory.ae_cover.integral_tendsto_of_countably_generated`. -/
structure ae_cover(φ : ι → Set α) : Prop where 
  ae_eventually_mem : ∀ᵐx ∂μ, ∀ᶠi in l, x ∈ φ i 
  Measurable : ∀ i, MeasurableSet$ φ i

variable{μ}{l}

section Preorderα

variable[Preorderₓ
      α][TopologicalSpace
      α][OrderClosedTopology α][OpensMeasurableSpace α]{a b : ι → α}(ha : tendsto a l at_bot)(hb : tendsto b l at_top)

theorem ae_cover_Icc : ae_cover μ l fun i => Icc (a i) (b i) :=
  { ae_eventually_mem :=
      ae_of_all μ
        fun x =>
          (ha.eventually$ eventually_le_at_bot x).mp$
            (hb.eventually$ eventually_ge_at_top x).mono$ fun i hbi hai => ⟨hai, hbi⟩,
    Measurable := fun i => measurable_set_Icc }

theorem ae_cover_Ici : ae_cover μ l fun i => Ici$ a i :=
  { ae_eventually_mem := ae_of_all μ fun x => (ha.eventually$ eventually_le_at_bot x).mono$ fun i hai => hai,
    Measurable := fun i => measurable_set_Ici }

theorem ae_cover_Iic : ae_cover μ l fun i => Iic$ b i :=
  { ae_eventually_mem := ae_of_all μ fun x => (hb.eventually$ eventually_ge_at_top x).mono$ fun i hbi => hbi,
    Measurable := fun i => measurable_set_Iic }

end Preorderα

section LinearOrderα

variable[LinearOrderₓ
      α][TopologicalSpace
      α][OrderClosedTopology α][OpensMeasurableSpace α]{a b : ι → α}(ha : tendsto a l at_bot)(hb : tendsto b l at_top)

theorem ae_cover_Ioo [NoBotOrder α] [NoTopOrder α] : ae_cover μ l fun i => Ioo (a i) (b i) :=
  { ae_eventually_mem :=
      ae_of_all μ
        fun x =>
          (ha.eventually$ eventually_lt_at_bot x).mp$
            (hb.eventually$ eventually_gt_at_top x).mono$ fun i hbi hai => ⟨hai, hbi⟩,
    Measurable := fun i => measurable_set_Ioo }

theorem ae_cover_Ioc [NoBotOrder α] : ae_cover μ l fun i => Ioc (a i) (b i) :=
  { ae_eventually_mem :=
      ae_of_all μ
        fun x =>
          (ha.eventually$ eventually_lt_at_bot x).mp$
            (hb.eventually$ eventually_ge_at_top x).mono$ fun i hbi hai => ⟨hai, hbi⟩,
    Measurable := fun i => measurable_set_Ioc }

theorem ae_cover_Ico [NoTopOrder α] : ae_cover μ l fun i => Ico (a i) (b i) :=
  { ae_eventually_mem :=
      ae_of_all μ
        fun x =>
          (ha.eventually$ eventually_le_at_bot x).mp$
            (hb.eventually$ eventually_gt_at_top x).mono$ fun i hbi hai => ⟨hai, hbi⟩,
    Measurable := fun i => measurable_set_Ico }

theorem ae_cover_Ioi [NoBotOrder α] : ae_cover μ l fun i => Ioi$ a i :=
  { ae_eventually_mem := ae_of_all μ fun x => (ha.eventually$ eventually_lt_at_bot x).mono$ fun i hai => hai,
    Measurable := fun i => measurable_set_Ioi }

theorem ae_cover_Iio [NoTopOrder α] : ae_cover μ l fun i => Iio$ b i :=
  { ae_eventually_mem := ae_of_all μ fun x => (hb.eventually$ eventually_gt_at_top x).mono$ fun i hbi => hbi,
    Measurable := fun i => measurable_set_Iio }

end LinearOrderα

theorem ae_cover.restrict {φ : ι → Set α} (hφ : ae_cover μ l φ) {s : Set α} : ae_cover (μ.restrict s) l φ :=
  { ae_eventually_mem := ae_restrict_of_ae hφ.ae_eventually_mem, Measurable := hφ.measurable }

theorem ae_cover_restrict_of_ae_imp {s : Set α} {φ : ι → Set α} (hs : MeasurableSet s)
  (ae_eventually_mem : ∀ᵐx ∂μ, x ∈ s → ∀ᶠn in l, x ∈ φ n) (measurable : ∀ n, MeasurableSet$ φ n) :
  ae_cover (μ.restrict s) l φ :=
  { ae_eventually_mem :=
      by 
        rwa [ae_restrict_iff' hs],
    Measurable }

theorem ae_cover.inter_restrict {φ : ι → Set α} (hφ : ae_cover μ l φ) {s : Set α} (hs : MeasurableSet s) :
  ae_cover (μ.restrict s) l fun i => φ i ∩ s :=
  ae_cover_restrict_of_ae_imp hs (hφ.ae_eventually_mem.mono fun x hx hxs => hx.mono$ fun i hi => ⟨hi, hxs⟩)
    fun i => (hφ.measurable i).inter hs

theorem ae_cover.ae_tendsto_indicator {β : Type _} [HasZero β] [TopologicalSpace β] {f : α → β} {φ : ι → Set α}
  (hφ : ae_cover μ l φ) : ∀ᵐx ∂μ, tendsto (fun i => (φ i).indicator f x) l (𝓝$ f x) :=
  hφ.ae_eventually_mem.mono fun x hx => tendsto_const_nhds.congr'$ hx.mono$ fun n hn => (indicator_of_mem hn _).symm

end AeCover

theorem ae_cover.comp_tendsto {α ι ι' : Type _} [MeasurableSpace α] {μ : Measureₓ α} {l : Filter ι} {l' : Filter ι'}
  {φ : ι → Set α} (hφ : ae_cover μ l φ) {u : ι' → ι} (hu : tendsto u l' l) : ae_cover μ l' (φ ∘ u) :=
  { ae_eventually_mem := hφ.ae_eventually_mem.mono fun x hx => hu.eventually hx,
    Measurable := fun i => hφ.measurable (u i) }

section AeCoverUnionInterEncodable

variable{α ι : Type _}[Encodable ι][MeasurableSpace α]{μ : Measureₓ α}

-- error in MeasureTheory.Integral.IntegralEqImproper: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem ae_cover.bUnion_Iic_ae_cover
[preorder ι]
{φ : ι → set α}
(hφ : ae_cover μ at_top φ) : ae_cover μ at_top (λ n : ι, «expr⋃ , »((k) (h : «expr ∈ »(k, Iic n)), φ k)) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono (λ x h, h.mono (λ i hi, mem_bUnion right_mem_Iic hi)),
  measurable := λ i, measurable_set.bUnion (countable_encodable _) (λ n _, hφ.measurable n) }

-- error in MeasureTheory.Integral.IntegralEqImproper: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem ae_cover.bInter_Ici_ae_cover
[semilattice_sup ι]
[nonempty ι]
{φ : ι → set α}
(hφ : ae_cover μ at_top φ) : ae_cover μ at_top (λ n : ι, «expr⋂ , »((k) (h : «expr ∈ »(k, Ici n)), φ k)) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono (begin
     intros [ident x, ident h],
     rw [expr eventually_at_top] ["at", "*"],
     rcases [expr h, "with", "⟨", ident i, ",", ident hi, "⟩"],
     use [expr i],
     intros [ident j, ident hj],
     exact [expr mem_bInter (λ k hk, hi k (le_trans hj hk))]
   end),
  measurable := λ i, measurable_set.bInter (countable_encodable _) (λ n _, hφ.measurable n) }

end AeCoverUnionInterEncodable

section Lintegral

variable{α ι : Type _}[MeasurableSpace α]{μ : Measureₓ α}{l : Filter ι}

private theorem lintegral_tendsto_of_monotone_of_nat {φ : ℕ → Set α} (hφ : ae_cover μ at_top φ) (hmono : Monotone φ)
  {f : α → ℝ≥0∞} (hfm : AeMeasurable f μ) : tendsto (fun i => ∫⁻x in φ i, f x ∂μ) at_top (𝓝$ ∫⁻x, f x ∂μ) :=
  let F := fun n => (φ n).indicator f 
  have key₁ : ∀ n, AeMeasurable (F n) μ := fun n => hfm.indicator (hφ.measurable n)
  have key₂ : ∀ᵐx : α ∂μ, Monotone fun n => F n x :=
    ae_of_all _ fun x i j hij => indicator_le_indicator_of_subset (hmono hij) (fun x => zero_le$ f x) x 
  have key₃ : ∀ᵐx : α ∂μ, tendsto (fun n => F n x) at_top (𝓝 (f x)) := hφ.ae_tendsto_indicator
  (lintegral_tendsto_of_tendsto_of_monotone key₁ key₂ key₃).congr fun n => lintegral_indicator f (hφ.measurable n)

-- error in MeasureTheory.Integral.IntegralEqImproper: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_cover.lintegral_tendsto_of_nat
{φ : exprℕ() → set α}
(hφ : ae_cover μ at_top φ)
{f : α → «exprℝ≥0∞»()}
(hfm : ae_measurable f μ) : tendsto (λ
 i, «expr∫⁻ in , ∂ »((x), φ i, f x, μ)) at_top «expr $ »(expr𝓝(), «expr∫⁻ , ∂ »((x), f x, μ)) :=
begin
  have [ident lim₁] [] [":=", expr lintegral_tendsto_of_monotone_of_nat hφ.bInter_Ici_ae_cover (λ
    i j hij, bInter_subset_bInter_left (Ici_subset_Ici.mpr hij)) hfm],
  have [ident lim₂] [] [":=", expr lintegral_tendsto_of_monotone_of_nat hφ.bUnion_Iic_ae_cover (λ
    i j hij, bUnion_subset_bUnion_left (Iic_subset_Iic.mpr hij)) hfm],
  have [ident le₁] [] [":=", expr λ n, lintegral_mono_set (bInter_subset_of_mem left_mem_Ici)],
  have [ident le₂] [] [":=", expr λ n, lintegral_mono_set (subset_bUnion_of_mem right_mem_Iic)],
  exact [expr tendsto_of_tendsto_of_tendsto_of_le_of_le lim₁ lim₂ le₁ le₂]
end

theorem ae_cover.lintegral_tendsto_of_countably_generated [l.is_countably_generated] {φ : ι → Set α}
  (hφ : ae_cover μ l φ) {f : α → ℝ≥0∞} (hfm : AeMeasurable f μ) :
  tendsto (fun i => ∫⁻x in φ i, f x ∂μ) l (𝓝$ ∫⁻x, f x ∂μ) :=
  tendsto_of_seq_tendsto fun u hu => (hφ.comp_tendsto hu).lintegral_tendsto_of_nat hfm

theorem ae_cover.lintegral_eq_of_tendsto [l.ne_bot] [l.is_countably_generated] {φ : ι → Set α} (hφ : ae_cover μ l φ)
  {f : α → ℝ≥0∞} (I : ℝ≥0∞) (hfm : AeMeasurable f μ) (htendsto : tendsto (fun i => ∫⁻x in φ i, f x ∂μ) l (𝓝 I)) :
  (∫⁻x, f x ∂μ) = I :=
  tendsto_nhds_unique (hφ.lintegral_tendsto_of_countably_generated hfm) htendsto

-- error in MeasureTheory.Integral.IntegralEqImproper: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ae_cover.supr_lintegral_eq_of_countably_generated
[nonempty ι]
[l.ne_bot]
[l.is_countably_generated]
{φ : ι → set α}
(hφ : ae_cover μ l φ)
{f : α → «exprℝ≥0∞»()}
(hfm : ae_measurable f μ) : «expr = »(«expr⨆ , »((i : ι), «expr∫⁻ in , ∂ »((x), φ i, f x, μ)), «expr∫⁻ , ∂ »((x), f x, μ)) :=
begin
  have [] [] [":=", expr hφ.lintegral_tendsto_of_countably_generated hfm],
  refine [expr csupr_eq_of_forall_le_of_forall_lt_exists_gt (λ
    i, lintegral_mono' measure.restrict_le_self (le_refl _)) (λ w hw, _)],
  rcases [expr exists_between hw, "with", "⟨", ident m, ",", ident hm₁, ",", ident hm₂, "⟩"],
  rcases [expr (eventually_ge_of_tendsto_gt hm₂ this).exists, "with", "⟨", ident i, ",", ident hi, "⟩"],
  exact [expr ⟨i, lt_of_lt_of_le hm₁ hi⟩]
end

end Lintegral

section Integrable

variable{α ι E :
    Type _}[MeasurableSpace α]{μ : Measureₓ α}{l : Filter ι}[NormedGroup E][MeasurableSpace E][OpensMeasurableSpace E]

theorem ae_cover.integrable_of_lintegral_nnnorm_tendsto [l.ne_bot] [l.is_countably_generated] {φ : ι → Set α}
  (hφ : ae_cover μ l φ) {f : α → E} (I : ℝ) (hfm : AeMeasurable f μ)
  (htendsto : tendsto (fun i => ∫⁻x in φ i, nnnorm (f x) ∂μ) l (𝓝$ Ennreal.ofReal I)) : integrable f μ :=
  by 
    refine' ⟨hfm, _⟩
    unfold has_finite_integral 
    rw [hφ.lintegral_eq_of_tendsto _ (measurable_nnnorm.comp_ae_measurable hfm).coe_nnreal_ennreal htendsto]
    exact Ennreal.of_real_lt_top

theorem ae_cover.integrable_of_lintegral_nnnorm_tendsto' [l.ne_bot] [l.is_countably_generated] {φ : ι → Set α}
  (hφ : ae_cover μ l φ) {f : α → E} (I :  ℝ≥0 ) (hfm : AeMeasurable f μ)
  (htendsto : tendsto (fun i => ∫⁻x in φ i, nnnorm (f x) ∂μ) l (𝓝$ Ennreal.ofReal I)) : integrable f μ :=
  hφ.integrable_of_lintegral_nnnorm_tendsto I hfm htendsto

theorem ae_cover.integrable_of_integral_norm_tendsto [l.ne_bot] [l.is_countably_generated] {φ : ι → Set α}
  (hφ : ae_cover μ l φ) {f : α → E} (I : ℝ) (hfm : AeMeasurable f μ) (hfi : ∀ i, integrable_on f (φ i) μ)
  (htendsto : tendsto (fun i => ∫x in φ i, ∥f x∥ ∂μ) l (𝓝 I)) : integrable f μ :=
  by 
    refine' hφ.integrable_of_lintegral_nnnorm_tendsto I hfm _ 
    conv  at htendsto in integral _ _ =>
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => @norm_nonneg E _ (f x)) hfm.norm.restrict]
    conv  at htendsto in Ennreal.ofReal _ => dsimp rw [←coe_nnnorm]rw [Ennreal.of_real_coe_nnreal]
    convert Ennreal.tendsto_of_real htendsto 
    ext i : 1
    rw [Ennreal.of_real_to_real _]
    exact ne_top_of_lt (hfi i).2

theorem ae_cover.integrable_of_integral_tendsto_of_nonneg_ae [l.ne_bot] [l.is_countably_generated] {φ : ι → Set α}
  (hφ : ae_cover μ l φ) {f : α → ℝ} (I : ℝ) (hfm : AeMeasurable f μ) (hfi : ∀ i, integrable_on f (φ i) μ)
  (hnng : ∀ᵐx ∂μ, 0 ≤ f x) (htendsto : tendsto (fun i => ∫x in φ i, f x ∂μ) l (𝓝 I)) : integrable f μ :=
  hφ.integrable_of_integral_norm_tendsto I hfm hfi
    (htendsto.congr$
      fun i => integral_congr_ae$ ae_restrict_of_ae$ hnng.mono$ fun x hx => (Real.norm_of_nonneg hx).symm)

end Integrable

section Integral

variable{α ι E :
    Type
      _}[MeasurableSpace
      α]{μ :
    Measureₓ
      α}{l :
    Filter
      ι}[NormedGroup E][NormedSpace ℝ E][MeasurableSpace E][BorelSpace E][CompleteSpace E][second_countable_topology E]

theorem ae_cover.integral_tendsto_of_countably_generated [l.is_countably_generated] {φ : ι → Set α}
  (hφ : ae_cover μ l φ) {f : α → E} (hfi : integrable f μ) : tendsto (fun i => ∫x in φ i, f x ∂μ) l (𝓝$ ∫x, f x ∂μ) :=
  suffices h : tendsto (fun i => ∫x : α, (φ i).indicator f x ∂μ) l (𝓝 (∫x : α, f x ∂μ))by 
    convert h 
    ext n 
    rw [integral_indicator (hφ.measurable n)]
  tendsto_integral_filter_of_dominated_convergence (fun x => ∥f x∥)
    (eventually_of_forall$ fun i => hfi.ae_measurable.indicator$ hφ.measurable i)
    (eventually_of_forall$ fun i => ae_of_all _$ fun x => norm_indicator_le_norm_self _ _) hfi.norm
    hφ.ae_tendsto_indicator

/-- Slight reformulation of
    `measure_theory.ae_cover.integral_tendsto_of_countably_generated`. -/
theorem ae_cover.integral_eq_of_tendsto [l.ne_bot] [l.is_countably_generated] {φ : ι → Set α} (hφ : ae_cover μ l φ)
  {f : α → E} (I : E) (hfi : integrable f μ) (h : tendsto (fun n => ∫x in φ n, f x ∂μ) l (𝓝 I)) : (∫x, f x ∂μ) = I :=
  tendsto_nhds_unique (hφ.integral_tendsto_of_countably_generated hfi) h

theorem ae_cover.integral_eq_of_tendsto_of_nonneg_ae [l.ne_bot] [l.is_countably_generated] {φ : ι → Set α}
  (hφ : ae_cover μ l φ) {f : α → ℝ} (I : ℝ) (hnng : 0 ≤ᵐ[μ] f) (hfm : AeMeasurable f μ)
  (hfi : ∀ n, integrable_on f (φ n) μ) (htendsto : tendsto (fun n => ∫x in φ n, f x ∂μ) l (𝓝 I)) : (∫x, f x ∂μ) = I :=
  have hfi' : integrable f μ := hφ.integrable_of_integral_tendsto_of_nonneg_ae I hfm hfi hnng htendsto 
  hφ.integral_eq_of_tendsto I hfi' htendsto

end Integral

section IntegrableOfIntervalIntegral

variable{α ι E :
    Type
      _}[TopologicalSpace
      α][LinearOrderₓ
      α][OrderClosedTopology
      α][MeasurableSpace
      α][OpensMeasurableSpace
      α]{μ :
    Measureₓ
      α}{l :
    Filter
      ι}[Filter.NeBot
      l][is_countably_generated
      l][MeasurableSpace E][NormedGroup E][BorelSpace E]{a b : ι → α}{f : α → E}(hfm : AeMeasurable f μ)

include hfm

-- error in MeasureTheory.Integral.IntegralEqImproper: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integrable_of_interval_integral_norm_tendsto
[no_bot_order α]
[nonempty α]
(I : exprℝ())
(hfi : ∀ i, integrable_on f (Ioc (a i) (b i)) μ)
(ha : tendsto a l at_bot)
(hb : tendsto b l at_top)
(h : tendsto (λ i, «expr∫ in .. , ∂ »((x), a i, b i, «expr∥ ∥»(f x), μ)) l «expr $ »(expr𝓝(), I)) : integrable f μ :=
begin
  let [ident φ] [] [":=", expr λ n, Ioc (a n) (b n)],
  let [ident c] [":", expr α] [":=", expr classical.choice «expr‹ ›»(_)],
  have [ident hφ] [":", expr ae_cover μ l φ] [":=", expr ae_cover_Ioc ha hb],
  refine [expr hφ.integrable_of_integral_norm_tendsto _ hfm hfi (h.congr' _)],
  filter_upwards ["[", expr ha.eventually (eventually_le_at_bot c), ",", expr hb.eventually (eventually_ge_at_top c), "]"] [],
  intros [ident i, ident hai, ident hbi],
  exact [expr interval_integral.integral_of_le (hai.trans hbi)]
end

-- error in MeasureTheory.Integral.IntegralEqImproper: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integrable_on_Iic_of_interval_integral_norm_tendsto
[no_bot_order α]
(I : exprℝ())
(b : α)
(hfi : ∀ i, integrable_on f (Ioc (a i) b) μ)
(ha : tendsto a l at_bot)
(h : tendsto (λ
  i, «expr∫ in .. , ∂ »((x), a i, b, «expr∥ ∥»(f x), μ)) l «expr $ »(expr𝓝(), I)) : integrable_on f (Iic b) μ :=
begin
  let [ident φ] [] [":=", expr λ i, Ioi (a i)],
  have [ident hφ] [":", expr ae_cover «expr $ »(μ.restrict, Iic b) l φ] [":=", expr ae_cover_Ioi ha],
  have [ident hfi] [":", expr ∀ i, integrable_on f (φ i) «expr $ »(μ.restrict, Iic b)] [],
  { intro [ident i],
    rw ["[", expr integrable_on, ",", expr measure.restrict_restrict (hφ.measurable i), "]"] [],
    exact [expr hfi i] },
  refine [expr hφ.integrable_of_integral_norm_tendsto _ hfm.restrict hfi (h.congr' _)],
  filter_upwards ["[", expr ha.eventually (eventually_le_at_bot b), "]"] [],
  intros [ident i, ident hai],
  rw ["[", expr interval_integral.integral_of_le hai, ",", expr measure.restrict_restrict (hφ.measurable i), "]"] [],
  refl
end

-- error in MeasureTheory.Integral.IntegralEqImproper: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem integrable_on_Ioi_of_interval_integral_norm_tendsto
(I : exprℝ())
(a : α)
(hfi : ∀ i, integrable_on f (Ioc a (b i)) μ)
(hb : tendsto b l at_top)
(h : tendsto (λ
  i, «expr∫ in .. , ∂ »((x), a, b i, «expr∥ ∥»(f x), μ)) l «expr $ »(expr𝓝(), I)) : integrable_on f (Ioi a) μ :=
begin
  let [ident φ] [] [":=", expr λ i, Iic (b i)],
  have [ident hφ] [":", expr ae_cover «expr $ »(μ.restrict, Ioi a) l φ] [":=", expr ae_cover_Iic hb],
  have [ident hfi] [":", expr ∀ i, integrable_on f (φ i) «expr $ »(μ.restrict, Ioi a)] [],
  { intro [ident i],
    rw ["[", expr integrable_on, ",", expr measure.restrict_restrict (hφ.measurable i), ",", expr inter_comm, "]"] [],
    exact [expr hfi i] },
  refine [expr hφ.integrable_of_integral_norm_tendsto _ hfm.restrict hfi (h.congr' _)],
  filter_upwards ["[", expr hb.eventually «expr $ »(eventually_ge_at_top, a), "]"] [],
  intros [ident i, ident hbi],
  rw ["[", expr interval_integral.integral_of_le hbi, ",", expr measure.restrict_restrict (hφ.measurable i), ",", expr inter_comm, "]"] [],
  refl
end

end IntegrableOfIntervalIntegral

section IntegralOfIntervalIntegral

variable{α ι E :
    Type
      _}[TopologicalSpace
      α][LinearOrderₓ
      α][OrderClosedTopology
      α][MeasurableSpace
      α][OpensMeasurableSpace
      α]{μ :
    Measureₓ
      α}{l :
    Filter
      ι}[is_countably_generated
      l][MeasurableSpace
      E][NormedGroup
      E][NormedSpace ℝ E][BorelSpace E][CompleteSpace E][second_countable_topology E]{a b : ι → α}{f : α → E}

-- error in MeasureTheory.Integral.IntegralEqImproper: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem interval_integral_tendsto_integral
[no_bot_order α]
[nonempty α]
(hfi : integrable f μ)
(ha : tendsto a l at_bot)
(hb : tendsto b l at_top) : tendsto (λ
 i, «expr∫ in .. , ∂ »((x), a i, b i, f x, μ)) l «expr $ »(expr𝓝(), «expr∫ , ∂ »((x), f x, μ)) :=
begin
  let [ident φ] [] [":=", expr λ i, Ioc (a i) (b i)],
  let [ident c] [":", expr α] [":=", expr classical.choice «expr‹ ›»(_)],
  have [ident hφ] [":", expr ae_cover μ l φ] [":=", expr ae_cover_Ioc ha hb],
  refine [expr (hφ.integral_tendsto_of_countably_generated hfi).congr' _],
  filter_upwards ["[", expr ha.eventually (eventually_le_at_bot c), ",", expr hb.eventually (eventually_ge_at_top c), "]"] [],
  intros [ident i, ident hai, ident hbi],
  exact [expr (interval_integral.integral_of_le (hai.trans hbi)).symm]
end

-- error in MeasureTheory.Integral.IntegralEqImproper: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem interval_integral_tendsto_integral_Iic
[no_bot_order α]
(b : α)
(hfi : integrable_on f (Iic b) μ)
(ha : tendsto a l at_bot) : tendsto (λ
 i, «expr∫ in .. , ∂ »((x), a i, b, f x, μ)) l «expr $ »(expr𝓝(), «expr∫ in , ∂ »((x), Iic b, f x, μ)) :=
begin
  let [ident φ] [] [":=", expr λ i, Ioi (a i)],
  have [ident hφ] [":", expr ae_cover «expr $ »(μ.restrict, Iic b) l φ] [":=", expr ae_cover_Ioi ha],
  refine [expr (hφ.integral_tendsto_of_countably_generated hfi).congr' _],
  filter_upwards ["[", expr ha.eventually «expr $ »(eventually_le_at_bot, b), "]"] [],
  intros [ident i, ident hai],
  rw ["[", expr interval_integral.integral_of_le hai, ",", expr measure.restrict_restrict (hφ.measurable i), "]"] [],
  refl
end

-- error in MeasureTheory.Integral.IntegralEqImproper: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem interval_integral_tendsto_integral_Ioi
(a : α)
(hfi : integrable_on f (Ioi a) μ)
(hb : tendsto b l at_top) : tendsto (λ
 i, «expr∫ in .. , ∂ »((x), a, b i, f x, μ)) l «expr $ »(expr𝓝(), «expr∫ in , ∂ »((x), Ioi a, f x, μ)) :=
begin
  let [ident φ] [] [":=", expr λ i, Iic (b i)],
  have [ident hφ] [":", expr ae_cover «expr $ »(μ.restrict, Ioi a) l φ] [":=", expr ae_cover_Iic hb],
  refine [expr (hφ.integral_tendsto_of_countably_generated hfi).congr' _],
  filter_upwards ["[", expr hb.eventually «expr $ »(eventually_ge_at_top, a), "]"] [],
  intros [ident i, ident hbi],
  rw ["[", expr interval_integral.integral_of_le hbi, ",", expr measure.restrict_restrict (hφ.measurable i), ",", expr inter_comm, "]"] [],
  refl
end

end IntegralOfIntervalIntegral

end MeasureTheory

