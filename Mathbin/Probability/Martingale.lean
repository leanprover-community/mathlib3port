/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import Mathbin.Probability.Notation
import Mathbin.Probability.Stopping

/-!
# Martingales

A family of functions `f : ι → α → E` is a martingale with respect to a filtration `ℱ` if every
`f i` is integrable, `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ i] =ᵐ[μ] f i`. On the other hand, `f : ι → α → E` is said to be a supermartingale
with respect to the filtration `ℱ` if `f i` is integrable, `f` is adapted with resepct to `ℱ`
and for all `i ≤ j`, `μ[f j | ℱ i] ≤ᵐ[μ] f i`. Finally, `f : ι → α → E` is said to be a
submartingale with respect to the filtration `ℱ` if `f i` is integrable, `f` is adapted with
resepct to `ℱ` and for all `i ≤ j`, `f i ≤ᵐ[μ] μ[f j | ℱ i]`.

The definitions of filtration and adapted can be found in `probability.stopping`.

### Definitions

* `measure_theory.martingale f ℱ μ`: `f` is a martingale with respect to filtration `ℱ` and
  measure `μ`.
* `measure_theory.supermartingale f ℱ μ`: `f` is a supermartingale with respect to
  filtration `ℱ` and measure `μ`.
* `measure_theory.submartingale f ℱ μ`: `f` is a submartingale with respect to filtration `ℱ` and
  measure `μ`.

### Results

* `measure_theory.martingale_condexp f ℱ μ`: the sequence `λ i, μ[f | ℱ i, ℱ.le i])` is a
  martingale with respect to `ℱ` and `μ`.

-/


open TopologicalSpace Filter

open Nnreal Ennreal MeasureTheory ProbabilityTheory BigOperators

namespace MeasureTheory

variable {α E ι : Type _} [Preorderₓ ι] {m0 : MeasurableSpace α} {μ : Measure α} [NormedGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {f g : ι → α → E} {ℱ : Filtration ι m0}

/-- A family of functions `f : ι → α → E` is a martingale with respect to a filtration `ℱ` if `f`
is adapted with respect to `ℱ` and for all `i ≤ j`, `μ[f j | ℱ i] =ᵐ[μ] f i`. -/
def Martingale (f : ι → α → E) (ℱ : Filtration ι m0) (μ : Measure α) : Prop :=
  Adapted ℱ f ∧ ∀ i j, i ≤ j → μ[f j|ℱ i] =ᵐ[μ] f i

/-- A family of integrable functions `f : ι → α → E` is a supermartingale with respect to a
filtration `ℱ` if `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] ≤ᵐ[μ] f i`. -/
def Supermartingale [LE E] (f : ι → α → E) (ℱ : Filtration ι m0) (μ : Measure α) : Prop :=
  Adapted ℱ f ∧ (∀ i j, i ≤ j → μ[f j|ℱ i] ≤ᵐ[μ] f i) ∧ ∀ i, Integrable (f i) μ

/-- A family of integrable functions `f : ι → α → E` is a submartingale with respect to a
filtration `ℱ` if `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`f i ≤ᵐ[μ] μ[f j | ℱ.le i]`. -/
def Submartingale [LE E] (f : ι → α → E) (ℱ : Filtration ι m0) (μ : Measure α) : Prop :=
  Adapted ℱ f ∧ (∀ i j, i ≤ j → f i ≤ᵐ[μ] μ[f j|ℱ i]) ∧ ∀ i, Integrable (f i) μ

variable (E)

theorem martingale_zero (ℱ : Filtration ι m0) (μ : Measure α) : Martingale (0 : ι → α → E) ℱ μ :=
  ⟨adapted_zero E ℱ, fun i j hij => by
    rw [Pi.zero_apply, condexp_zero]
    simp ⟩

variable {E}

namespace Martingale

@[protected]
theorem adapted (hf : Martingale f ℱ μ) : Adapted ℱ f :=
  hf.1

@[protected]
theorem strongly_measurable (hf : Martingale f ℱ μ) (i : ι) : strongly_measurable[ℱ i] (f i) :=
  hf.Adapted i

theorem condexp_ae_eq (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j) : μ[f j|ℱ i] =ᵐ[μ] f i :=
  hf.2 i j hij

@[protected]
theorem integrable (hf : Martingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  integrable_condexp.congr (hf.condexp_ae_eq (le_reflₓ i))

theorem set_integral_eq [SigmaFiniteFiltration μ ℱ] (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j) {s : Set α}
    (hs : measurable_set[ℱ i] s) : (∫ x in s, f i x ∂μ) = ∫ x in s, f j x ∂μ := by
  rw [← @set_integral_condexp _ _ _ _ _ (ℱ i) m0 _ _ _ (ℱ.le i) _ (hf.integrable j) hs]
  refine' set_integral_congr_ae (ℱ.le i s hs) _
  filter_upwards [hf.2 i j hij] with _ heq _ using HEq.symm

theorem add (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f + g) ℱ μ := by
  refine' ⟨hf.adapted.add hg.adapted, fun i j hij => _⟩
  exact (condexp_add (hf.integrable j) (hg.integrable j)).trans ((hf.2 i j hij).add (hg.2 i j hij))

theorem neg (hf : Martingale f ℱ μ) : Martingale (-f) ℱ μ :=
  ⟨hf.Adapted.neg, fun i j hij => (condexp_neg (f j)).trans (hf.2 i j hij).neg⟩

theorem sub (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem smul (c : ℝ) (hf : Martingale f ℱ μ) : Martingale (c • f) ℱ μ := by
  refine' ⟨hf.adapted.smul c, fun i j hij => _⟩
  refine' (condexp_smul c (f j)).trans ((hf.2 i j hij).mono fun x hx => _)
  rw [Pi.smul_apply, hx, Pi.smul_apply, Pi.smul_apply]

theorem supermartingale [Preorderₓ E] (hf : Martingale f ℱ μ) : Supermartingale f ℱ μ :=
  ⟨hf.1, fun i j hij => (hf.2 i j hij).le, fun i => hf.Integrable i⟩

theorem submartingale [Preorderₓ E] (hf : Martingale f ℱ μ) : Submartingale f ℱ μ :=
  ⟨hf.1, fun i j hij => (hf.2 i j hij).symm.le, fun i => hf.Integrable i⟩

end Martingale

theorem martingale_iff [PartialOrderₓ E] : Martingale f ℱ μ ↔ Supermartingale f ℱ μ ∧ Submartingale f ℱ μ :=
  ⟨fun hf => ⟨hf.Supermartingale, hf.Submartingale⟩, fun ⟨hf₁, hf₂⟩ =>
    ⟨hf₁.1, fun i j hij => (hf₁.2.1 i j hij).antisymm (hf₂.2.1 i j hij)⟩⟩

theorem martingale_condexp (f : α → E) (ℱ : Filtration ι m0) (μ : Measure α) [SigmaFiniteFiltration μ ℱ] :
    Martingale (fun i => μ[f|ℱ i]) ℱ μ :=
  ⟨fun i => strongly_measurable_condexp, fun i j hij => condexp_condexp_of_le (ℱ.mono hij) (ℱ.le j)⟩

namespace Supermartingale

@[protected]
theorem adapted [LE E] (hf : Supermartingale f ℱ μ) : Adapted ℱ f :=
  hf.1

@[protected]
theorem strongly_measurable [LE E] (hf : Supermartingale f ℱ μ) (i : ι) : strongly_measurable[ℱ i] (f i) :=
  hf.Adapted i

@[protected]
theorem integrable [LE E] (hf : Supermartingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i

theorem condexp_ae_le [LE E] (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j) : μ[f j|ℱ i] ≤ᵐ[μ] f i :=
  hf.2.1 i j hij

theorem set_integral_le [SigmaFiniteFiltration μ ℱ] {f : ι → α → ℝ} (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j)
    {s : Set α} (hs : measurable_set[ℱ i] s) : (∫ x in s, f j x ∂μ) ≤ ∫ x in s, f i x ∂μ := by
  rw [← set_integral_condexp (ℱ.le i) (hf.integrable j) hs]
  refine' set_integral_mono_ae integrable_condexp.integrable_on (hf.integrable i).IntegrableOn _
  filter_upwards [hf.2.1 i j hij] with _ heq using HEq

theorem add [Preorderₓ E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Supermartingale f ℱ μ)
    (hg : Supermartingale g ℱ μ) : Supermartingale (f + g) ℱ μ := by
  refine' ⟨hf.1.add hg.1, fun i j hij => _, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine' (condexp_add (hf.integrable j) (hg.integrable j)).le.trans _
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine' add_le_add _ _ <;> assumption

theorem add_martingale [Preorderₓ E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Supermartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Supermartingale (f + g) ℱ μ :=
  hf.add hg.Supermartingale

theorem neg [Preorderₓ E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Supermartingale f ℱ μ) : Submartingale (-f) ℱ μ :=
  by
  refine' ⟨hf.1.neg, fun i j hij => _, fun i => (hf.2.2 i).neg⟩
  refine' eventually_le.trans _ (condexp_neg (f j)).symm.le
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa

end Supermartingale

namespace Submartingale

@[protected]
theorem adapted [LE E] (hf : Submartingale f ℱ μ) : Adapted ℱ f :=
  hf.1

@[protected]
theorem strongly_measurable [LE E] (hf : Submartingale f ℱ μ) (i : ι) : strongly_measurable[ℱ i] (f i) :=
  hf.Adapted i

@[protected]
theorem integrable [LE E] (hf : Submartingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i

theorem ae_le_condexp [LE E] (hf : Submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) : f i ≤ᵐ[μ] μ[f j|ℱ i] :=
  hf.2.1 i j hij

theorem add [Preorderₓ E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Submartingale f ℱ μ) (hg : Submartingale g ℱ μ) :
    Submartingale (f + g) ℱ μ := by
  refine' ⟨hf.1.add hg.1, fun i j hij => _, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  refine' eventually_le.trans _ (condexp_add (hf.integrable j) (hg.integrable j)).symm.le
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij]
  intros
  refine' add_le_add _ _ <;> assumption

theorem add_martingale [Preorderₓ E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Submartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Submartingale (f + g) ℱ μ :=
  hf.add hg.Submartingale

theorem neg [Preorderₓ E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Submartingale f ℱ μ) : Supermartingale (-f) ℱ μ :=
  by
  refine' ⟨hf.1.neg, fun i j hij => (condexp_neg (f j)).le.trans _, fun i => (hf.2.2 i).neg⟩
  filter_upwards [hf.2.1 i j hij] with _ _
  simpa

/-- The converse of this lemma is `measure_theory.submartingale_of_set_integral_le`. -/
theorem set_integral_le [SigmaFiniteFiltration μ ℱ] {f : ι → α → ℝ} (hf : Submartingale f ℱ μ) {i j : ι} (hij : i ≤ j)
    {s : Set α} (hs : measurable_set[ℱ i] s) : (∫ x in s, f i x ∂μ) ≤ ∫ x in s, f j x ∂μ := by
  rw [← neg_le_neg_iff, ← integral_neg, ← integral_neg]
  exact supermartingale.set_integral_le hf.neg hij hs

theorem sub_supermartingale [Preorderₓ E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Submartingale f ℱ μ)
    (hg : Supermartingale g ℱ μ) : Submartingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem sub_martingale [Preorderₓ E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Submartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Submartingale (f - g) ℱ μ :=
  hf.sub_supermartingale hg.Supermartingale

end Submartingale

section Submartingale

theorem submartingale_of_set_integral_le [IsFiniteMeasure μ] {f : ι → α → ℝ} (hadp : Adapted ℱ f)
    (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i j : ι, i ≤ j → ∀ s : Set α, measurable_set[ℱ i] s → (∫ x in s, f i x ∂μ) ≤ ∫ x in s, f j x ∂μ) :
    Submartingale f ℱ μ := by
  refine' ⟨hadp, fun i j hij => _, hint⟩
  suffices f i ≤ᵐ[μ.trim (ℱ.le i)] μ[f j|ℱ i] by
    exact ae_le_of_ae_le_trim this
  suffices 0 ≤ᵐ[μ.trim (ℱ.le i)] μ[f j|ℱ i] - f i by
    filter_upwards [this] with x hx
    rwa [← sub_nonneg]
  refine'
    ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure
      ((integrable_condexp.sub (hint i)).trim _ (strongly_measurable_condexp.sub <| hadp i)) fun s hs => _
  specialize hf i j hij s hs
  rwa [← set_integral_trim _ (strongly_measurable_condexp.sub <| hadp i) hs,
    integral_sub' integrable_condexp.integrable_on (hint i).IntegrableOn, sub_nonneg,
    set_integral_condexp (ℱ.le i) (hint j) hs]

theorem submartingale_of_condexp_sub_nonneg [IsFiniteMeasure μ] {f : ι → α → ℝ} (hadp : Adapted ℱ f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[f j - f i|ℱ i]) : Submartingale f ℱ μ := by
  refine' ⟨hadp, fun i j hij => _, hint⟩
  rw [← condexp_of_strongly_measurable (ℱ.le _) (hadp _) (hint _), ← eventually_sub_nonneg]
  exact eventually_le.trans (hf i j hij) (condexp_sub (hint _) (hint _)).le
  infer_instance

theorem Submartingale.condexp_sub_nonneg [IsFiniteMeasure μ] {f : ι → α → ℝ} (hf : Submartingale f ℱ μ) {i j : ι}
    (hij : i ≤ j) : 0 ≤ᵐ[μ] μ[f j - f i|ℱ i] := by
  refine' eventually_le.trans _ (condexp_sub (hf.integrable _) (hf.integrable _)).symm.le
  rw [eventually_sub_nonneg, condexp_of_strongly_measurable (ℱ.le _) (hf.adapted _) (hf.integrable _)]
  exact hf.2.1 i j hij
  infer_instance

theorem submartingale_iff_condexp_sub_nonneg [IsFiniteMeasure μ] {f : ι → α → ℝ} :
    Submartingale f ℱ μ ↔ Adapted ℱ f ∧ (∀ i, Integrable (f i) μ) ∧ ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[f j - f i|ℱ i] :=
  ⟨fun h => ⟨h.Adapted, h.Integrable, fun i j => h.condexp_sub_nonneg⟩, fun ⟨hadp, hint, h⟩ =>
    submartingale_of_condexp_sub_nonneg hadp hint h⟩

end Submartingale

namespace Supermartingale

theorem sub_submartingale [Preorderₓ E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Supermartingale f ℱ μ)
    (hg : Submartingale g ℱ μ) : Supermartingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem sub_martingale [Preorderₓ E] [CovariantClass E E (· + ·) (· ≤ ·)] (hf : Supermartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Supermartingale (f - g) ℱ μ :=
  hf.sub_submartingale hg.Submartingale

section

variable {F : Type _} [NormedLatticeAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [OrderedSmul ℝ F]

theorem smul_nonneg {f : ι → α → F} {c : ℝ} (hc : 0 ≤ c) (hf : Supermartingale f ℱ μ) : Supermartingale (c • f) ℱ μ :=
  by
  refine' ⟨hf.1.smul c, fun i j hij => _, fun i => (hf.2.2 i).smul c⟩
  refine' (condexp_smul c (f j)).le.trans _
  filter_upwards [hf.2.1 i j hij] with _ hle
  simp
  exact smul_le_smul_of_nonneg hle hc

theorem smul_nonpos {f : ι → α → F} {c : ℝ} (hc : c ≤ 0) (hf : Supermartingale f ℱ μ) : Submartingale (c • f) ℱ μ := by
  rw [← neg_negₓ c,
    (by
      ext i x
      simp : - -c • f = -(-c • f))]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

end

end Supermartingale

namespace Submartingale

section

variable {F : Type _} [NormedLatticeAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [OrderedSmul ℝ F]

theorem smul_nonneg {f : ι → α → F} {c : ℝ} (hc : 0 ≤ c) (hf : Submartingale f ℱ μ) : Submartingale (c • f) ℱ μ := by
  rw [← neg_negₓ c,
    (by
      ext i x
      simp : - -c • f = -(c • -f))]
  exact supermartingale.neg (hf.neg.smul_nonneg hc)

theorem smul_nonpos {f : ι → α → F} {c : ℝ} (hc : c ≤ 0) (hf : Submartingale f ℱ μ) : Supermartingale (c • f) ℱ μ := by
  rw [← neg_negₓ c,
    (by
      ext i x
      simp : - -c • f = -(-c • f))]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

end

end Submartingale

section Nat

variable {𝒢 : Filtration ℕ m0}

theorem submartingale_of_set_integral_le_succ [IsFiniteMeasure μ] {f : ℕ → α → ℝ} (hadp : Adapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set α, measurable_set[𝒢 i] s → (∫ x in s, f i x ∂μ) ≤ ∫ x in s, f (i + 1) x ∂μ) :
    Submartingale f 𝒢 μ := by
  refine' submartingale_of_set_integral_le hadp hint fun i j hij s hs => _
  induction' hij with k hk₁ hk₂
  · exact le_rfl
    
  · exact le_transₓ hk₂ (hf k s (𝒢.mono hk₁ _ hs))
    

theorem submartingale_nat [IsFiniteMeasure μ] {f : ℕ → α → ℝ} (hadp : Adapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, f i ≤ᵐ[μ] μ[f (i + 1)|𝒢 i]) : Submartingale f 𝒢 μ := by
  refine' submartingale_of_set_integral_le_succ hadp hint fun i s hs => _
  have : (∫ x in s, f (i + 1) x ∂μ) = ∫ x in s, (μ[f (i + 1)|𝒢 i]) x ∂μ :=
    (set_integral_condexp (𝒢.le i) (hint _) hs).symm
  rw [this]
  exact set_integral_mono_ae (hint i).IntegrableOn integrable_condexp.integrable_on (hf i)

theorem submartingale_of_condexp_sub_nonneg_nat [IsFiniteMeasure μ] {f : ℕ → α → ℝ} (hadp : Adapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i, 0 ≤ᵐ[μ] μ[f (i + 1) - f i|𝒢 i]) : Submartingale f 𝒢 μ := by
  refine' submartingale_nat hadp hint fun i => _
  rw [← condexp_of_strongly_measurable (𝒢.le _) (hadp _) (hint _), ← eventually_sub_nonneg]
  exact eventually_le.trans (hf i) (condexp_sub (hint _) (hint _)).le
  infer_instance

namespace Submartingale

theorem integrable_stopped_value [LE E] {f : ℕ → α → E} (hf : Submartingale f 𝒢 μ) {τ : α → ℕ} (hτ : IsStoppingTime 𝒢 τ)
    {N : ℕ} (hbdd : ∀ x, τ x ≤ N) : Integrable (stoppedValue f τ) μ :=
  integrable_stopped_value hτ hf.Integrable hbdd

/-- Given a submartingale `f` and bounded stopping times `τ` and `π` such that `τ ≤ π`, the
expectation of `stopped_value f τ` is less than or equal to the expectation of `stopped_value f π`.
This is the forward direction of the optional stopping theorem. -/
-- We may generalize the below lemma to functions taking value in a `normed_lattice_add_comm_group`.
-- Similarly, generalize `(super/)submartingale.set_integral_le`.
theorem expected_stopped_value_mono [SigmaFiniteFiltration μ 𝒢] {f : ℕ → α → ℝ} (hf : Submartingale f 𝒢 μ) {τ π : α → ℕ}
    (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π) (hle : τ ≤ π) {N : ℕ} (hbdd : ∀ x, π x ≤ N) :
    μ[stoppedValue f τ] ≤ μ[stoppedValue f π] := by
  rw [← sub_nonneg, ← integral_sub', stopped_value_sub_eq_sum' hle hbdd]
  · simp only [← Finset.sum_apply]
    have : ∀ i, measurable_set[𝒢 i] { x : α | τ x ≤ i ∧ i < π x } := by
      intro i
      refine' (hτ i).inter _
      convert (hπ i).compl
      ext x
      simpa
    rw [integral_finset_sum]
    · refine' Finset.sum_nonneg fun i hi => _
      rw [integral_indicator (𝒢.le _ _ (this _)), integral_sub', sub_nonneg]
      · exact hf.set_integral_le (Nat.le_succₓ i) (this _)
        
      · exact (hf.integrable _).IntegrableOn
        
      · exact (hf.integrable _).IntegrableOn
        
      
    intro i hi
    exact integrable.indicator (integrable.sub (hf.integrable _) (hf.integrable _)) (𝒢.le _ _ (this _))
    
  · exact hf.integrable_stopped_value hπ hbdd
    
  · exact hf.integrable_stopped_value hτ fun x => le_transₓ (hle x) (hbdd x)
    

end Submartingale

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
/-- The converse direction of the optional stopping theorem, i.e. an adapted integrable process `f`
is a submartingale if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
theorem submartingale_of_expected_stopped_value_mono [IsFiniteMeasure μ] {f : ℕ → α → ℝ} (hadp : Adapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ)
    (hf :
      ∀ τ π : α → ℕ,
        IsStoppingTime 𝒢 τ →
          IsStoppingTime 𝒢 π → τ ≤ π → (∃ N, ∀ x, π x ≤ N) → μ[stoppedValue f τ] ≤ μ[stoppedValue f π]) :
    Submartingale f 𝒢 μ := by
  refine' submartingale_of_set_integral_le hadp hint fun i j hij s hs => _
  classical
  specialize
    hf (s.piecewise (fun _ => i) fun _ => j) _ (is_stopping_time_piecewise_const hij hs) (is_stopping_time_const 𝒢 j)
      (fun x => (ite_le_sup _ _ _).trans (max_eq_rightₓ hij).le) ⟨j, fun x => le_rfl⟩
  rwa [stopped_value_const, stopped_value_piecewise_const,
    integral_piecewise (𝒢.le _ _ hs) (hint _).IntegrableOn (hint _).IntegrableOn, ←
    integral_add_compl (𝒢.le _ _ hs) (hint j), add_le_add_iff_right] at hf

/-- **The optional stopping theorem** (fair game theorem): an adapted integrable process `f`
is a submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
theorem submartingale_iff_expected_stopped_value_mono [IsFiniteMeasure μ] {f : ℕ → α → ℝ} (hadp : Adapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) :
    Submartingale f 𝒢 μ ↔
      ∀ τ π : α → ℕ,
        IsStoppingTime 𝒢 τ →
          IsStoppingTime 𝒢 π → τ ≤ π → (∃ N, ∀ x, π x ≤ N) → μ[stoppedValue f τ] ≤ μ[stoppedValue f π] :=
  ⟨fun hf _ _ hτ hπ hle ⟨N, hN⟩ => hf.expected_stopped_value_mono hτ hπ hle hN,
    submartingale_of_expected_stopped_value_mono hadp hint⟩

end Nat

end MeasureTheory

