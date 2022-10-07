/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
import Mathbin.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Filtrations

This file defines filtrations of a measurable space and σ-finite filtrations.

## Main definitions

* `measure_theory.filtration`: a filtration on a measurable space. That is, a monotone sequence of
  sub-σ-algebras.
* `measure_theory.sigma_finite_filtration`: a filtration `f` is σ-finite with respect to a measure
  `μ` if for all `i`, `μ.trim (f.le i)` is σ-finite.
* `measure_theory.filtration.natular`: the smallest filtration that makes a process adapted. That
  notion `adapted` is not defined yet in this file. See `measure_theory.adapted`.

## Main results

* `measure_theory.filtration.complete_lattice`: filtrations are a complete lattice.

## Tags

filtration, stochastic process

-/


open Filter Order TopologicalSpace

open Classical MeasureTheory Nnreal Ennreal TopologicalSpace BigOperators

namespace MeasureTheory

/-- A `filtration` on a measurable space `Ω` with σ-algebra `m` is a monotone
sequence of sub-σ-algebras of `m`. -/
structure Filtration {Ω : Type _} (ι : Type _) [Preorderₓ ι] (m : MeasurableSpace Ω) where
  seq : ι → MeasurableSpace Ω
  mono' : Monotoneₓ seq
  le' : ∀ i : ι, seq i ≤ m

variable {Ω β ι : Type _} {m : MeasurableSpace Ω}

instance [Preorderₓ ι] : CoeFun (Filtration ι m) fun _ => ι → MeasurableSpace Ω :=
  ⟨fun f => f.seq⟩

namespace Filtration

variable [Preorderₓ ι]

protected theorem mono {i j : ι} (f : Filtration ι m) (hij : i ≤ j) : f i ≤ f j :=
  f.mono' hij

protected theorem le (f : Filtration ι m) (i : ι) : f i ≤ m :=
  f.le' i

@[ext]
protected theorem ext {f g : Filtration ι m} (h : (f : ι → MeasurableSpace Ω) = g) : f = g := by
  cases f
  cases g
  simp only
  exact h

variable (ι)

/-- The constant filtration which is equal to `m` for all `i : ι`. -/
def const (m' : MeasurableSpace Ω) (hm' : m' ≤ m) : Filtration ι m :=
  ⟨fun _ => m', monotone_constₓ, fun _ => hm'⟩

variable {ι}

@[simp]
theorem const_apply {m' : MeasurableSpace Ω} {hm' : m' ≤ m} (i : ι) : const ι m' hm' i = m' :=
  rfl

instance : Inhabited (Filtration ι m) :=
  ⟨const ι m le_rflₓ⟩

instance : LE (Filtration ι m) :=
  ⟨fun f g => ∀ i, f i ≤ g i⟩

instance : HasBot (Filtration ι m) :=
  ⟨const ι ⊥ bot_le⟩

instance : HasTop (Filtration ι m) :=
  ⟨const ι m le_rflₓ⟩

instance : HasSup (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i ⊔ g i,
      mono' := fun i j hij => sup_le ((f.mono hij).trans le_sup_left) ((g.mono hij).trans le_sup_right),
      le' := fun i => sup_le (f.le i) (g.le i) }⟩

@[norm_cast]
theorem coe_fn_sup {f g : Filtration ι m} : ⇑(f ⊔ g) = f ⊔ g :=
  rfl

instance : HasInf (Filtration ι m) :=
  ⟨fun f g =>
    { seq := fun i => f i ⊓ g i,
      mono' := fun i j hij => le_inf (inf_le_left.trans (f.mono hij)) (inf_le_right.trans (g.mono hij)),
      le' := fun i => inf_le_left.trans (f.le i) }⟩

@[norm_cast]
theorem coe_fn_inf {f g : Filtration ι m} : ⇑(f ⊓ g) = f ⊓ g :=
  rfl

instance : HasSupₓ (Filtration ι m) :=
  ⟨fun s =>
    { seq := fun i => sup ((fun f : Filtration ι m => f i) '' s),
      mono' := fun i j hij => by
        refine' Sup_le fun m' hm' => _
        rw [Set.mem_image] at hm'
        obtain ⟨f, hf_mem, hfm'⟩ := hm'
        rw [← hfm']
        refine' (f.mono hij).trans _
        have hfj_mem : f j ∈ (fun g : filtration ι m => g j) '' s := ⟨f, hf_mem, rfl⟩
        exact le_Sup hfj_mem,
      le' := fun i => by
        refine' Sup_le fun m' hm' => _
        rw [Set.mem_image] at hm'
        obtain ⟨f, hf_mem, hfm'⟩ := hm'
        rw [← hfm']
        exact f.le i }⟩

theorem Sup_def (s : Set (Filtration ι m)) (i : ι) : sup s i = sup ((fun f : Filtration ι m => f i) '' s) :=
  rfl

noncomputable instance : HasInfₓ (Filtration ι m) :=
  ⟨fun s =>
    { seq := fun i => if Set.Nonempty s then inf ((fun f : Filtration ι m => f i) '' s) else m,
      mono' := fun i j hij => by
        by_cases h_nonempty:Set.Nonempty s
        swap
        · simp only [h_nonempty, Set.nonempty_image_iff, if_false, le_reflₓ]
          
        simp only [h_nonempty, if_true, le_Inf_iff, Set.mem_image, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        refine' fun f hf_mem => le_transₓ _ (f.mono hij)
        have hfi_mem : f i ∈ (fun g : filtration ι m => g i) '' s := ⟨f, hf_mem, rfl⟩
        exact Inf_le hfi_mem,
      le' := fun i => by
        by_cases h_nonempty:Set.Nonempty s
        swap
        · simp only [h_nonempty, if_false, le_reflₓ]
          
        simp only [h_nonempty, if_true]
        obtain ⟨f, hf_mem⟩ := h_nonempty
        exact le_transₓ (Inf_le ⟨f, hf_mem, rfl⟩) (f.le i) }⟩

theorem Inf_def (s : Set (Filtration ι m)) (i : ι) :
    inf s i = if Set.Nonempty s then inf ((fun f : Filtration ι m => f i) '' s) else m :=
  rfl

noncomputable instance : CompleteLattice (Filtration ι m) where
  le := (· ≤ ·)
  le_refl := fun f i => le_rflₓ
  le_trans := fun f g h h_fg h_gh i => (h_fg i).trans (h_gh i)
  le_antisymm := fun f g h_fg h_gf => filtration.ext <| funext fun i => (h_fg i).antisymm (h_gf i)
  sup := (· ⊔ ·)
  le_sup_left := fun f g i => le_sup_left
  le_sup_right := fun f g i => le_sup_right
  sup_le := fun f g h h_fh h_gh i => sup_le (h_fh i) (h_gh _)
  inf := (· ⊓ ·)
  inf_le_left := fun f g i => inf_le_left
  inf_le_right := fun f g i => inf_le_right
  le_inf := fun f g h h_fg h_fh i => le_inf (h_fg i) (h_fh i)
  sup := sup
  le_Sup := fun s f hf_mem i => le_Sup ⟨f, hf_mem, rfl⟩
  Sup_le := fun s f h_forall i =>
    Sup_le fun m' hm' => by
      obtain ⟨g, hg_mem, hfm'⟩ := hm'
      rw [← hfm']
      exact h_forall g hg_mem i
  inf := inf
  Inf_le := fun s f hf_mem i => by
    have hs : s.nonempty := ⟨f, hf_mem⟩
    simp only [Inf_def, hs, if_true]
    exact Inf_le ⟨f, hf_mem, rfl⟩
  le_Inf := fun s f h_forall i => by
    by_cases hs:s.nonempty
    swap
    · simp only [Inf_def, hs, if_false]
      exact f.le i
      
    simp only [Inf_def, hs, if_true, le_Inf_iff, Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun g hg_mem => h_forall g hg_mem i
  top := ⊤
  bot := ⊥
  le_top := fun f i => f.le' i
  bot_le := fun f i => bot_le

end Filtration

theorem measurable_set_of_filtration [Preorderₓ ι] {f : Filtration ι m} {s : Set Ω} {i : ι}
    (hs : measurable_set[f i] s) : measurable_set[m] s :=
  f.le i s hs

/-- A measure is σ-finite with respect to filtration if it is σ-finite with respect
to all the sub-σ-algebra of the filtration. -/
class SigmaFiniteFiltration [Preorderₓ ι] (μ : Measure Ω) (f : Filtration ι m) : Prop where
  SigmaFinite : ∀ i : ι, SigmaFinite (μ.trim (f.le i))

instance sigma_finite_of_sigma_finite_filtration [Preorderₓ ι] (μ : Measure Ω) (f : Filtration ι m)
    [hf : SigmaFiniteFiltration μ f] (i : ι) : SigmaFinite (μ.trim (f.le i)) := by apply hf.sigma_finite

-- can't exact here
instance (priority := 100) IsFiniteMeasure.sigma_finite_filtration [Preorderₓ ι] (μ : Measure Ω) (f : Filtration ι m)
    [IsFiniteMeasure μ] : SigmaFiniteFiltration μ f :=
  ⟨fun n => by infer_instance⟩

/-- Given a integrable function `g`, the conditional expectations of `g` with respect to a
filtration is uniformly integrable. -/
theorem Integrable.uniform_integrable_condexp_filtration [Preorderₓ ι] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Filtration ι m} {g : Ω → ℝ} (hg : Integrable g μ) : UniformIntegrable (fun i => μ[g|f i]) 1 μ :=
  hg.uniform_integrable_condexp f.le

namespace Filtration

variable [TopologicalSpace β] [MetrizableSpace β] [mβ : MeasurableSpace β] [BorelSpace β] [Preorderₓ ι]

include mβ

/-- Given a sequence of functions, the natural filtration is the smallest sequence
of σ-algebras such that that sequence of functions is measurable with respect to
the filtration. -/
def natural (u : ι → Ω → β) (hum : ∀ i, StronglyMeasurable (u i)) : Filtration ι m where
  seq := fun i => ⨆ j ≤ i, MeasurableSpace.comap (u j) mβ
  mono' := fun i j hij => bsupr_mono fun k => ge_transₓ hij
  le' := fun i => by
    refine' supr₂_le _
    rintro j hj s ⟨t, ht, rfl⟩
    exact (hum j).Measurable ht

section Limit

omit mβ

variable {E : Type _} [Zero E] [TopologicalSpace E] {ℱ : Filtration ι m} {f : ι → Ω → E} {μ : Measure Ω}

/-- Given a process `f` and a filtration `ℱ`, if `f` converges to some `g` almost everywhere and
`g` is `⨆ n, ℱ n`-measurable, then `limit_process f ℱ μ` chooses said `g`, else it returns 0.

This definition is used to phrase the a.e. martingale convergence theorem
`submartingale.ae_tendsto_limit_process` where an L¹-bounded submartingale `f` adapted to `ℱ`
converges to `limit_process f ℱ μ` `μ`-almost everywhere. -/
noncomputable def limitProcess (f : ι → Ω → E) (ℱ : Filtration ι m)
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) :=
  if h : ∃ g : Ω → E, strongly_measurable[⨆ n, ℱ n] g ∧ ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) then
    Classical.choose h
  else 0

theorem strongly_measurable_limit_process : strongly_measurable[⨆ n, ℱ n] (limitProcess f ℱ μ) := by
  rw [limit_process]
  split_ifs with h h
  exacts[(Classical.choose_spec h).1, strongly_measurable_zero]

theorem strongly_measurable_limit_process' : strongly_measurable[m] (limitProcess f ℱ μ) :=
  strongly_measurable_limit_process.mono (Sup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _)

theorem mem_ℒp_limit_process_of_snorm_bdd {R : ℝ≥0} {p : ℝ≥0∞} {F : Type _} [NormedAddCommGroup F] {ℱ : Filtration ℕ m}
    {f : ℕ → Ω → F} (hfm : ∀ n, AeStronglyMeasurable (f n) μ) (hbdd : ∀ n, snorm (f n) p μ ≤ R) :
    Memℒp (limitProcess f ℱ μ) p μ := by
  rw [limit_process]
  split_ifs with h
  · refine'
      ⟨strongly_measurable.ae_strongly_measurable
          ((Classical.choose_spec h).1.mono (Sup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _)),
        lt_of_le_of_ltₓ (Lp.snorm_lim_le_liminf_snorm hfm _ (Classical.choose_spec h).2)
          (lt_of_le_of_ltₓ _ (Ennreal.coe_lt_top : ↑R < ∞))⟩
    simp_rw [liminf_eq, eventually_at_top]
    exact Sup_le fun b ⟨a, ha⟩ => (ha a le_rflₓ).trans (hbdd _)
    
  · exact zero_mem_ℒp
    

end Limit

end Filtration

end MeasureTheory

