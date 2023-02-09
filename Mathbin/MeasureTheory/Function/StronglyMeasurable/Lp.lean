/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.function.strongly_measurable.lp
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Function.SimpleFuncDenseLp
import Mathbin.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Finitely strongly measurable functions in `Lp`

Functions in `Lp` for `0 < p < ∞` are finitely strongly measurable.

## Main statements

* `mem_ℒp.ae_fin_strongly_measurable`: if `mem_ℒp f p μ` with `0 < p < ∞`, then
  `ae_fin_strongly_measurable f μ`.
* `Lp.fin_strongly_measurable`: for `0 < p < ∞`, `Lp` functions are finitely strongly measurable.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
Springer, 2016.
-/


open MeasureTheory Filter TopologicalSpace Function

open Ennreal Topology MeasureTheory

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

variable {α G : Type _} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup G]
  {f : α → G}

theorem Memℒp.finStronglyMeasurableOfStronglyMeasurable (hf : Memℒp f p μ)
    (hf_meas : StronglyMeasurable f) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    FinStronglyMeasurable f μ := by
  borelize G
  haveI : SeparableSpace (Set.range f ∪ {0} : Set G) :=
    hf_meas.separable_space_range_union_singleton
  let fs := SimpleFunc.approxOn f hf_meas.measurable (Set.range f ∪ {0}) 0 (by simp)
  refine' ⟨fs, _, _⟩
  · have h_fs_Lp : ∀ n, Memℒp (fs n) p μ := SimpleFunc.memℒpApproxOnRange hf_meas.measurable hf
    exact fun n => (fs n).measure_support_lt_top_of_memℒp (h_fs_Lp n) hp_ne_zero hp_ne_top
  · intro x
    apply SimpleFunc.tendsto_approxOn
    apply subset_closure
    simp
#align measure_theory.mem_ℒp.fin_strongly_measurable_of_strongly_measurable MeasureTheory.Memℒp.finStronglyMeasurableOfStronglyMeasurable

theorem Memℒp.aeFinStronglyMeasurable (hf : Memℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    AeFinStronglyMeasurable f μ :=
  ⟨hf.aeStronglyMeasurable.mk f,
    ((memℒp_congr_ae hf.aeStronglyMeasurable.ae_eq_mk).mp
          hf).finStronglyMeasurableOfStronglyMeasurable
      hf.aeStronglyMeasurable.stronglyMeasurable_mk hp_ne_zero hp_ne_top,
    hf.aeStronglyMeasurable.ae_eq_mk⟩
#align measure_theory.mem_ℒp.ae_fin_strongly_measurable MeasureTheory.Memℒp.aeFinStronglyMeasurable

theorem Integrable.aeFinStronglyMeasurable (hf : Integrable f μ) : AeFinStronglyMeasurable f μ :=
  (memℒp_one_iff_integrable.mpr hf).aeFinStronglyMeasurable one_ne_zero Ennreal.coe_ne_top
#align measure_theory.integrable.ae_fin_strongly_measurable MeasureTheory.Integrable.aeFinStronglyMeasurable

theorem lp.finStronglyMeasurable (f : lp G p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    FinStronglyMeasurable f μ :=
  (lp.memℒp f).finStronglyMeasurableOfStronglyMeasurable (lp.stronglyMeasurable f) hp_ne_zero
    hp_ne_top
#align measure_theory.Lp.fin_strongly_measurable MeasureTheory.lp.finStronglyMeasurable

end MeasureTheory

