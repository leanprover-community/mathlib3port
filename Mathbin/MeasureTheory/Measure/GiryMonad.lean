/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module measure_theory.measure.giry_monad
! leanprover-community/mathlib commit 38df578a6450a8c5142b3727e3ae894c2300cae0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Integral.Lebesgue

/-!
# The Giry monad

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let X be a measurable space. The collection of all measures on X again
forms a measurable space. This construction forms a monad on
measurable spaces and measurable functions, called the Giry monad.

Note that most sources use the term "Giry monad" for the restriction
to *probability* measures. Here we include all measures on X.

See also `measure_theory/category/Meas.lean`, containing an upgrade of the type-level
monad to an honest monad of the functor `Measure : Meas ⥤ Meas`.

## References

* <https://ncatlab.org/nlab/show/Giry+monad>

## Tags

giry monad
-/


noncomputable section

open Classical BigOperators ENNReal

open Classical Set Filter

variable {α β : Type _}

namespace MeasureTheory

namespace Measure

variable [MeasurableSpace α] [MeasurableSpace β]

/-- Measurability structure on `measure`: Measures are measurable w.r.t. all projections -/
instance : MeasurableSpace (Measure α) :=
  ⨆ (s : Set α) (hs : MeasurableSet s), (borel ℝ≥0∞).comap fun μ => μ s

#print MeasureTheory.Measure.measurable_coe /-
theorem measurable_coe {s : Set α} (hs : MeasurableSet s) : Measurable fun μ : Measure α => μ s :=
  Measurable.of_comap_le <| le_iSup_of_le s <| le_iSup_of_le hs <| le_rfl
#align measure_theory.measure.measurable_coe MeasureTheory.Measure.measurable_coe
-/

/- warning: measure_theory.measure.measurable_of_measurable_coe -> MeasureTheory.Measure.measurable_of_measurable_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (f : β -> (MeasureTheory.Measure.{u1} α _inst_1)), (forall (s : Set.{u1} α), (MeasurableSet.{u1} α _inst_1 s) -> (Measurable.{u2, 0} β ENNReal _inst_2 ENNReal.measurableSpace (fun (b : β) => coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α _inst_1) (fun (_x : MeasureTheory.Measure.{u1} α _inst_1) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α _inst_1) (f b) s))) -> (Measurable.{u2, u1} β (MeasureTheory.Measure.{u1} α _inst_1) _inst_2 (MeasureTheory.Measure.instMeasurableSpace.{u1} α _inst_1) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (f : β -> (MeasureTheory.Measure.{u2} α _inst_1)), (forall (s : Set.{u2} α), (MeasurableSet.{u2} α _inst_1 s) -> (Measurable.{u1, 0} β ENNReal _inst_2 ENNReal.measurableSpace (fun (b : β) => MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α _inst_1 (f b)) s))) -> (Measurable.{u1, u2} β (MeasureTheory.Measure.{u2} α _inst_1) _inst_2 (MeasureTheory.Measure.instMeasurableSpace.{u2} α _inst_1) f)
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.measurable_of_measurable_coe MeasureTheory.Measure.measurable_of_measurable_coeₓ'. -/
theorem measurable_of_measurable_coe (f : β → Measure α)
    (h : ∀ (s : Set α) (hs : MeasurableSet s), Measurable fun b => f b s) : Measurable f :=
  Measurable.of_le_map <|
    iSup₂_le fun s hs =>
      MeasurableSpace.comap_le_iff_le_map.2 <| by rw [MeasurableSpace.map_comp] <;> exact h s hs
#align measure_theory.measure.measurable_of_measurable_coe MeasureTheory.Measure.measurable_of_measurable_coe

instance {α : Type _} {m : MeasurableSpace α} : MeasurableAdd₂ (Measure α) :=
  by
  refine' ⟨measure.measurable_of_measurable_coe _ fun s hs => _⟩
  simp_rw [measure.coe_add, Pi.add_apply]
  refine' Measurable.add _ _
  · exact (measure.measurable_coe hs).comp measurable_fst
  · exact (measure.measurable_coe hs).comp measurable_snd

#print MeasureTheory.Measure.measurable_measure /-
theorem measurable_measure {μ : α → Measure β} :
    Measurable μ ↔ ∀ (s : Set β) (hs : MeasurableSet s), Measurable fun b => μ b s :=
  ⟨fun hμ s hs => (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩
#align measure_theory.measure.measurable_measure MeasureTheory.Measure.measurable_measure
-/

/- warning: measure_theory.measure.measurable_map -> MeasureTheory.Measure.measurable_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (f : α -> β), (Measurable.{u1, u2} α β _inst_1 _inst_2 f) -> (Measurable.{u1, u2} (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.{u2} β _inst_2) (MeasureTheory.Measure.instMeasurableSpace.{u1} α _inst_1) (MeasureTheory.Measure.instMeasurableSpace.{u2} β _inst_2) (fun (μ : MeasureTheory.Measure.{u1} α _inst_1) => MeasureTheory.Measure.map.{u1, u2} α β _inst_2 _inst_1 f μ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (f : α -> β), (Measurable.{u2, u1} α β _inst_1 _inst_2 f) -> (Measurable.{u2, u1} (MeasureTheory.Measure.{u2} α _inst_1) (MeasureTheory.Measure.{u1} β _inst_2) (MeasureTheory.Measure.instMeasurableSpace.{u2} α _inst_1) (MeasureTheory.Measure.instMeasurableSpace.{u1} β _inst_2) (fun (μ : MeasureTheory.Measure.{u2} α _inst_1) => MeasureTheory.Measure.map.{u2, u1} α β _inst_2 _inst_1 f μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.measurable_map MeasureTheory.Measure.measurable_mapₓ'. -/
theorem measurable_map (f : α → β) (hf : Measurable f) : Measurable fun μ : Measure α => map f μ :=
  by
  refine' measurable_of_measurable_coe _ fun s hs => _
  simp_rw [map_apply hf hs]
  exact measurable_coe (hf hs)
#align measure_theory.measure.measurable_map MeasureTheory.Measure.measurable_map

#print MeasureTheory.Measure.measurable_dirac /-
theorem measurable_dirac : Measurable (Measure.dirac : α → Measure α) :=
  by
  refine' measurable_of_measurable_coe _ fun s hs => _
  simp_rw [dirac_apply' _ hs]
  exact measurable_one.indicator hs
#align measure_theory.measure.measurable_dirac MeasureTheory.Measure.measurable_dirac
-/

#print MeasureTheory.Measure.measurable_lintegral /-
theorem measurable_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun μ : Measure α => ∫⁻ x, f x ∂μ :=
  by
  simp only [lintegral_eq_supr_eapprox_lintegral, hf, simple_func.lintegral]
  refine' measurable_iSup fun n => Finset.measurable_sum _ fun i _ => _
  refine' Measurable.const_mul _ _
  exact measurable_coe ((simple_func.eapprox f n).measurableSet_preimage _)
#align measure_theory.measure.measurable_lintegral MeasureTheory.Measure.measurable_lintegral
-/

#print MeasureTheory.Measure.join /-
/-- Monadic join on `measure` in the category of measurable spaces and measurable
functions. -/
def join (m : Measure (Measure α)) : Measure α :=
  Measure.ofMeasurable (fun s hs => ∫⁻ μ, μ s ∂m)
    (by simp only [measure_empty, lintegral_const, MulZeroClass.zero_mul])
    (by
      intro f hf h
      simp_rw [measure_Union h hf]
      apply lintegral_tsum
      intro i; exact (measurable_coe (hf i)).AEMeasurable)
#align measure_theory.measure.join MeasureTheory.Measure.join
-/

#print MeasureTheory.Measure.join_apply /-
@[simp]
theorem join_apply {m : Measure (Measure α)} {s : Set α} (hs : MeasurableSet s) :
    join m s = ∫⁻ μ, μ s ∂m :=
  Measure.ofMeasurable_apply s hs
#align measure_theory.measure.join_apply MeasureTheory.Measure.join_apply
-/

#print MeasureTheory.Measure.join_zero /-
@[simp]
theorem join_zero : (0 : Measure (Measure α)).join = 0 := by ext1 s hs;
  simp only [hs, join_apply, lintegral_zero_measure, coe_zero, Pi.zero_apply]
#align measure_theory.measure.join_zero MeasureTheory.Measure.join_zero
-/

#print MeasureTheory.Measure.measurable_join /-
theorem measurable_join : Measurable (join : Measure (Measure α) → Measure α) :=
  measurable_of_measurable_coe _ fun s hs => by
    simp only [join_apply hs] <;> exact measurable_lintegral (measurable_coe hs)
#align measure_theory.measure.measurable_join MeasureTheory.Measure.measurable_join
-/

#print MeasureTheory.Measure.lintegral_join /-
theorem lintegral_join {m : Measure (Measure α)} {f : α → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂join m) = ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m :=
  by
  simp_rw [lintegral_eq_supr_eapprox_lintegral hf, simple_func.lintegral,
    join_apply (simple_func.measurable_set_preimage _ _)]
  suffices
    ∀ (s : ℕ → Finset ℝ≥0∞) (f : ℕ → ℝ≥0∞ → Measure α → ℝ≥0∞) (hf : ∀ n r, Measurable (f n r))
      (hm : Monotone fun n μ => ∑ r in s n, r * f n r μ),
      (⨆ n, ∑ r in s n, r * ∫⁻ μ, f n r μ ∂m) = ∫⁻ μ, ⨆ n, ∑ r in s n, r * f n r μ ∂m
    by
    refine'
      this (fun n => simple_func.range (simple_func.eapprox f n))
        (fun n r μ => μ (simple_func.eapprox f n ⁻¹' {r})) _ _
    · exact fun n r => measurable_coe (simple_func.measurable_set_preimage _ _)
    · exact fun n m h μ => simple_func.lintegral_mono (simple_func.monotone_eapprox _ h) le_rfl
  intro s f hf hm
  rw [lintegral_supr _ hm]
  swap; · exact fun n => Finset.measurable_sum _ fun r _ => (hf _ _).const_mul _
  congr
  funext n
  rw [lintegral_finset_sum (s n)]
  · simp_rw [lintegral_const_mul _ (hf _ _)]
  · exact fun r _ => (hf _ _).const_mul _
#align measure_theory.measure.lintegral_join MeasureTheory.Measure.lintegral_join
-/

#print MeasureTheory.Measure.bind /-
/-- Monadic bind on `measure`, only works in the category of measurable spaces and measurable
functions. When the function `f` is not measurable the result is not well defined. -/
def bind (m : Measure α) (f : α → Measure β) : Measure β :=
  join (map f m)
#align measure_theory.measure.bind MeasureTheory.Measure.bind
-/

#print MeasureTheory.Measure.bind_zero_left /-
@[simp]
theorem bind_zero_left (f : α → Measure β) : bind 0 f = 0 := by simp [bind]
#align measure_theory.measure.bind_zero_left MeasureTheory.Measure.bind_zero_left
-/

/- warning: measure_theory.measure.bind_zero_right -> MeasureTheory.Measure.bind_zero_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (m : MeasureTheory.Measure.{u1} α _inst_1), Eq.{succ u2} (MeasureTheory.Measure.{u2} β _inst_2) (MeasureTheory.Measure.bind.{u1, u2} α β _inst_1 _inst_2 m (OfNat.ofNat.{max u1 u2} (α -> (MeasureTheory.Measure.{u2} β _inst_2)) 0 (OfNat.mk.{max u1 u2} (α -> (MeasureTheory.Measure.{u2} β _inst_2)) 0 (Zero.zero.{max u1 u2} (α -> (MeasureTheory.Measure.{u2} β _inst_2)) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => MeasureTheory.Measure.{u2} β _inst_2) (fun (i : α) => MeasureTheory.Measure.instZero.{u2} β _inst_2)))))) (OfNat.ofNat.{u2} (MeasureTheory.Measure.{u2} β _inst_2) 0 (OfNat.mk.{u2} (MeasureTheory.Measure.{u2} β _inst_2) 0 (Zero.zero.{u2} (MeasureTheory.Measure.{u2} β _inst_2) (MeasureTheory.Measure.instZero.{u2} β _inst_2))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (m : MeasureTheory.Measure.{u2} α _inst_1), Eq.{succ u1} (MeasureTheory.Measure.{u1} β _inst_2) (MeasureTheory.Measure.bind.{u2, u1} α β _inst_1 _inst_2 m (OfNat.ofNat.{max u2 u1} (α -> (MeasureTheory.Measure.{u1} β _inst_2)) 0 (Zero.toOfNat0.{max u2 u1} (α -> (MeasureTheory.Measure.{u1} β _inst_2)) (Pi.instZero.{u2, u1} α (fun (a._@.Mathlib.MeasureTheory.Measure.GiryMonad._hyg.1222 : α) => MeasureTheory.Measure.{u1} β _inst_2) (fun (i : α) => MeasureTheory.Measure.instZero.{u1} β _inst_2))))) (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} β _inst_2) 0 (Zero.toOfNat0.{u1} (MeasureTheory.Measure.{u1} β _inst_2) (MeasureTheory.Measure.instZero.{u1} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.bind_zero_right MeasureTheory.Measure.bind_zero_rightₓ'. -/
@[simp]
theorem bind_zero_right (m : Measure α) : bind m (0 : α → Measure β) = 0 :=
  by
  ext1 s hs
  simp only [bind, hs, join_apply, coe_zero, Pi.zero_apply]
  rw [lintegral_map (measurable_coe hs) measurable_zero]
  simp only [Pi.zero_apply, coe_zero, lintegral_const, MulZeroClass.zero_mul]
#align measure_theory.measure.bind_zero_right MeasureTheory.Measure.bind_zero_right

/- warning: measure_theory.measure.bind_zero_right' -> MeasureTheory.Measure.bind_zero_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] (m : MeasureTheory.Measure.{u1} α _inst_1), Eq.{succ u2} (MeasureTheory.Measure.{u2} β _inst_2) (MeasureTheory.Measure.bind.{u1, u2} α β _inst_1 _inst_2 m (fun (_x : α) => OfNat.ofNat.{u2} (MeasureTheory.Measure.{u2} β _inst_2) 0 (OfNat.mk.{u2} (MeasureTheory.Measure.{u2} β _inst_2) 0 (Zero.zero.{u2} (MeasureTheory.Measure.{u2} β _inst_2) (MeasureTheory.Measure.instZero.{u2} β _inst_2))))) (OfNat.ofNat.{u2} (MeasureTheory.Measure.{u2} β _inst_2) 0 (OfNat.mk.{u2} (MeasureTheory.Measure.{u2} β _inst_2) 0 (Zero.zero.{u2} (MeasureTheory.Measure.{u2} β _inst_2) (MeasureTheory.Measure.instZero.{u2} β _inst_2))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] (m : MeasureTheory.Measure.{u2} α _inst_1), Eq.{succ u1} (MeasureTheory.Measure.{u1} β _inst_2) (MeasureTheory.Measure.bind.{u2, u1} α β _inst_1 _inst_2 m (fun (_x : α) => OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} β _inst_2) 0 (Zero.toOfNat0.{u1} (MeasureTheory.Measure.{u1} β _inst_2) (MeasureTheory.Measure.instZero.{u1} β _inst_2)))) (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} β _inst_2) 0 (Zero.toOfNat0.{u1} (MeasureTheory.Measure.{u1} β _inst_2) (MeasureTheory.Measure.instZero.{u1} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.bind_zero_right' MeasureTheory.Measure.bind_zero_right'ₓ'. -/
@[simp]
theorem bind_zero_right' (m : Measure α) : bind m (fun _ => 0 : α → Measure β) = 0 :=
  bind_zero_right m
#align measure_theory.measure.bind_zero_right' MeasureTheory.Measure.bind_zero_right'

/- warning: measure_theory.measure.bind_apply -> MeasureTheory.Measure.bind_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {m : MeasureTheory.Measure.{u1} α _inst_1} {f : α -> (MeasureTheory.Measure.{u2} β _inst_2)} {s : Set.{u2} β}, (MeasurableSet.{u2} β _inst_2 s) -> (Measurable.{u1, u2} α (MeasureTheory.Measure.{u2} β _inst_2) _inst_1 (MeasureTheory.Measure.instMeasurableSpace.{u2} β _inst_2) f) -> (Eq.{1} ENNReal (coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} β _inst_2) (fun (_x : MeasureTheory.Measure.{u2} β _inst_2) => (Set.{u2} β) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} β _inst_2) (MeasureTheory.Measure.bind.{u1, u2} α β _inst_1 _inst_2 m f) s) (MeasureTheory.lintegral.{u1} α _inst_1 m (fun (a : α) => coeFn.{succ u2, succ u2} (MeasureTheory.Measure.{u2} β _inst_2) (fun (_x : MeasureTheory.Measure.{u2} β _inst_2) => (Set.{u2} β) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u2} β _inst_2) (f a) s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {m : MeasureTheory.Measure.{u2} α _inst_1} {f : α -> (MeasureTheory.Measure.{u1} β _inst_2)} {s : Set.{u1} β}, (MeasurableSet.{u1} β _inst_2 s) -> (Measurable.{u2, u1} α (MeasureTheory.Measure.{u1} β _inst_2) _inst_1 (MeasureTheory.Measure.instMeasurableSpace.{u1} β _inst_2) f) -> (Eq.{1} ENNReal (MeasureTheory.OuterMeasure.measureOf.{u1} β (MeasureTheory.Measure.toOuterMeasure.{u1} β _inst_2 (MeasureTheory.Measure.bind.{u2, u1} α β _inst_1 _inst_2 m f)) s) (MeasureTheory.lintegral.{u2} α _inst_1 m (fun (a : α) => MeasureTheory.OuterMeasure.measureOf.{u1} β (MeasureTheory.Measure.toOuterMeasure.{u1} β _inst_2 (f a)) s)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.bind_apply MeasureTheory.Measure.bind_applyₓ'. -/
@[simp]
theorem bind_apply {m : Measure α} {f : α → Measure β} {s : Set β} (hs : MeasurableSet s)
    (hf : Measurable f) : bind m f s = ∫⁻ a, f a s ∂m := by
  rw [bind, join_apply hs, lintegral_map (measurable_coe hs) hf]
#align measure_theory.measure.bind_apply MeasureTheory.Measure.bind_apply

#print MeasureTheory.Measure.measurable_bind' /-
theorem measurable_bind' {g : α → Measure β} (hg : Measurable g) : Measurable fun m => bind m g :=
  measurable_join.comp (measurable_map _ hg)
#align measure_theory.measure.measurable_bind' MeasureTheory.Measure.measurable_bind'
-/

/- warning: measure_theory.measure.lintegral_bind -> MeasureTheory.Measure.lintegral_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {m : MeasureTheory.Measure.{u1} α _inst_1} {μ : α -> (MeasureTheory.Measure.{u2} β _inst_2)} {f : β -> ENNReal}, (Measurable.{u1, u2} α (MeasureTheory.Measure.{u2} β _inst_2) _inst_1 (MeasureTheory.Measure.instMeasurableSpace.{u2} β _inst_2) μ) -> (Measurable.{u2, 0} β ENNReal _inst_2 ENNReal.measurableSpace f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u2} β _inst_2 (MeasureTheory.Measure.bind.{u1, u2} α β _inst_1 _inst_2 m μ) (fun (x : β) => f x)) (MeasureTheory.lintegral.{u1} α _inst_1 m (fun (a : α) => MeasureTheory.lintegral.{u2} β _inst_2 (μ a) (fun (x : β) => f x))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {m : MeasureTheory.Measure.{u2} α _inst_1} {μ : α -> (MeasureTheory.Measure.{u1} β _inst_2)} {f : β -> ENNReal}, (Measurable.{u2, u1} α (MeasureTheory.Measure.{u1} β _inst_2) _inst_1 (MeasureTheory.Measure.instMeasurableSpace.{u1} β _inst_2) μ) -> (Measurable.{u1, 0} β ENNReal _inst_2 ENNReal.measurableSpace f) -> (Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} β _inst_2 (MeasureTheory.Measure.bind.{u2, u1} α β _inst_1 _inst_2 m μ) (fun (x : β) => f x)) (MeasureTheory.lintegral.{u2} α _inst_1 m (fun (a : α) => MeasureTheory.lintegral.{u1} β _inst_2 (μ a) (fun (x : β) => f x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.lintegral_bind MeasureTheory.Measure.lintegral_bindₓ'. -/
theorem lintegral_bind {m : Measure α} {μ : α → Measure β} {f : β → ℝ≥0∞} (hμ : Measurable μ)
    (hf : Measurable f) : (∫⁻ x, f x ∂bind m μ) = ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m :=
  (lintegral_join hf).trans (lintegral_map (measurable_lintegral hf) hμ)
#align measure_theory.measure.lintegral_bind MeasureTheory.Measure.lintegral_bind

/- warning: measure_theory.measure.bind_bind -> MeasureTheory.Measure.bind_bind is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {γ : Type.{u3}} [_inst_3 : MeasurableSpace.{u3} γ] {m : MeasureTheory.Measure.{u1} α _inst_1} {f : α -> (MeasureTheory.Measure.{u2} β _inst_2)} {g : β -> (MeasureTheory.Measure.{u3} γ _inst_3)}, (Measurable.{u1, u2} α (MeasureTheory.Measure.{u2} β _inst_2) _inst_1 (MeasureTheory.Measure.instMeasurableSpace.{u2} β _inst_2) f) -> (Measurable.{u2, u3} β (MeasureTheory.Measure.{u3} γ _inst_3) _inst_2 (MeasureTheory.Measure.instMeasurableSpace.{u3} γ _inst_3) g) -> (Eq.{succ u3} (MeasureTheory.Measure.{u3} γ _inst_3) (MeasureTheory.Measure.bind.{u2, u3} β γ _inst_2 _inst_3 (MeasureTheory.Measure.bind.{u1, u2} α β _inst_1 _inst_2 m f) g) (MeasureTheory.Measure.bind.{u1, u3} α γ _inst_1 _inst_3 m (fun (a : α) => MeasureTheory.Measure.bind.{u2, u3} β γ _inst_2 _inst_3 (f a) g)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {γ : Type.{u3}} [_inst_3 : MeasurableSpace.{u3} γ] {m : MeasureTheory.Measure.{u2} α _inst_1} {f : α -> (MeasureTheory.Measure.{u1} β _inst_2)} {g : β -> (MeasureTheory.Measure.{u3} γ _inst_3)}, (Measurable.{u2, u1} α (MeasureTheory.Measure.{u1} β _inst_2) _inst_1 (MeasureTheory.Measure.instMeasurableSpace.{u1} β _inst_2) f) -> (Measurable.{u1, u3} β (MeasureTheory.Measure.{u3} γ _inst_3) _inst_2 (MeasureTheory.Measure.instMeasurableSpace.{u3} γ _inst_3) g) -> (Eq.{succ u3} (MeasureTheory.Measure.{u3} γ _inst_3) (MeasureTheory.Measure.bind.{u1, u3} β γ _inst_2 _inst_3 (MeasureTheory.Measure.bind.{u2, u1} α β _inst_1 _inst_2 m f) g) (MeasureTheory.Measure.bind.{u2, u3} α γ _inst_1 _inst_3 m (fun (a : α) => MeasureTheory.Measure.bind.{u1, u3} β γ _inst_2 _inst_3 (f a) g)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.bind_bind MeasureTheory.Measure.bind_bindₓ'. -/
theorem bind_bind {γ} [MeasurableSpace γ] {m : Measure α} {f : α → Measure β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) : bind (bind m f) g = bind m fun a => bind (f a) g :=
  by
  ext1 s hs
  simp_rw [bind_apply hs hg, bind_apply hs ((measurable_bind' hg).comp hf),
    lintegral_bind hf ((measurable_coe hs).comp hg), bind_apply hs hg]
#align measure_theory.measure.bind_bind MeasureTheory.Measure.bind_bind

#print MeasureTheory.Measure.bind_dirac /-
theorem bind_dirac {f : α → Measure β} (hf : Measurable f) (a : α) : bind (dirac a) f = f a := by
  ext1 s hs; rw [bind_apply hs hf, lintegral_dirac' a ((measurable_coe hs).comp hf)]
#align measure_theory.measure.bind_dirac MeasureTheory.Measure.bind_dirac
-/

#print MeasureTheory.Measure.dirac_bind /-
theorem dirac_bind {m : Measure α} : bind m dirac = m :=
  by
  ext1 s hs
  simp only [bind_apply hs measurable_dirac, dirac_apply' _ hs, lintegral_indicator 1 hs,
    Pi.one_apply, lintegral_one, restrict_apply, MeasurableSet.univ, univ_inter]
#align measure_theory.measure.dirac_bind MeasureTheory.Measure.dirac_bind
-/

#print MeasureTheory.Measure.join_eq_bind /-
theorem join_eq_bind (μ : Measure (Measure α)) : join μ = bind μ id := by rw [bind, map_id]
#align measure_theory.measure.join_eq_bind MeasureTheory.Measure.join_eq_bind
-/

/- warning: measure_theory.measure.join_map_map -> MeasureTheory.Measure.join_map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] [_inst_2 : MeasurableSpace.{u2} β] {f : α -> β}, (Measurable.{u1, u2} α β _inst_1 _inst_2 f) -> (forall (μ : MeasureTheory.Measure.{u1} (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.instMeasurableSpace.{u1} α _inst_1)), Eq.{succ u2} (MeasureTheory.Measure.{u2} β _inst_2) (MeasureTheory.Measure.join.{u2} β _inst_2 (MeasureTheory.Measure.map.{u1, u2} (MeasureTheory.Measure.{u1} α _inst_1) (MeasureTheory.Measure.{u2} β _inst_2) (MeasureTheory.Measure.instMeasurableSpace.{u2} β _inst_2) (MeasureTheory.Measure.instMeasurableSpace.{u1} α _inst_1) (MeasureTheory.Measure.map.{u1, u2} α β _inst_2 _inst_1 f) μ)) (MeasureTheory.Measure.map.{u1, u2} α β _inst_2 _inst_1 f (MeasureTheory.Measure.join.{u1} α _inst_1 μ)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] [_inst_2 : MeasurableSpace.{u1} β] {f : α -> β}, (Measurable.{u2, u1} α β _inst_1 _inst_2 f) -> (forall (μ : MeasureTheory.Measure.{u2} (MeasureTheory.Measure.{u2} α _inst_1) (MeasureTheory.Measure.instMeasurableSpace.{u2} α _inst_1)), Eq.{succ u1} (MeasureTheory.Measure.{u1} β _inst_2) (MeasureTheory.Measure.join.{u1} β _inst_2 (MeasureTheory.Measure.map.{u2, u1} (MeasureTheory.Measure.{u2} α _inst_1) (MeasureTheory.Measure.{u1} β _inst_2) (MeasureTheory.Measure.instMeasurableSpace.{u1} β _inst_2) (MeasureTheory.Measure.instMeasurableSpace.{u2} α _inst_1) (MeasureTheory.Measure.map.{u2, u1} α β _inst_2 _inst_1 f) μ)) (MeasureTheory.Measure.map.{u2, u1} α β _inst_2 _inst_1 f (MeasureTheory.Measure.join.{u2} α _inst_1 μ)))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure.join_map_map MeasureTheory.Measure.join_map_mapₓ'. -/
theorem join_map_map {f : α → β} (hf : Measurable f) (μ : Measure (Measure α)) :
    join (map (map f) μ) = map f (join μ) := by
  ext1 s hs
  rw [join_apply hs, map_apply hf hs, join_apply (hf hs),
    lintegral_map (measurable_coe hs) (measurable_map f hf)]
  simp_rw [map_apply hf hs]
#align measure_theory.measure.join_map_map MeasureTheory.Measure.join_map_map

#print MeasureTheory.Measure.join_map_join /-
theorem join_map_join (μ : Measure (Measure (Measure α))) : join (map join μ) = join (join μ) :=
  by
  show bind μ join = join (join μ)
  rw [join_eq_bind, join_eq_bind, bind_bind measurable_id measurable_id]
  apply congr_arg (bind μ)
  funext ν
  exact join_eq_bind ν
#align measure_theory.measure.join_map_join MeasureTheory.Measure.join_map_join
-/

#print MeasureTheory.Measure.join_map_dirac /-
theorem join_map_dirac (μ : Measure α) : join (map dirac μ) = μ :=
  dirac_bind
#align measure_theory.measure.join_map_dirac MeasureTheory.Measure.join_map_dirac
-/

#print MeasureTheory.Measure.join_dirac /-
theorem join_dirac (μ : Measure α) : join (dirac μ) = μ :=
  (join_eq_bind (dirac μ)).trans (bind_dirac measurable_id _)
#align measure_theory.measure.join_dirac MeasureTheory.Measure.join_dirac
-/

end Measure

end MeasureTheory

