/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.function.strongly_measurable.basic
! leanprover-community/mathlib commit ef95945cd48c932c9e034872bd25c3c220d9c946
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.FiniteDimension
import Mathbin.Analysis.NormedSpace.BoundedLinearMaps
import Mathbin.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathbin.MeasureTheory.Integral.Lebesgue
import Mathbin.MeasureTheory.Function.SimpleFuncDense

/-!
# Strongly measurable and finitely strongly measurable functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A function `f` is said to be strongly measurable if `f` is the sequential limit of simple functions.
It is said to be finitely strongly measurable with respect to a measure `μ` if the supports
of those simple functions have finite measure. We also provide almost everywhere versions of
these notions.

Almost everywhere strongly measurable functions form the largest class of functions that can be
integrated using the Bochner integral.

If the target space has a second countable topology, strongly measurable and measurable are
equivalent.

If the measure is sigma-finite, strongly measurable and finitely strongly measurable are equivalent.

The main property of finitely strongly measurable functions is
`fin_strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that the
function is supported on `t` and `μ.restrict t` is sigma-finite. As a consequence, we can prove some
results for those functions as if the measure was sigma-finite.

## Main definitions

* `strongly_measurable f`: `f : α → β` is the limit of a sequence `fs : ℕ → simple_func α β`.
* `fin_strongly_measurable f μ`: `f : α → β` is the limit of a sequence `fs : ℕ → simple_func α β`
  such that for all `n ∈ ℕ`, the measure of the support of `fs n` is finite.
* `ae_strongly_measurable f μ`: `f` is almost everywhere equal to a `strongly_measurable` function.
* `ae_fin_strongly_measurable f μ`: `f` is almost everywhere equal to a `fin_strongly_measurable`
  function.

* `ae_fin_strongly_measurable.sigma_finite_set`: a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

## Main statements

* `ae_fin_strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

We provide a solid API for strongly measurable functions, and for almost everywhere strongly
measurable functions, as a basis for the Bochner integral.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.

-/


open MeasureTheory Filter TopologicalSpace Function Set MeasureTheory.Measure

open ENNReal Topology MeasureTheory NNReal BigOperators

#print SecondCountableTopologyEither /-
/-- The typeclass `second_countable_topology_either α β` registers the fact that at least one of
the two spaces has second countable topology. This is the right assumption to ensure that continuous
maps from `α` to `β` are strongly measurable. -/
class SecondCountableTopologyEither (α β : Type _) [TopologicalSpace α] [TopologicalSpace β] :
  Prop where
  out : SecondCountableTopology α ∨ SecondCountableTopology β
#align second_countable_topology_either SecondCountableTopologyEither
-/

#print secondCountableTopologyEither_of_left /-
instance (priority := 100) secondCountableTopologyEither_of_left (α β : Type _) [TopologicalSpace α]
    [TopologicalSpace β] [SecondCountableTopology α] : SecondCountableTopologyEither α β
    where out := Or.inl (by infer_instance)
#align second_countable_topology_either_of_left secondCountableTopologyEither_of_left
-/

#print secondCountableTopologyEither_of_right /-
instance (priority := 100) secondCountableTopologyEither_of_right (α β : Type _)
    [TopologicalSpace α] [TopologicalSpace β] [SecondCountableTopology β] :
    SecondCountableTopologyEither α β where out := Or.inr (by infer_instance)
#align second_countable_topology_either_of_right secondCountableTopologyEither_of_right
-/

variable {α β γ ι : Type _} [Countable ι]

namespace MeasureTheory

-- mathport name: «expr →ₛ »
local infixr:25 " →ₛ " => SimpleFunc

section Definitions

variable [TopologicalSpace β]

#print MeasureTheory.StronglyMeasurable /-
/-- A function is `strongly_measurable` if it is the limit of simple functions. -/
def StronglyMeasurable [MeasurableSpace α] (f : α → β) : Prop :=
  ∃ fs : ℕ → α →ₛ β, ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))
#align measure_theory.strongly_measurable MeasureTheory.StronglyMeasurable
-/

-- mathport name: strongly_measurable_of
scoped notation "strongly_measurable[" m "]" => @MeasureTheory.StronglyMeasurable _ _ _ m

#print MeasureTheory.FinStronglyMeasurable /-
/-- A function is `fin_strongly_measurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
def FinStronglyMeasurable [Zero β] {m0 : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop :=
  ∃ fs : ℕ → α →ₛ β, (∀ n, μ (support (fs n)) < ∞) ∧ ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))
#align measure_theory.fin_strongly_measurable MeasureTheory.FinStronglyMeasurable
-/

#print MeasureTheory.AEStronglyMeasurable /-
/-- A function is `ae_strongly_measurable` with respect to a measure `μ` if it is almost everywhere
equal to the limit of a sequence of simple functions. -/
def AEStronglyMeasurable {m0 : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop :=
  ∃ g, StronglyMeasurable g ∧ f =ᵐ[μ] g
#align measure_theory.ae_strongly_measurable MeasureTheory.AEStronglyMeasurable
-/

#print MeasureTheory.AEFinStronglyMeasurable /-
/-- A function is `ae_fin_strongly_measurable` with respect to a measure if it is almost everywhere
equal to the limit of a sequence of simple functions with support with finite measure. -/
def AEFinStronglyMeasurable [Zero β] {m0 : MeasurableSpace α} (f : α → β) (μ : Measure α) : Prop :=
  ∃ g, FinStronglyMeasurable g μ ∧ f =ᵐ[μ] g
#align measure_theory.ae_fin_strongly_measurable MeasureTheory.AEFinStronglyMeasurable
-/

end Definitions

open MeasureTheory

/-! ## Strongly measurable functions -/


/- warning: measure_theory.strongly_measurable.ae_strongly_measurable -> MeasureTheory.StronglyMeasurable.aestronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {μ : MeasureTheory.Measure.{u1} α m0}, (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m0 f) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m0 f μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α m0}, (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m0 f) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m0 f μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.ae_strongly_measurable MeasureTheory.StronglyMeasurable.aestronglyMeasurableₓ'. -/
protected theorem StronglyMeasurable.aestronglyMeasurable {α β} {m0 : MeasurableSpace α}
    [TopologicalSpace β] {f : α → β} {μ : Measure α} (hf : StronglyMeasurable f) :
    AEStronglyMeasurable f μ :=
  ⟨f, hf, EventuallyEq.refl _ _⟩
#align measure_theory.strongly_measurable.ae_strongly_measurable MeasureTheory.StronglyMeasurable.aestronglyMeasurable

/- warning: measure_theory.subsingleton.strongly_measurable -> MeasureTheory.Subsingleton.stronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Subsingleton.{succ u2} β] (f : α -> β), MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_3 _inst_2 f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : MeasurableSpace.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : Subsingleton.{succ u1} β] (f : α -> β), MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_3 _inst_2 f
Case conversion may be inaccurate. Consider using '#align measure_theory.subsingleton.strongly_measurable MeasureTheory.Subsingleton.stronglyMeasurableₓ'. -/
@[simp]
theorem Subsingleton.stronglyMeasurable {α β} [MeasurableSpace α] [TopologicalSpace β]
    [Subsingleton β] (f : α → β) : StronglyMeasurable f :=
  by
  let f_sf : α →ₛ β := ⟨f, fun x => _, Set.Subsingleton.finite Set.subsingleton_of_subsingleton⟩
  · exact ⟨fun n => f_sf, fun x => tendsto_const_nhds⟩
  · have h_univ : f ⁻¹' {x} = Set.univ := by
      ext1 y
      simp
    rw [h_univ]
    exact MeasurableSet.univ
#align measure_theory.subsingleton.strongly_measurable MeasureTheory.Subsingleton.stronglyMeasurable

/- warning: measure_theory.simple_func.strongly_measurable -> MeasureTheory.SimpleFunc.stronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] (f : MeasureTheory.SimpleFunc.{u1, u2} α m β), MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] (f : MeasureTheory.SimpleFunc.{u2, u1} α m β), MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m (MeasureTheory.SimpleFunc.toFun.{u2, u1} α m β f)
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.strongly_measurable MeasureTheory.SimpleFunc.stronglyMeasurableₓ'. -/
theorem SimpleFunc.stronglyMeasurable {α β} {m : MeasurableSpace α} [TopologicalSpace β]
    (f : α →ₛ β) : StronglyMeasurable f :=
  ⟨fun _ => f, fun x => tendsto_const_nhds⟩
#align measure_theory.simple_func.strongly_measurable MeasureTheory.SimpleFunc.stronglyMeasurable

/- warning: measure_theory.strongly_measurable_of_is_empty -> MeasureTheory.stronglyMeasurable_of_isEmpty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : IsEmpty.{succ u1} α] {m : MeasurableSpace.{u1} α} [_inst_3 : TopologicalSpace.{u2} β] (f : α -> β), MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_3 m f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : IsEmpty.{succ u2} α] {m : MeasurableSpace.{u2} α} [_inst_3 : TopologicalSpace.{u1} β] (f : α -> β), MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_3 m f
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable_of_is_empty MeasureTheory.stronglyMeasurable_of_isEmptyₓ'. -/
theorem stronglyMeasurable_of_isEmpty [IsEmpty α] {m : MeasurableSpace α} [TopologicalSpace β]
    (f : α → β) : StronglyMeasurable f :=
  ⟨fun n => SimpleFunc.ofIsEmpty, isEmptyElim⟩
#align measure_theory.strongly_measurable_of_is_empty MeasureTheory.stronglyMeasurable_of_isEmpty

/- warning: measure_theory.strongly_measurable_const -> MeasureTheory.stronglyMeasurable_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] {b : β}, MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m (fun (a : α) => b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] {b : β}, MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m (fun (a : α) => b)
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable_const MeasureTheory.stronglyMeasurable_constₓ'. -/
theorem stronglyMeasurable_const {α β} {m : MeasurableSpace α} [TopologicalSpace β] {b : β} :
    StronglyMeasurable fun a : α => b :=
  ⟨fun n => SimpleFunc.const α b, fun a => tendsto_const_nhds⟩
#align measure_theory.strongly_measurable_const MeasureTheory.stronglyMeasurable_const

/- warning: measure_theory.strongly_measurable_one -> MeasureTheory.stronglyMeasurable_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : One.{u2} β], MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m (OfNat.ofNat.{max u1 u2} (α -> β) 1 (OfNat.mk.{max u1 u2} (α -> β) 1 (One.one.{max u1 u2} (α -> β) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_3)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : One.{u1} β], MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m (OfNat.ofNat.{max u2 u1} (α -> β) 1 (One.toOfNat1.{max u2 u1} (α -> β) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic._hyg.1583 : α) => β) (fun (i : α) => _inst_3))))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable_one MeasureTheory.stronglyMeasurable_oneₓ'. -/
@[to_additive]
theorem stronglyMeasurable_one {α β} {m : MeasurableSpace α} [TopologicalSpace β] [One β] :
    StronglyMeasurable (1 : α → β) :=
  @stronglyMeasurable_const _ _ _ _ 1
#align measure_theory.strongly_measurable_one MeasureTheory.stronglyMeasurable_one
#align measure_theory.strongly_measurable_zero MeasureTheory.stronglyMeasurable_zero

/- warning: measure_theory.strongly_measurable_const' -> MeasureTheory.stronglyMeasurable_const' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (forall (x : α) (y : α), Eq.{succ u2} β (f x) (f y)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (forall (x : α) (y : α), Eq.{succ u1} β (f x) (f y)) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f)
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable_const' MeasureTheory.stronglyMeasurable_const'ₓ'. -/
/-- A version of `strongly_measurable_const` that assumes `f x = f y` for all `x, y`.
This version works for functions between empty types. -/
theorem stronglyMeasurable_const' {α β} {m : MeasurableSpace α} [TopologicalSpace β] {f : α → β}
    (hf : ∀ x y, f x = f y) : StronglyMeasurable f :=
  by
  cases isEmpty_or_nonempty α
  · exact strongly_measurable_of_is_empty f
  · convert strongly_measurable_const
    exact funext fun x => hf x h.some
#align measure_theory.strongly_measurable_const' MeasureTheory.stronglyMeasurable_const'

/- warning: measure_theory.subsingleton.strongly_measurable' -> MeasureTheory.Subsingleton.stronglyMeasurable' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : Subsingleton.{succ u1} α] (f : α -> β), MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_3 _inst_2 f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : MeasurableSpace.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : Subsingleton.{succ u2} α] (f : α -> β), MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_3 _inst_2 f
Case conversion may be inaccurate. Consider using '#align measure_theory.subsingleton.strongly_measurable' MeasureTheory.Subsingleton.stronglyMeasurable'ₓ'. -/
@[simp]
theorem Subsingleton.stronglyMeasurable' {α β} [MeasurableSpace α] [TopologicalSpace β]
    [Subsingleton α] (f : α → β) : StronglyMeasurable f :=
  stronglyMeasurable_const' fun x y => by rw [Subsingleton.elim x y]
#align measure_theory.subsingleton.strongly_measurable' MeasureTheory.Subsingleton.stronglyMeasurable'

namespace StronglyMeasurable

variable {f g : α → β}

section BasicPropertiesInAnyTopologicalSpace

variable [TopologicalSpace β]

#print MeasureTheory.StronglyMeasurable.approx /-
/-- A sequence of simple functions such that `∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x))`.
That property is given by `strongly_measurable.tendsto_approx`. -/
protected noncomputable def approx {m : MeasurableSpace α} (hf : StronglyMeasurable f) :
    ℕ → α →ₛ β :=
  hf.some
#align measure_theory.strongly_measurable.approx MeasureTheory.StronglyMeasurable.approx
-/

/- warning: measure_theory.strongly_measurable.tendsto_approx -> MeasureTheory.StronglyMeasurable.tendsto_approx is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_2 : TopologicalSpace.{u2} β] {m : MeasurableSpace.{u1} α} (hf : MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) (x : α), Filter.Tendsto.{0, u2} Nat β (fun (n : Nat) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m) (MeasureTheory.StronglyMeasurable.approx.{u1, u2} α β f _inst_2 m hf n) x) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u2} β _inst_2 (f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} [_inst_2 : TopologicalSpace.{u1} β] {m : MeasurableSpace.{u2} α} (hf : MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) (x : α), Filter.Tendsto.{0, u1} Nat β (fun (n : Nat) => MeasureTheory.SimpleFunc.toFun.{u2, u1} α m β (MeasureTheory.StronglyMeasurable.approx.{u2, u1} α β f _inst_2 m hf n) x) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} β _inst_2 (f x))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.tendsto_approx MeasureTheory.StronglyMeasurable.tendsto_approxₓ'. -/
protected theorem tendsto_approx {m : MeasurableSpace α} (hf : StronglyMeasurable f) :
    ∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x)) :=
  hf.choose_spec
#align measure_theory.strongly_measurable.tendsto_approx MeasureTheory.StronglyMeasurable.tendsto_approx

#print MeasureTheory.StronglyMeasurable.approxBounded /-
/-- Similar to `strongly_measurable.approx`, but enforces that the norm of every function in the
sequence is less than `c` everywhere. If `‖f x‖ ≤ c` this sequence of simple functions verifies
`tendsto (λ n, hf.approx_bounded n x) at_top (𝓝 (f x))`. -/
noncomputable def approxBounded {m : MeasurableSpace α} [Norm β] [SMul ℝ β]
    (hf : StronglyMeasurable f) (c : ℝ) : ℕ → SimpleFunc α β := fun n =>
  (hf.approx n).map fun x => min 1 (c / ‖x‖) • x
#align measure_theory.strongly_measurable.approx_bounded MeasureTheory.StronglyMeasurable.approxBounded
-/

/- warning: measure_theory.strongly_measurable.tendsto_approx_bounded_of_norm_le -> MeasureTheory.StronglyMeasurable.tendsto_approxBounded_of_norm_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_3 : NormedAddCommGroup.{u2} β] [_inst_4 : NormedSpace.{0, u2} Real β Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)] {m : MeasurableSpace.{u1} α} (hf : MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))) m f) {c : Real} {x : α}, (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} β (NormedAddCommGroup.toHasNorm.{u2} β _inst_3) (f x)) c) -> (Filter.Tendsto.{0, u2} Nat β (fun (n : Nat) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m) (MeasureTheory.StronglyMeasurable.approxBounded.{u1, u2} α β f (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))) m (NormedAddCommGroup.toHasNorm.{u2} β _inst_3) (SMulZeroClass.toHasSmul.{0, u2} Real β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))))) (SMulWithZero.toSmulZeroClass.{0, u2} Real β (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real β (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))))) (Module.toMulActionWithZero.{0, u2} Real β (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3))) (NormedSpace.toModule.{0, u2} Real β Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3) _inst_4))))) hf c n) x) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))) (f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_3 : NormedAddCommGroup.{u2} β] [_inst_4 : NormedSpace.{0, u2} Real β Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)] {m : MeasurableSpace.{u1} α} (hf : MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))) m f) {c : Real} {x : α}, (LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} β (NormedAddCommGroup.toNorm.{u2} β _inst_3) (f x)) c) -> (Filter.Tendsto.{0, u2} Nat β (fun (n : Nat) => MeasureTheory.SimpleFunc.toFun.{u1, u2} α m β (MeasureTheory.StronglyMeasurable.approxBounded.{u1, u2} α β f (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))) m (NormedAddCommGroup.toNorm.{u2} β _inst_3) (SMulZeroClass.toSMul.{0, u2} Real β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (NormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)))))) (SMulWithZero.toSMulZeroClass.{0, u2} Real β Real.instZeroReal (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (NormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real β Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (NormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)))))) (Module.toMulActionWithZero.{0, u2} Real β Real.semiring (AddCommGroup.toAddCommMonoid.{u2} β (NormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)) (NormedSpace.toModule.{0, u2} Real β Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3) _inst_4))))) hf c n) x) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))) (f x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.tendsto_approx_bounded_of_norm_le MeasureTheory.StronglyMeasurable.tendsto_approxBounded_of_norm_leₓ'. -/
theorem tendsto_approxBounded_of_norm_le {β} {f : α → β} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {m : MeasurableSpace α} (hf : strongly_measurable[m] f) {c : ℝ} {x : α} (hfx : ‖f x‖ ≤ c) :
    Tendsto (fun n => hf.approxBounded c n x) atTop (𝓝 (f x)) :=
  by
  have h_tendsto := hf.tendsto_approx x
  simp only [strongly_measurable.approx_bounded, simple_func.coe_map, Function.comp_apply]
  by_cases hfx0 : ‖f x‖ = 0
  · rw [norm_eq_zero] at hfx0
    rw [hfx0] at h_tendsto⊢
    have h_tendsto_norm : tendsto (fun n => ‖hf.approx n x‖) at_top (𝓝 0) :=
      by
      convert h_tendsto.norm
      rw [norm_zero]
    refine' squeeze_zero_norm (fun n => _) h_tendsto_norm
    calc
      ‖min 1 (c / ‖hf.approx n x‖) • hf.approx n x‖ =
          ‖min 1 (c / ‖hf.approx n x‖)‖ * ‖hf.approx n x‖ :=
        norm_smul _ _
      _ ≤ ‖(1 : ℝ)‖ * ‖hf.approx n x‖ :=
        by
        refine' mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [norm_one, Real.norm_of_nonneg]
        · exact min_le_left _ _
        · exact le_min zero_le_one (div_nonneg ((norm_nonneg _).trans hfx) (norm_nonneg _))
      _ = ‖hf.approx n x‖ := by rw [norm_one, one_mul]
      
  rw [← one_smul ℝ (f x)]
  refine' tendsto.smul _ h_tendsto
  have : min 1 (c / ‖f x‖) = 1 :=
    by
    rw [min_eq_left_iff, one_le_div (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hfx0))]
    exact hfx
  nth_rw 1 [this.symm]
  refine' tendsto.min tendsto_const_nhds _
  refine' tendsto.div tendsto_const_nhds h_tendsto.norm hfx0
#align measure_theory.strongly_measurable.tendsto_approx_bounded_of_norm_le MeasureTheory.StronglyMeasurable.tendsto_approxBounded_of_norm_le

/- warning: measure_theory.strongly_measurable.tendsto_approx_bounded_ae -> MeasureTheory.StronglyMeasurable.tendsto_approxBounded_ae is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_3 : NormedAddCommGroup.{u2} β] [_inst_4 : NormedSpace.{0, u2} Real β Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)] {m : MeasurableSpace.{u1} α} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (hf : MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))) m f) {c : Real}, (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.hasLe (Norm.norm.{u2} β (NormedAddCommGroup.toHasNorm.{u2} β _inst_3) (f x)) c) (MeasureTheory.Measure.ae.{u1} α m0 μ)) -> (Filter.Eventually.{u1} α (fun (x : α) => Filter.Tendsto.{0, u2} Nat β (fun (n : Nat) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m) (MeasureTheory.StronglyMeasurable.approxBounded.{u1, u2} α β f (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))) m (NormedAddCommGroup.toHasNorm.{u2} β _inst_3) (SMulZeroClass.toHasSmul.{0, u2} Real β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))))) (SMulWithZero.toSmulZeroClass.{0, u2} Real β (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real β (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))))) (Module.toMulActionWithZero.{0, u2} Real β (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3))) (NormedSpace.toModule.{0, u2} Real β Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3) _inst_4))))) hf c n) x) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))) (f x))) (MeasureTheory.Measure.ae.{u1} α m0 μ))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_3 : NormedAddCommGroup.{u2} β] [_inst_4 : NormedSpace.{0, u2} Real β Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)] {m : MeasurableSpace.{u1} α} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} (hf : MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))) m f) {c : Real}, (Filter.Eventually.{u1} α (fun (x : α) => LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} β (NormedAddCommGroup.toNorm.{u2} β _inst_3) (f x)) c) (MeasureTheory.Measure.ae.{u1} α m0 μ)) -> (Filter.Eventually.{u1} α (fun (x : α) => Filter.Tendsto.{0, u2} Nat β (fun (n : Nat) => MeasureTheory.SimpleFunc.toFun.{u1, u2} α m β (MeasureTheory.StronglyMeasurable.approxBounded.{u1, u2} α β f (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))) m (NormedAddCommGroup.toNorm.{u2} β _inst_3) (SMulZeroClass.toSMul.{0, u2} Real β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (NormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)))))) (SMulWithZero.toSMulZeroClass.{0, u2} Real β Real.instZeroReal (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (NormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real β Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (NormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)))))) (Module.toMulActionWithZero.{0, u2} Real β Real.semiring (AddCommGroup.toAddCommMonoid.{u2} β (NormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)) (NormedSpace.toModule.{0, u2} Real β Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3) _inst_4))))) hf c n) x) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u2} β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} β _inst_3)))) (f x))) (MeasureTheory.Measure.ae.{u1} α m0 μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.tendsto_approx_bounded_ae MeasureTheory.StronglyMeasurable.tendsto_approxBounded_aeₓ'. -/
theorem tendsto_approxBounded_ae {β} {f : α → β} [NormedAddCommGroup β] [NormedSpace ℝ β]
    {m m0 : MeasurableSpace α} {μ : Measure α} (hf : strongly_measurable[m] f) {c : ℝ}
    (hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ c) :
    ∀ᵐ x ∂μ, Tendsto (fun n => hf.approxBounded c n x) atTop (𝓝 (f x)) := by
  filter_upwards [hf_bound]with x hfx using tendsto_approx_bounded_of_norm_le hf hfx
#align measure_theory.strongly_measurable.tendsto_approx_bounded_ae MeasureTheory.StronglyMeasurable.tendsto_approxBounded_ae

/- warning: measure_theory.strongly_measurable.norm_approx_bounded_le -> MeasureTheory.StronglyMeasurable.norm_approxBounded_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_3 : SeminormedAddCommGroup.{u2} β] [_inst_4 : NormedSpace.{0, u2} Real β Real.normedField _inst_3] {m : MeasurableSpace.{u1} α} {c : Real} (hf : MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_3))) m f), (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) c) -> (forall (n : Nat) (x : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} β (SeminormedAddCommGroup.toHasNorm.{u2} β _inst_3) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m) (MeasureTheory.StronglyMeasurable.approxBounded.{u1, u2} α β f (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_3))) m (SeminormedAddCommGroup.toHasNorm.{u2} β _inst_3) (SMulZeroClass.toHasSmul.{0, u2} Real β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β _inst_3))))) (SMulWithZero.toSmulZeroClass.{0, u2} Real β (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β _inst_3))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real β (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β _inst_3))))) (Module.toMulActionWithZero.{0, u2} Real β (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)) (NormedSpace.toModule.{0, u2} Real β Real.normedField _inst_3 _inst_4))))) hf c n) x)) c)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_3 : SeminormedAddCommGroup.{u2} β] [_inst_4 : NormedSpace.{0, u2} Real β Real.normedField _inst_3] {m : MeasurableSpace.{u1} α} {c : Real} (hf : MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_3))) m f), (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) c) -> (forall (n : Nat) (x : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} β (SeminormedAddCommGroup.toNorm.{u2} β _inst_3) (MeasureTheory.SimpleFunc.toFun.{u1, u2} α m β (MeasureTheory.StronglyMeasurable.approxBounded.{u1, u2} α β f (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_3))) m (SeminormedAddCommGroup.toNorm.{u2} β _inst_3) (SMulZeroClass.toSMul.{0, u2} Real β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)))))) (SMulWithZero.toSMulZeroClass.{0, u2} Real β Real.instZeroReal (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real β Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)))))) (Module.toMulActionWithZero.{0, u2} Real β Real.semiring (AddCommGroup.toAddCommMonoid.{u2} β (SeminormedAddCommGroup.toAddCommGroup.{u2} β _inst_3)) (NormedSpace.toModule.{0, u2} Real β Real.normedField _inst_3 _inst_4))))) hf c n) x)) c)
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.norm_approx_bounded_le MeasureTheory.StronglyMeasurable.norm_approxBounded_leₓ'. -/
theorem norm_approxBounded_le {β} {f : α → β} [SeminormedAddCommGroup β] [NormedSpace ℝ β]
    {m : MeasurableSpace α} {c : ℝ} (hf : strongly_measurable[m] f) (hc : 0 ≤ c) (n : ℕ) (x : α) :
    ‖hf.approxBounded c n x‖ ≤ c :=
  by
  simp only [strongly_measurable.approx_bounded, simple_func.coe_map, Function.comp_apply]
  refine' (norm_smul_le _ _).trans _
  by_cases h0 : ‖hf.approx n x‖ = 0
  · simp only [h0, div_zero, min_eq_right, zero_le_one, norm_zero, MulZeroClass.mul_zero]
    exact hc
  cases le_total ‖hf.approx n x‖ c
  · rw [min_eq_left _]
    · simpa only [norm_one, one_mul] using h
    · rwa [one_le_div (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]
  · rw [min_eq_right _]
    ·
      rw [norm_div, norm_norm, mul_comm, mul_div, div_eq_mul_inv, mul_comm, ← mul_assoc,
        inv_mul_cancel h0, one_mul, Real.norm_of_nonneg hc]
    · rwa [div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]
#align measure_theory.strongly_measurable.norm_approx_bounded_le MeasureTheory.StronglyMeasurable.norm_approxBounded_le

/- warning: strongly_measurable_bot_iff -> stronglyMeasurable_bot_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Nonempty.{succ u2} β] [_inst_4 : T2Space.{u2} β _inst_2], Iff (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 (Bot.bot.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toHasBot.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.completeLattice.{u1} α))) f) (Exists.{succ u2} β (fun (c : β) => Eq.{max (succ u1) (succ u2)} (α -> β) f (fun (_x : α) => c)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Nonempty.{succ u2} β] [_inst_4 : T2Space.{u2} β _inst_2], Iff (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 (Bot.bot.{u1} (MeasurableSpace.{u1} α) (CompleteLattice.toBot.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instCompleteLatticeMeasurableSpace.{u1} α))) f) (Exists.{succ u2} β (fun (c : β) => Eq.{max (succ u1) (succ u2)} (α -> β) f (fun (_x : α) => c)))
Case conversion may be inaccurate. Consider using '#align strongly_measurable_bot_iff stronglyMeasurable_bot_iffₓ'. -/
theorem stronglyMeasurable_bot_iff [Nonempty β] [T2Space β] :
    strongly_measurable[⊥] f ↔ ∃ c, f = fun _ => c :=
  by
  cases' isEmpty_or_nonempty α with hα hα
  · simp only [subsingleton.strongly_measurable', eq_iff_true_of_subsingleton, exists_const]
  refine' ⟨fun hf => _, fun hf_eq => _⟩
  · refine' ⟨f hα.some, _⟩
    let fs := hf.approx
    have h_fs_tendsto : ∀ x, tendsto (fun n => fs n x) at_top (𝓝 (f x)) := hf.tendsto_approx
    have : ∀ n, ∃ c, ∀ x, fs n x = c := fun n => simple_func.simple_func_bot (fs n)
    let cs n := (this n).some
    have h_cs_eq : ∀ n, ⇑(fs n) = fun x => cs n := fun n => funext (this n).choose_spec
    simp_rw [h_cs_eq] at h_fs_tendsto
    have h_tendsto : tendsto cs at_top (𝓝 (f hα.some)) := h_fs_tendsto hα.some
    ext1 x
    exact tendsto_nhds_unique (h_fs_tendsto x) h_tendsto
  · obtain ⟨c, rfl⟩ := hf_eq
    exact strongly_measurable_const
#align strongly_measurable_bot_iff stronglyMeasurable_bot_iff

end BasicPropertiesInAnyTopologicalSpace

/- warning: measure_theory.strongly_measurable.fin_strongly_measurable_of_set_sigma_finite -> MeasureTheory.StronglyMeasurable.finStronglyMeasurable_of_set_sigmaFinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Zero.{u2} β] {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (forall {t : Set.{u1} α}, (MeasurableSet.{u1} α m t) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)) -> (Eq.{succ u2} β (f x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3))))) -> (MeasureTheory.SigmaFinite.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ t)) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m f μ))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Zero.{u2} β] {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (forall {t : Set.{u1} α}, (MeasurableSet.{u1} α m t) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t)) -> (Eq.{succ u2} β (f x) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_3)))) -> (MeasureTheory.SigmaFinite.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ t)) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m f μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.fin_strongly_measurable_of_set_sigma_finite MeasureTheory.StronglyMeasurable.finStronglyMeasurable_of_set_sigmaFiniteₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ∉ » t) -/
theorem finStronglyMeasurable_of_set_sigmaFinite [TopologicalSpace β] [Zero β]
    {m : MeasurableSpace α} {μ : Measure α} (hf_meas : StronglyMeasurable f) {t : Set α}
    (ht : MeasurableSet t) (hft_zero : ∀ x ∈ tᶜ, f x = 0) (htμ : SigmaFinite (μ.restrict t)) :
    FinStronglyMeasurable f μ :=
  by
  haveI : sigma_finite (μ.restrict t) := htμ
  let S := spanning_sets (μ.restrict t)
  have hS_meas : ∀ n, MeasurableSet (S n) := measurable_spanning_sets (μ.restrict t)
  let f_approx := hf_meas.approx
  let fs n := simple_func.restrict (f_approx n) (S n ∩ t)
  have h_fs_t_compl : ∀ n, ∀ (x) (_ : x ∉ t), fs n x = 0 :=
    by
    intro n x hxt
    rw [simple_func.restrict_apply _ ((hS_meas n).inter ht)]
    refine' Set.indicator_of_not_mem _ _
    simp [hxt]
  refine' ⟨fs, _, fun x => _⟩
  · simp_rw [simple_func.support_eq]
    refine' fun n => (measure_bUnion_finset_le _ _).trans_lt _
    refine' ennreal.sum_lt_top_iff.mpr fun y hy => _
    rw [simple_func.restrict_preimage_singleton _ ((hS_meas n).inter ht)]
    swap
    · rw [Finset.mem_filter] at hy
      exact hy.2
    refine' (measure_mono (Set.inter_subset_left _ _)).trans_lt _
    have h_lt_top := measure_spanning_sets_lt_top (μ.restrict t) n
    rwa [measure.restrict_apply' ht] at h_lt_top
  · by_cases hxt : x ∈ t
    swap
    · rw [funext fun n => h_fs_t_compl n x hxt, hft_zero x hxt]
      exact tendsto_const_nhds
    have h : tendsto (fun n => (f_approx n) x) at_top (𝓝 (f x)) := hf_meas.tendsto_approx x
    obtain ⟨n₁, hn₁⟩ : ∃ n, ∀ m, n ≤ m → fs m x = f_approx m x :=
      by
      obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → x ∈ S m ∩ t :=
        by
        rsuffices ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → x ∈ S m
        · exact ⟨n, fun m hnm => Set.mem_inter (hn m hnm) hxt⟩
        rsuffices ⟨n, hn⟩ : ∃ n, x ∈ S n
        · exact ⟨n, fun m hnm => monotone_spanning_sets (μ.restrict t) hnm hn⟩
        rw [← Set.mem_iUnion, Union_spanning_sets (μ.restrict t)]
        trivial
      refine' ⟨n, fun m hnm => _⟩
      simp_rw [fs, simple_func.restrict_apply _ ((hS_meas m).inter ht),
        Set.indicator_of_mem (hn m hnm)]
    rw [tendsto_at_top'] at h⊢
    intro s hs
    obtain ⟨n₂, hn₂⟩ := h s hs
    refine' ⟨max n₁ n₂, fun m hm => _⟩
    rw [hn₁ m ((le_max_left _ _).trans hm.le)]
    exact hn₂ m ((le_max_right _ _).trans hm.le)
#align measure_theory.strongly_measurable.fin_strongly_measurable_of_set_sigma_finite MeasureTheory.StronglyMeasurable.finStronglyMeasurable_of_set_sigmaFinite

#print MeasureTheory.StronglyMeasurable.finStronglyMeasurable /-
/-- If the measure is sigma-finite, all strongly measurable functions are
  `fin_strongly_measurable`. -/
protected theorem finStronglyMeasurable [TopologicalSpace β] [Zero β] {m0 : MeasurableSpace α}
    (hf : StronglyMeasurable f) (μ : Measure α) [SigmaFinite μ] : FinStronglyMeasurable f μ :=
  hf.finStronglyMeasurable_of_set_sigmaFinite MeasurableSet.univ (by simp)
    (by rwa [measure.restrict_univ])
#align measure_theory.strongly_measurable.fin_strongly_measurable MeasureTheory.StronglyMeasurable.finStronglyMeasurable
-/

/- warning: measure_theory.strongly_measurable.measurable -> MeasureTheory.StronglyMeasurable.measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_4 : MeasurableSpace.{u2} β] [_inst_5 : BorelSpace.{u2} β _inst_2 _inst_4], (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (Measurable.{u1, u2} α β m _inst_4 f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.PseudoMetrizableSpace.{u1} β _inst_2] [_inst_4 : MeasurableSpace.{u1} β] [_inst_5 : BorelSpace.{u1} β _inst_2 _inst_4], (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) -> (Measurable.{u2, u1} α β m _inst_4 f)
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.measurable MeasureTheory.StronglyMeasurable.measurableₓ'. -/
/-- A strongly measurable function is measurable. -/
protected theorem measurable {m : MeasurableSpace α} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] (hf : StronglyMeasurable f) : Measurable f :=
  measurable_of_tendsto_metrizable (fun n => (hf.approx n).Measurable)
    (tendsto_pi_nhds.mpr hf.tendsto_approx)
#align measure_theory.strongly_measurable.measurable MeasureTheory.StronglyMeasurable.measurable

/- warning: measure_theory.strongly_measurable.ae_measurable -> MeasureTheory.StronglyMeasurable.aemeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_4 : MeasurableSpace.{u2} β] [_inst_5 : BorelSpace.{u2} β _inst_2 _inst_4] {μ : MeasureTheory.Measure.{u1} α m}, (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (AEMeasurable.{u1, u2} α β _inst_4 m f μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.PseudoMetrizableSpace.{u1} β _inst_2] [_inst_4 : MeasurableSpace.{u1} β] [_inst_5 : BorelSpace.{u1} β _inst_2 _inst_4] {μ : MeasureTheory.Measure.{u2} α m}, (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) -> (AEMeasurable.{u2, u1} α β _inst_4 m f μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.ae_measurable MeasureTheory.StronglyMeasurable.aemeasurableₓ'. -/
/-- A strongly measurable function is almost everywhere measurable. -/
protected theorem aemeasurable {m : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] {μ : Measure α}
    (hf : StronglyMeasurable f) : AEMeasurable f μ :=
  hf.Measurable.AEMeasurable
#align measure_theory.strongly_measurable.ae_measurable MeasureTheory.StronglyMeasurable.aemeasurable

/- warning: continuous.comp_strongly_measurable -> Continuous.comp_stronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : β -> γ} {f : α -> β}, (Continuous.{u2, u3} β γ _inst_2 _inst_3 g) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u1, u3} α γ _inst_3 m (fun (x : α) => g (f x)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {m : MeasurableSpace.{u3} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {g : β -> γ} {f : α -> β}, (Continuous.{u2, u1} β γ _inst_2 _inst_3 g) -> (MeasureTheory.StronglyMeasurable.{u3, u2} α β _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u3, u1} α γ _inst_3 m (fun (x : α) => g (f x)))
Case conversion may be inaccurate. Consider using '#align continuous.comp_strongly_measurable Continuous.comp_stronglyMeasurableₓ'. -/
theorem Continuous.comp_stronglyMeasurable {m : MeasurableSpace α} [TopologicalSpace β]
    [TopologicalSpace γ] {g : β → γ} {f : α → β} (hg : Continuous g) (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => g (f x) :=
  ⟨fun n => SimpleFunc.map g (hf.approx n), fun x => (hg.Tendsto _).comp (hf.tendsto_approx x)⟩
#align continuous.comp_strongly_measurable Continuous.comp_stronglyMeasurable

/- warning: measure_theory.strongly_measurable.measurable_set_mul_support -> MeasureTheory.StronglyMeasurable.measurableSet_mulSupport is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {m : MeasurableSpace.{u1} α} [_inst_2 : One.{u2} β] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : TopologicalSpace.MetrizableSpace.{u2} β _inst_3], (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_3 m f) -> (MeasurableSet.{u1} α m (Function.mulSupport.{u1, u2} α β _inst_2 f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {m : MeasurableSpace.{u2} α} [_inst_2 : One.{u1} β] [_inst_3 : TopologicalSpace.{u1} β] [_inst_4 : TopologicalSpace.MetrizableSpace.{u1} β _inst_3], (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_3 m f) -> (MeasurableSet.{u2} α m (Function.mulSupport.{u2, u1} α β _inst_2 f))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.measurable_set_mul_support MeasureTheory.StronglyMeasurable.measurableSet_mulSupportₓ'. -/
@[to_additive]
theorem measurableSet_mulSupport {m : MeasurableSpace α} [One β] [TopologicalSpace β]
    [MetrizableSpace β] (hf : StronglyMeasurable f) : MeasurableSet (mulSupport f) :=
  by
  borelize β
  exact measurableSet_mulSupport hf.measurable
#align measure_theory.strongly_measurable.measurable_set_mul_support MeasureTheory.StronglyMeasurable.measurableSet_mulSupport
#align measure_theory.strongly_measurable.measurable_set_support MeasureTheory.StronglyMeasurable.measurableSet_support

/- warning: measure_theory.strongly_measurable.mono -> MeasureTheory.StronglyMeasurable.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {m : MeasurableSpace.{u1} α} {m' : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β], (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m' f) -> (LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) m' m) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {m : MeasurableSpace.{u2} α} {m' : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β], (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m' f) -> (LE.le.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instLEMeasurableSpace.{u2} α) m' m) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f)
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.mono MeasureTheory.StronglyMeasurable.monoₓ'. -/
protected theorem mono {m m' : MeasurableSpace α} [TopologicalSpace β]
    (hf : strongly_measurable[m'] f) (h_mono : m' ≤ m) : strongly_measurable[m] f :=
  by
  let f_approx : ℕ → @simple_func α m β := fun n =>
    { toFun := hf.approx n
      measurableSet_fiber' := fun x => h_mono _ (simple_func.measurable_set_fiber' _ x)
      finite_range' := simple_func.finite_range (hf.approx n) }
  exact ⟨f_approx, hf.tendsto_approx⟩
#align measure_theory.strongly_measurable.mono MeasureTheory.StronglyMeasurable.mono

/- warning: measure_theory.strongly_measurable.prod_mk -> MeasureTheory.StronglyMeasurable.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β} {g : α -> γ}, (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u1, u3} α γ _inst_3 m g) -> (MeasureTheory.StronglyMeasurable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) m (fun (x : α) => Prod.mk.{u2, u3} β γ (f x) (g x)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {m : MeasurableSpace.{u3} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> β} {g : α -> γ}, (MeasureTheory.StronglyMeasurable.{u3, u2} α β _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u3, u1} α γ _inst_3 m g) -> (MeasureTheory.StronglyMeasurable.{u3, max u1 u2} α (Prod.{u2, u1} β γ) (instTopologicalSpaceProd.{u2, u1} β γ _inst_2 _inst_3) m (fun (x : α) => Prod.mk.{u2, u1} β γ (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.prod_mk MeasureTheory.StronglyMeasurable.prod_mkₓ'. -/
protected theorem prod_mk {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {f : α → β} {g : α → γ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => (f x, g x) :=
  by
  refine' ⟨fun n => simple_func.pair (hf.approx n) (hg.approx n), fun x => _⟩
  rw [nhds_prod_eq]
  exact tendsto.prod_mk (hf.tendsto_approx x) (hg.tendsto_approx x)
#align measure_theory.strongly_measurable.prod_mk MeasureTheory.StronglyMeasurable.prod_mk

/- warning: measure_theory.strongly_measurable.comp_measurable -> MeasureTheory.StronglyMeasurable.comp_measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {m : MeasurableSpace.{u1} α} {m' : MeasurableSpace.{u3} γ} {f : α -> β} {g : γ -> α}, (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (Measurable.{u3, u1} γ α m' m g) -> (MeasureTheory.StronglyMeasurable.{u3, u2} γ β _inst_2 m' (Function.comp.{succ u3, succ u1, succ u2} γ α β f g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} β] {m : MeasurableSpace.{u2} α} {m' : MeasurableSpace.{u1} γ} {f : α -> β} {g : γ -> α}, (MeasureTheory.StronglyMeasurable.{u2, u3} α β _inst_2 m f) -> (Measurable.{u1, u2} γ α m' m g) -> (MeasureTheory.StronglyMeasurable.{u1, u3} γ β _inst_2 m' (Function.comp.{succ u1, succ u2, succ u3} γ α β f g))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.comp_measurable MeasureTheory.StronglyMeasurable.comp_measurableₓ'. -/
theorem comp_measurable [TopologicalSpace β] {m : MeasurableSpace α} {m' : MeasurableSpace γ}
    {f : α → β} {g : γ → α} (hf : StronglyMeasurable f) (hg : Measurable g) :
    StronglyMeasurable (f ∘ g) :=
  ⟨fun n => SimpleFunc.comp (hf.approx n) g hg, fun x => hf.tendsto_approx (g x)⟩
#align measure_theory.strongly_measurable.comp_measurable MeasureTheory.StronglyMeasurable.comp_measurable

/- warning: measure_theory.strongly_measurable.of_uncurry_left -> MeasureTheory.StronglyMeasurable.of_uncurry_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {mα : MeasurableSpace.{u1} α} {mγ : MeasurableSpace.{u3} γ} {f : α -> γ -> β}, (MeasureTheory.StronglyMeasurable.{max u1 u3, u2} (Prod.{u1, u3} α γ) β _inst_2 (Prod.instMeasurableSpace.{u1, u3} α γ mα mγ) (Function.uncurry.{u1, u3, u2} α γ β f)) -> (forall {x : α}, MeasureTheory.StronglyMeasurable.{u3, u2} γ β _inst_2 mγ (f x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} β] {mα : MeasurableSpace.{u2} α} {mγ : MeasurableSpace.{u1} γ} {f : α -> γ -> β}, (MeasureTheory.StronglyMeasurable.{max u1 u2, u3} (Prod.{u2, u1} α γ) β _inst_2 (Prod.instMeasurableSpace.{u2, u1} α γ mα mγ) (Function.uncurry.{u2, u1, u3} α γ β f)) -> (forall {x : α}, MeasureTheory.StronglyMeasurable.{u1, u3} γ β _inst_2 mγ (f x))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.of_uncurry_left MeasureTheory.StronglyMeasurable.of_uncurry_leftₓ'. -/
theorem of_uncurry_left [TopologicalSpace β] {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
    {f : α → γ → β} (hf : StronglyMeasurable (uncurry f)) {x : α} : StronglyMeasurable (f x) :=
  hf.comp_measurable measurable_prod_mk_left
#align measure_theory.strongly_measurable.of_uncurry_left MeasureTheory.StronglyMeasurable.of_uncurry_left

/- warning: measure_theory.strongly_measurable.of_uncurry_right -> MeasureTheory.StronglyMeasurable.of_uncurry_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] {mα : MeasurableSpace.{u1} α} {mγ : MeasurableSpace.{u3} γ} {f : α -> γ -> β}, (MeasureTheory.StronglyMeasurable.{max u1 u3, u2} (Prod.{u1, u3} α γ) β _inst_2 (Prod.instMeasurableSpace.{u1, u3} α γ mα mγ) (Function.uncurry.{u1, u3, u2} α γ β f)) -> (forall {y : γ}, MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 mα (fun (x : α) => f x y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_2 : TopologicalSpace.{u3} β] {mα : MeasurableSpace.{u2} α} {mγ : MeasurableSpace.{u1} γ} {f : α -> γ -> β}, (MeasureTheory.StronglyMeasurable.{max u1 u2, u3} (Prod.{u2, u1} α γ) β _inst_2 (Prod.instMeasurableSpace.{u2, u1} α γ mα mγ) (Function.uncurry.{u2, u1, u3} α γ β f)) -> (forall {y : γ}, MeasureTheory.StronglyMeasurable.{u2, u3} α β _inst_2 mα (fun (x : α) => f x y))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.of_uncurry_right MeasureTheory.StronglyMeasurable.of_uncurry_rightₓ'. -/
theorem of_uncurry_right [TopologicalSpace β] {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
    {f : α → γ → β} (hf : StronglyMeasurable (uncurry f)) {y : γ} :
    StronglyMeasurable fun x => f x y :=
  hf.comp_measurable measurable_prod_mk_right
#align measure_theory.strongly_measurable.of_uncurry_right MeasureTheory.StronglyMeasurable.of_uncurry_right

section Arithmetic

variable {mα : MeasurableSpace α} [TopologicalSpace β]

include mα

#print MeasureTheory.StronglyMeasurable.mul /-
@[to_additive]
protected theorem mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f * g) :=
  ⟨fun n => hf.approx n * hg.approx n, fun x => (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩
#align measure_theory.strongly_measurable.mul MeasureTheory.StronglyMeasurable.mul
#align measure_theory.strongly_measurable.add MeasureTheory.StronglyMeasurable.add
-/

#print MeasureTheory.StronglyMeasurable.mul_const /-
@[to_additive]
theorem mul_const [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => f x * c :=
  hf.mul stronglyMeasurable_const
#align measure_theory.strongly_measurable.mul_const MeasureTheory.StronglyMeasurable.mul_const
#align measure_theory.strongly_measurable.add_const MeasureTheory.StronglyMeasurable.add_const
-/

#print MeasureTheory.StronglyMeasurable.const_mul /-
@[to_additive]
theorem const_mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => c * f x :=
  stronglyMeasurable_const.mul hf
#align measure_theory.strongly_measurable.const_mul MeasureTheory.StronglyMeasurable.const_mul
#align measure_theory.strongly_measurable.const_add MeasureTheory.StronglyMeasurable.const_add
-/

/- warning: measure_theory.strongly_measurable.inv -> MeasureTheory.StronglyMeasurable.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {mα : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Group.{u2} β] [_inst_4 : TopologicalGroup.{u2} β _inst_2 _inst_3], (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 mα f) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 mα (Inv.inv.{max u1 u2} (α -> β) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => DivInvMonoid.toHasInv.{u2} β (Group.toDivInvMonoid.{u2} β _inst_3))) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {mα : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Group.{u2} β] [_inst_4 : TopologicalGroup.{u2} β _inst_2 _inst_3], (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 mα f) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 mα (Inv.inv.{max u2 u1} (α -> β) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => InvOneClass.toInv.{u2} β (DivInvOneMonoid.toInvOneClass.{u2} β (DivisionMonoid.toDivInvOneMonoid.{u2} β (Group.toDivisionMonoid.{u2} β _inst_3))))) f))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.inv MeasureTheory.StronglyMeasurable.invₓ'. -/
@[to_additive]
protected theorem inv [Group β] [TopologicalGroup β] (hf : StronglyMeasurable f) :
    StronglyMeasurable f⁻¹ :=
  ⟨fun n => (hf.approx n)⁻¹, fun x => (hf.tendsto_approx x).inv⟩
#align measure_theory.strongly_measurable.inv MeasureTheory.StronglyMeasurable.inv
#align measure_theory.strongly_measurable.neg MeasureTheory.StronglyMeasurable.neg

#print MeasureTheory.StronglyMeasurable.div /-
@[to_additive]
protected theorem div [Div β] [ContinuousDiv β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f / g) :=
  ⟨fun n => hf.approx n / hg.approx n, fun x => (hf.tendsto_approx x).div' (hg.tendsto_approx x)⟩
#align measure_theory.strongly_measurable.div MeasureTheory.StronglyMeasurable.div
#align measure_theory.strongly_measurable.sub MeasureTheory.StronglyMeasurable.sub
-/

#print MeasureTheory.StronglyMeasurable.smul /-
@[to_additive]
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    {g : α → β} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => f x • g x :=
  continuous_smul.comp_stronglyMeasurable (hf.prod_mk hg)
#align measure_theory.strongly_measurable.smul MeasureTheory.StronglyMeasurable.smul
#align measure_theory.strongly_measurable.vadd MeasureTheory.StronglyMeasurable.vadd
-/

#print MeasureTheory.StronglyMeasurable.const_smul /-
protected theorem const_smul {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (hf : StronglyMeasurable f)
    (c : 𝕜) : StronglyMeasurable (c • f) :=
  ⟨fun n => c • hf.approx n, fun x => (hf.tendsto_approx x).const_smul c⟩
#align measure_theory.strongly_measurable.const_smul MeasureTheory.StronglyMeasurable.const_smul
-/

#print MeasureTheory.StronglyMeasurable.const_smul' /-
protected theorem const_smul' {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (hf : StronglyMeasurable f)
    (c : 𝕜) : StronglyMeasurable fun x => c • f x :=
  hf.const_smul c
#align measure_theory.strongly_measurable.const_smul' MeasureTheory.StronglyMeasurable.const_smul'
-/

#print MeasureTheory.StronglyMeasurable.smul_const /-
@[to_additive]
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    (hf : StronglyMeasurable f) (c : β) : StronglyMeasurable fun x => f x • c :=
  continuous_smul.comp_stronglyMeasurable (hf.prod_mk stronglyMeasurable_const)
#align measure_theory.strongly_measurable.smul_const MeasureTheory.StronglyMeasurable.smul_const
#align measure_theory.strongly_measurable.vadd_const MeasureTheory.StronglyMeasurable.vadd_const
-/

end Arithmetic

section MulAction

variable {M G G₀ : Type _}

variable [TopologicalSpace β]

variable [Monoid M] [MulAction M β] [ContinuousConstSMul M β]

variable [Group G] [MulAction G β] [ContinuousConstSMul G β]

variable [GroupWithZero G₀] [MulAction G₀ β] [ContinuousConstSMul G₀ β]

/- warning: strongly_measurable_const_smul_iff -> stronglyMeasurable_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {G : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] [_inst_6 : Group.{u3} G] [_inst_7 : MulAction.{u3, u2} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_6))] [_inst_8 : ContinuousConstSMul.{u3, u2} G β _inst_2 (MulAction.toHasSmul.{u3, u2} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_6)) _inst_7)] {m : MeasurableSpace.{u1} α} (c : G), Iff (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m (fun (x : α) => SMul.smul.{u3, u2} G β (MulAction.toHasSmul.{u3, u2} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_6)) _inst_7) c (f x))) (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {f : α -> β} [G : TopologicalSpace.{u2} β] {_inst_2 : Type.{u1}} [_inst_6 : Group.{u1} _inst_2] [_inst_7 : MulAction.{u1, u2} _inst_2 β (DivInvMonoid.toMonoid.{u1} _inst_2 (Group.toDivInvMonoid.{u1} _inst_2 _inst_6))] [_inst_8 : ContinuousConstSMul.{u1, u2} _inst_2 β G (MulAction.toSMul.{u1, u2} _inst_2 β (DivInvMonoid.toMonoid.{u1} _inst_2 (Group.toDivInvMonoid.{u1} _inst_2 _inst_6)) _inst_7)] {m : MeasurableSpace.{u3} α} (c : _inst_2), Iff (MeasureTheory.StronglyMeasurable.{u3, u2} α β G m (fun (x : α) => HSMul.hSMul.{u1, u2, u2} _inst_2 β β (instHSMul.{u1, u2} _inst_2 β (MulAction.toSMul.{u1, u2} _inst_2 β (DivInvMonoid.toMonoid.{u1} _inst_2 (Group.toDivInvMonoid.{u1} _inst_2 _inst_6)) _inst_7)) c (f x))) (MeasureTheory.StronglyMeasurable.{u3, u2} α β G m f)
Case conversion may be inaccurate. Consider using '#align strongly_measurable_const_smul_iff stronglyMeasurable_const_smul_iffₓ'. -/
theorem stronglyMeasurable_const_smul_iff {m : MeasurableSpace α} (c : G) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align strongly_measurable_const_smul_iff stronglyMeasurable_const_smul_iff

theorem IsUnit.stronglyMeasurable_const_smul_iff {m : MeasurableSpace α} {c : M} (hc : IsUnit c) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ stronglyMeasurable_const_smul_iff u
#align is_unit.strongly_measurable_const_smul_iff IsUnit.stronglyMeasurable_const_smul_iff

/- warning: strongly_measurable_const_smul_iff₀ -> stronglyMeasurable_const_smul_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {G₀ : Type.{u3}} [_inst_2 : TopologicalSpace.{u2} β] [_inst_9 : GroupWithZero.{u3} G₀] [_inst_10 : MulAction.{u3, u2} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_9))] [_inst_11 : ContinuousConstSMul.{u3, u2} G₀ β _inst_2 (MulAction.toHasSmul.{u3, u2} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_9)) _inst_10)] {m : MeasurableSpace.{u1} α} {c : G₀}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_9)))))))) -> (Iff (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m (fun (x : α) => SMul.smul.{u3, u2} G₀ β (MulAction.toHasSmul.{u3, u2} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_9)) _inst_10) c (f x))) (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {f : α -> β} [G₀ : TopologicalSpace.{u1} β] {_inst_2 : Type.{u2}} [_inst_9 : GroupWithZero.{u2} _inst_2] [_inst_10 : MulAction.{u2, u1} _inst_2 β (MonoidWithZero.toMonoid.{u2} _inst_2 (GroupWithZero.toMonoidWithZero.{u2} _inst_2 _inst_9))] [_inst_11 : ContinuousConstSMul.{u2, u1} _inst_2 β G₀ (MulAction.toSMul.{u2, u1} _inst_2 β (MonoidWithZero.toMonoid.{u2} _inst_2 (GroupWithZero.toMonoidWithZero.{u2} _inst_2 _inst_9)) _inst_10)] {m : MeasurableSpace.{u3} α} {c : _inst_2}, (Ne.{succ u2} _inst_2 c (OfNat.ofNat.{u2} _inst_2 0 (Zero.toOfNat0.{u2} _inst_2 (MonoidWithZero.toZero.{u2} _inst_2 (GroupWithZero.toMonoidWithZero.{u2} _inst_2 _inst_9))))) -> (Iff (MeasureTheory.StronglyMeasurable.{u3, u1} α β G₀ m (fun (x : α) => HSMul.hSMul.{u2, u1, u1} _inst_2 β β (instHSMul.{u2, u1} _inst_2 β (MulAction.toSMul.{u2, u1} _inst_2 β (MonoidWithZero.toMonoid.{u2} _inst_2 (GroupWithZero.toMonoidWithZero.{u2} _inst_2 _inst_9)) _inst_10)) c (f x))) (MeasureTheory.StronglyMeasurable.{u3, u1} α β G₀ m f))
Case conversion may be inaccurate. Consider using '#align strongly_measurable_const_smul_iff₀ stronglyMeasurable_const_smul_iff₀ₓ'. -/
theorem stronglyMeasurable_const_smul_iff₀ {m : MeasurableSpace α} {c : G₀} (hc : c ≠ 0) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  (IsUnit.mk0 _ hc).stronglyMeasurable_const_smul_iff
#align strongly_measurable_const_smul_iff₀ stronglyMeasurable_const_smul_iff₀

end MulAction

section Order

variable [MeasurableSpace α] [TopologicalSpace β]

open Filter

open Filter

#print MeasureTheory.StronglyMeasurable.sup /-
protected theorem sup [Sup β] [ContinuousSup β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f ⊔ g) :=
  ⟨fun n => hf.approx n ⊔ hg.approx n, fun x =>
    (hf.tendsto_approx x).sup_right_nhds (hg.tendsto_approx x)⟩
#align measure_theory.strongly_measurable.sup MeasureTheory.StronglyMeasurable.sup
-/

#print MeasureTheory.StronglyMeasurable.inf /-
protected theorem inf [Inf β] [ContinuousInf β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f ⊓ g) :=
  ⟨fun n => hf.approx n ⊓ hg.approx n, fun x =>
    (hf.tendsto_approx x).inf_right_nhds (hg.tendsto_approx x)⟩
#align measure_theory.strongly_measurable.inf MeasureTheory.StronglyMeasurable.inf
-/

end Order

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M : Type _} [Monoid M] [TopologicalSpace M] [ContinuousMul M] {m : MeasurableSpace α}

include m

/- warning: list.strongly_measurable_prod' -> List.stronglyMeasurable_prod' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_2 : Monoid.{u2} M] [_inst_3 : TopologicalSpace.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_3 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))] {m : MeasurableSpace.{u1} α} (l : List.{max u1 u2} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u1 u2, max u1 u2} (α -> M) (List.{max u1 u2} (α -> M)) (List.hasMem.{max u1 u2} (α -> M)) f l) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α M _inst_3 m f)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α M _inst_3 m (List.prod.{max u1 u2} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))) l))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_2 : Monoid.{u1} M] [_inst_3 : TopologicalSpace.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_3 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2))] {m : MeasurableSpace.{u2} α} (l : List.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (List.{max u2 u1} (α -> M)) (List.instMembershipList.{max u2 u1} (α -> M)) f l) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α M _inst_3 m f)) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α M _inst_3 m (List.prod.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2))) (Pi.instOne.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => Monoid.toOne.{u1} M _inst_2)) l))
Case conversion may be inaccurate. Consider using '#align list.strongly_measurable_prod' List.stronglyMeasurable_prod'ₓ'. -/
@[to_additive]
theorem List.stronglyMeasurable_prod' (l : List (α → M)) (hl : ∀ f ∈ l, StronglyMeasurable f) :
    StronglyMeasurable l.Prod := by
  induction' l with f l ihl; · exact strongly_measurable_one
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.strongly_measurable_prod' List.stronglyMeasurable_prod'
#align list.strongly_measurable_sum' List.stronglyMeasurable_sum'

/- warning: list.strongly_measurable_prod -> List.stronglyMeasurable_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_2 : Monoid.{u2} M] [_inst_3 : TopologicalSpace.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_3 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2))] {m : MeasurableSpace.{u1} α} (l : List.{max u1 u2} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u1 u2, max u1 u2} (α -> M) (List.{max u1 u2} (α -> M)) (List.hasMem.{max u1 u2} (α -> M)) f l) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α M _inst_3 m f)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α M _inst_3 m (fun (x : α) => List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_2)) (List.map.{max u1 u2, u2} (α -> M) M (fun (f : α -> M) => f x) l)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_2 : Monoid.{u1} M] [_inst_3 : TopologicalSpace.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_3 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2))] {m : MeasurableSpace.{u2} α} (l : List.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (List.{max u2 u1} (α -> M)) (List.instMembershipList.{max u2 u1} (α -> M)) f l) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α M _inst_3 m f)) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α M _inst_3 m (fun (x : α) => List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_2)) (Monoid.toOne.{u1} M _inst_2) (List.map.{max u2 u1, u1} (α -> M) M (fun (f : α -> M) => f x) l)))
Case conversion may be inaccurate. Consider using '#align list.strongly_measurable_prod List.stronglyMeasurable_prodₓ'. -/
@[to_additive]
theorem List.stronglyMeasurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, StronglyMeasurable f) :
    StronglyMeasurable fun x => (l.map fun f : α → M => f x).Prod := by
  simpa only [← Pi.list_prod_apply] using l.strongly_measurable_prod' hl
#align list.strongly_measurable_prod List.stronglyMeasurable_prod
#align list.strongly_measurable_sum List.stronglyMeasurable_sum

end Monoid

section CommMonoid

variable {M : Type _} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M] {m : MeasurableSpace α}

include m

/- warning: multiset.strongly_measurable_prod' -> Multiset.stronglyMeasurable_prod' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_2 : CommMonoid.{u2} M] [_inst_3 : TopologicalSpace.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_3 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))] {m : MeasurableSpace.{u1} α} (l : Multiset.{max u1 u2} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u1 u2, max u1 u2} (α -> M) (Multiset.{max u1 u2} (α -> M)) (Multiset.hasMem.{max u1 u2} (α -> M)) f l) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α M _inst_3 m f)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α M _inst_3 m (Multiset.prod.{max u1 u2} (α -> M) (Pi.commMonoid.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2)) l))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_2 : CommMonoid.{u1} M] [_inst_3 : TopologicalSpace.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_3 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))] {m : MeasurableSpace.{u2} α} (l : Multiset.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (Multiset.{max u2 u1} (α -> M)) (Multiset.instMembershipMultiset.{max u2 u1} (α -> M)) f l) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α M _inst_3 m f)) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α M _inst_3 m (Multiset.prod.{max u2 u1} (α -> M) (Pi.commMonoid.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2)) l))
Case conversion may be inaccurate. Consider using '#align multiset.strongly_measurable_prod' Multiset.stronglyMeasurable_prod'ₓ'. -/
@[to_additive]
theorem Multiset.stronglyMeasurable_prod' (l : Multiset (α → M))
    (hl : ∀ f ∈ l, StronglyMeasurable f) : StronglyMeasurable l.Prod :=
  by
  rcases l with ⟨l⟩
  simpa using l.strongly_measurable_prod' (by simpa using hl)
#align multiset.strongly_measurable_prod' Multiset.stronglyMeasurable_prod'
#align multiset.strongly_measurable_sum' Multiset.stronglyMeasurable_sum'

/- warning: multiset.strongly_measurable_prod -> Multiset.stronglyMeasurable_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_2 : CommMonoid.{u2} M] [_inst_3 : TopologicalSpace.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_3 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))] {m : MeasurableSpace.{u1} α} (s : Multiset.{max u1 u2} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u1 u2, max u1 u2} (α -> M) (Multiset.{max u1 u2} (α -> M)) (Multiset.hasMem.{max u1 u2} (α -> M)) f s) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α M _inst_3 m f)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α M _inst_3 m (fun (x : α) => Multiset.prod.{u2} M _inst_2 (Multiset.map.{max u1 u2, u2} (α -> M) M (fun (f : α -> M) => f x) s)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_2 : CommMonoid.{u1} M] [_inst_3 : TopologicalSpace.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_3 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))] {m : MeasurableSpace.{u2} α} (s : Multiset.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (Multiset.{max u2 u1} (α -> M)) (Multiset.instMembershipMultiset.{max u2 u1} (α -> M)) f s) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α M _inst_3 m f)) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α M _inst_3 m (fun (x : α) => Multiset.prod.{u1} M _inst_2 (Multiset.map.{max u2 u1, u1} (α -> M) M (fun (f : α -> M) => f x) s)))
Case conversion may be inaccurate. Consider using '#align multiset.strongly_measurable_prod Multiset.stronglyMeasurable_prodₓ'. -/
@[to_additive]
theorem Multiset.stronglyMeasurable_prod (s : Multiset (α → M))
    (hs : ∀ f ∈ s, StronglyMeasurable f) :
    StronglyMeasurable fun x => (s.map fun f : α → M => f x).Prod := by
  simpa only [← Pi.multiset_prod_apply] using s.strongly_measurable_prod' hs
#align multiset.strongly_measurable_prod Multiset.stronglyMeasurable_prod
#align multiset.strongly_measurable_sum Multiset.stronglyMeasurable_sum

/- warning: finset.strongly_measurable_prod' -> Finset.stronglyMeasurable_prod' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_2 : CommMonoid.{u2} M] [_inst_3 : TopologicalSpace.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_3 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))] {m : MeasurableSpace.{u1} α} {ι : Type.{u3}} {f : ι -> α -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α M _inst_3 m (f i))) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α M _inst_3 m (Finset.prod.{max u1 u2, u3} (α -> M) ι (Pi.commMonoid.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2)) s (fun (i : ι) => f i)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_2 : CommMonoid.{u1} M] [_inst_3 : TopologicalSpace.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_3 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))] {m : MeasurableSpace.{u2} α} {ι : Type.{u3}} {f : ι -> α -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α M _inst_3 m (f i))) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α M _inst_3 m (Finset.prod.{max u1 u2, u3} (α -> M) ι (Pi.commMonoid.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2)) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.strongly_measurable_prod' Finset.stronglyMeasurable_prod'ₓ'. -/
@[to_additive]
theorem Finset.stronglyMeasurable_prod' {ι : Type _} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) : StronglyMeasurable (∏ i in s, f i) :=
  Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) (@stronglyMeasurable_one α M _ _ _) hf
#align finset.strongly_measurable_prod' Finset.stronglyMeasurable_prod'
#align finset.strongly_measurable_sum' Finset.stronglyMeasurable_sum'

/- warning: finset.strongly_measurable_prod -> Finset.stronglyMeasurable_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_2 : CommMonoid.{u2} M] [_inst_3 : TopologicalSpace.{u2} M] [_inst_4 : ContinuousMul.{u2} M _inst_3 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))] {m : MeasurableSpace.{u1} α} {ι : Type.{u3}} {f : ι -> α -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α M _inst_3 m (f i))) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α M _inst_3 m (fun (a : α) => Finset.prod.{u2, u3} M ι _inst_2 s (fun (i : ι) => f i a)))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_2 : CommMonoid.{u1} M] [_inst_3 : TopologicalSpace.{u1} M] [_inst_4 : ContinuousMul.{u1} M _inst_3 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))] {m : MeasurableSpace.{u2} α} {ι : Type.{u3}} {f : ι -> α -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α M _inst_3 m (f i))) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α M _inst_3 m (fun (a : α) => Finset.prod.{u1, u3} M ι _inst_2 s (fun (i : ι) => f i a)))
Case conversion may be inaccurate. Consider using '#align finset.strongly_measurable_prod Finset.stronglyMeasurable_prodₓ'. -/
@[to_additive]
theorem Finset.stronglyMeasurable_prod {ι : Type _} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, StronglyMeasurable (f i)) : StronglyMeasurable fun a => ∏ i in s, f i a := by
  simpa only [← Finset.prod_apply] using s.strongly_measurable_prod' hf
#align finset.strongly_measurable_prod Finset.stronglyMeasurable_prod
#align finset.strongly_measurable_sum Finset.stronglyMeasurable_sum

end CommMonoid

/- warning: measure_theory.strongly_measurable.is_separable_range -> MeasureTheory.StronglyMeasurable.isSeparable_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β], (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (TopologicalSpace.IsSeparable.{u2} β _inst_2 (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β], (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) -> (TopologicalSpace.IsSeparable.{u1} β _inst_2 (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.is_separable_range MeasureTheory.StronglyMeasurable.isSeparable_rangeₓ'. -/
/-- The range of a strongly measurable function is separable. -/
theorem isSeparable_range {m : MeasurableSpace α} [TopologicalSpace β] (hf : StronglyMeasurable f) :
    TopologicalSpace.IsSeparable (range f) :=
  by
  have : IsSeparable (closure (⋃ n, range (hf.approx n))) :=
    (is_separable_Union fun n => (simple_func.finite_range (hf.approx n)).IsSeparable).closure
  apply this.mono
  rintro _ ⟨x, rfl⟩
  apply mem_closure_of_tendsto (hf.tendsto_approx x)
  apply eventually_of_forall fun n => _
  apply mem_Union_of_mem n
  exact mem_range_self _
#align measure_theory.strongly_measurable.is_separable_range MeasureTheory.StronglyMeasurable.isSeparable_range

/- warning: measure_theory.strongly_measurable.separable_space_range_union_singleton -> MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2], (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (forall {b : β}, TopologicalSpace.SeparableSpace.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.range.{u2, succ u1} β α f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b))) (Subtype.topologicalSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (Set.range.{u2, succ u1} β α f) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b))) _inst_2))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.PseudoMetrizableSpace.{u1} β _inst_2], (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) -> (forall {b : β}, TopologicalSpace.SeparableSpace.{u1} (Set.Elem.{u1} β (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (Set.range.{u1, succ u2} β α f) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b))) (instTopologicalSpaceSubtype.{u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) (Set.range.{u1, succ u2} β α f) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b))) _inst_2))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.separable_space_range_union_singleton MeasureTheory.StronglyMeasurable.separableSpace_range_union_singletonₓ'. -/
theorem separableSpace_range_union_singleton {m : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b : β} :
    SeparableSpace (range f ∪ {b} : Set β) :=
  letI := pseudo_metrizable_space_pseudo_metric β
  (hf.is_separable_range.union (finite_singleton _).IsSeparable).SeparableSpace
#align measure_theory.strongly_measurable.separable_space_range_union_singleton MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton

section SecondCountableStronglyMeasurable

variable {mα : MeasurableSpace α} [MeasurableSpace β]

include mα

#print Measurable.stronglyMeasurable /-
/-- In a space with second countable topology, measurable implies strongly measurable. -/
theorem Measurable.stronglyMeasurable [TopologicalSpace β] [PseudoMetrizableSpace β]
    [SecondCountableTopology β] [OpensMeasurableSpace β] (hf : Measurable f) :
    StronglyMeasurable f :=
  by
  letI := pseudo_metrizable_space_pseudo_metric β
  rcases isEmpty_or_nonempty β with ⟨⟩ <;> skip
  · exact subsingleton.strongly_measurable f
  · inhabit β
    exact
      ⟨simple_func.approx_on f hf Set.univ default (Set.mem_univ _), fun x =>
        simple_func.tendsto_approx_on hf (Set.mem_univ _) (by simp)⟩
#align measurable.strongly_measurable Measurable.stronglyMeasurable
-/

#print stronglyMeasurable_iff_measurable /-
/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
theorem stronglyMeasurable_iff_measurable [TopologicalSpace β] [MetrizableSpace β] [BorelSpace β]
    [SecondCountableTopology β] : StronglyMeasurable f ↔ Measurable f :=
  ⟨fun h => h.Measurable, fun h => Measurable.stronglyMeasurable h⟩
#align strongly_measurable_iff_measurable stronglyMeasurable_iff_measurable
-/

#print stronglyMeasurable_id /-
theorem stronglyMeasurable_id [TopologicalSpace α] [PseudoMetrizableSpace α]
    [OpensMeasurableSpace α] [SecondCountableTopology α] : StronglyMeasurable (id : α → α) :=
  measurable_id.StronglyMeasurable
#align strongly_measurable_id stronglyMeasurable_id
-/

end SecondCountableStronglyMeasurable

/- warning: strongly_measurable_iff_measurable_separable -> stronglyMeasurable_iff_measurable_separable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_4 : MeasurableSpace.{u2} β] [_inst_5 : BorelSpace.{u2} β _inst_2 _inst_4], Iff (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) (And (Measurable.{u1, u2} α β m _inst_4 f) (TopologicalSpace.IsSeparable.{u2} β _inst_2 (Set.range.{u2, succ u1} β α f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.PseudoMetrizableSpace.{u1} β _inst_2] [_inst_4 : MeasurableSpace.{u1} β] [_inst_5 : BorelSpace.{u1} β _inst_2 _inst_4], Iff (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) (And (Measurable.{u2, u1} α β m _inst_4 f) (TopologicalSpace.IsSeparable.{u1} β _inst_2 (Set.range.{u1, succ u2} β α f)))
Case conversion may be inaccurate. Consider using '#align strongly_measurable_iff_measurable_separable stronglyMeasurable_iff_measurable_separableₓ'. -/
/-- A function is strongly measurable if and only if it is measurable and has separable
range. -/
theorem stronglyMeasurable_iff_measurable_separable {m : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] :
    StronglyMeasurable f ↔ Measurable f ∧ IsSeparable (range f) :=
  by
  refine' ⟨fun H => ⟨H.Measurable, H.isSeparable_range⟩, _⟩
  rintro ⟨H, H'⟩
  letI := pseudo_metrizable_space_pseudo_metric β
  let g := cod_restrict f (closure (range f)) fun x => subset_closure (mem_range_self x)
  have fg : f = (coe : closure (range f) → β) ∘ g :=
    by
    ext x
    rfl
  have T : MeasurableEmbedding (coe : closure (range f) → β) :=
    by
    apply ClosedEmbedding.measurableEmbedding
    exact closedEmbedding_subtype_val isClosed_closure
  have g_meas : Measurable g := by
    rw [fg] at H
    exact T.measurable_comp_iff.1 H
  have : second_countable_topology (closure (range f)) :=
    by
    suffices separable_space (closure (range f)) by
      exact UniformSpace.secondCountable_of_separable _
    exact (is_separable.closure H').SeparableSpace
  have g_smeas : strongly_measurable g := Measurable.stronglyMeasurable g_meas
  rw [fg]
  exact continuous_subtype_coe.comp_strongly_measurable g_smeas
#align strongly_measurable_iff_measurable_separable stronglyMeasurable_iff_measurable_separable

/- warning: continuous.strongly_measurable -> Continuous.stronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : MeasurableSpace.{u1} α] [_inst_3 : TopologicalSpace.{u1} α] [_inst_4 : OpensMeasurableSpace.{u1} α _inst_3 _inst_2] {β : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_5] [h : SecondCountableTopologyEither.{u1, u2} α β _inst_3 _inst_5] {f : α -> β}, (Continuous.{u1, u2} α β _inst_3 _inst_5 f) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_5 _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} [_inst_2 : MeasurableSpace.{u2} α] [_inst_3 : TopologicalSpace.{u2} α] [_inst_4 : OpensMeasurableSpace.{u2} α _inst_3 _inst_2] {β : Type.{u1}} [_inst_5 : TopologicalSpace.{u1} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u1} β _inst_5] [h : SecondCountableTopologyEither.{u2, u1} α β _inst_3 _inst_5] {f : α -> β}, (Continuous.{u2, u1} α β _inst_3 _inst_5 f) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_5 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align continuous.strongly_measurable Continuous.stronglyMeasurableₓ'. -/
/-- A continuous function is strongly measurable when either the source space or the target space
is second-countable. -/
theorem Continuous.stronglyMeasurable [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] {β : Type _} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [h : SecondCountableTopologyEither α β] {f : α → β} (hf : Continuous f) :
    StronglyMeasurable f := by
  borelize β
  cases h.out
  · rw [stronglyMeasurable_iff_measurable_separable]
    refine' ⟨hf.measurable, _⟩
    rw [← image_univ]
    exact (is_separable_of_separable_space univ).image hf
  · exact hf.measurable.strongly_measurable
#align continuous.strongly_measurable Continuous.stronglyMeasurable

/- warning: embedding.comp_strongly_measurable_iff -> Embedding.comp_stronglyMeasurable_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u3} γ _inst_4] {g : β -> γ} {f : α -> β}, (Embedding.{u2, u3} β γ _inst_2 _inst_4 g) -> (Iff (MeasureTheory.StronglyMeasurable.{u1, u3} α γ _inst_4 m (fun (x : α) => g (f x))) (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {m : MeasurableSpace.{u3} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u1} γ _inst_4] {g : β -> γ} {f : α -> β}, (Embedding.{u2, u1} β γ _inst_2 _inst_4 g) -> (Iff (MeasureTheory.StronglyMeasurable.{u3, u1} α γ _inst_4 m (fun (x : α) => g (f x))) (MeasureTheory.StronglyMeasurable.{u3, u2} α β _inst_2 m f))
Case conversion may be inaccurate. Consider using '#align embedding.comp_strongly_measurable_iff Embedding.comp_stronglyMeasurable_iffₓ'. -/
/-- If `g` is a topological embedding, then `f` is strongly measurable iff `g ∘ f` is. -/
theorem Embedding.comp_stronglyMeasurable_iff {m : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] [TopologicalSpace γ] [PseudoMetrizableSpace γ] {g : β → γ} {f : α → β}
    (hg : Embedding g) : (StronglyMeasurable fun x => g (f x)) ↔ StronglyMeasurable f :=
  by
  letI := pseudo_metrizable_space_pseudo_metric γ
  borelize β γ
  refine'
    ⟨fun H => stronglyMeasurable_iff_measurable_separable.2 ⟨_, _⟩, fun H =>
      hg.continuous.comp_strongly_measurable H⟩
  · let G : β → range g := cod_restrict g (range g) mem_range_self
    have hG : ClosedEmbedding G :=
      { hg.cod_restrict _ _ with
        closed_range := by
          convert isClosed_univ
          apply eq_univ_of_forall
          rintro ⟨-, ⟨x, rfl⟩⟩
          exact mem_range_self x }
    have : Measurable (G ∘ f) := Measurable.subtype_mk H.measurable
    exact hG.measurable_embedding.measurable_comp_iff.1 this
  · have : IsSeparable (g ⁻¹' range (g ∘ f)) := hg.is_separable_preimage H.is_separable_range
    convert this
    ext x
    simp [hg.inj.eq_iff]
#align embedding.comp_strongly_measurable_iff Embedding.comp_stronglyMeasurable_iff

/- warning: strongly_measurable_of_tendsto -> stronglyMeasurable_of_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] (u : Filter.{u3} ι) [_inst_4 : Filter.NeBot.{u3} ι u] [_inst_5 : Filter.IsCountablyGenerated.{u3} ι u] {f : ι -> α -> β} {g : α -> β}, (forall (i : ι), MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m (f i)) -> (Filter.Tendsto.{u3, max u1 u2} ι (α -> β) f u (nhds.{max u1 u2} (α -> β) (Pi.topologicalSpace.{u1, u2} α (fun (ᾰ : α) => β) (fun (a : α) => _inst_2)) g)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Type.{u3}} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : TopologicalSpace.PseudoMetrizableSpace.{u1} β _inst_2] (u : Filter.{u3} ι) [_inst_4 : Filter.NeBot.{u3} ι u] [_inst_5 : Filter.IsCountablyGenerated.{u3} ι u] {f : ι -> α -> β} {g : α -> β}, (forall (i : ι), MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m (f i)) -> (Filter.Tendsto.{u3, max u2 u1} ι (α -> β) f u (nhds.{max u2 u1} (α -> β) (Pi.topologicalSpace.{u2, u1} α (fun (ᾰ : α) => β) (fun (a : α) => _inst_2)) g)) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m g)
Case conversion may be inaccurate. Consider using '#align strongly_measurable_of_tendsto stronglyMeasurable_of_tendstoₓ'. -/
/-- A sequential limit of strongly measurable functions is strongly measurable. -/
theorem stronglyMeasurable_of_tendsto {ι : Type _} {m : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] (u : Filter ι) [NeBot u] [IsCountablyGenerated u] {f : ι → α → β}
    {g : α → β} (hf : ∀ i, StronglyMeasurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    StronglyMeasurable g := by
  borelize β
  refine' stronglyMeasurable_iff_measurable_separable.2 ⟨_, _⟩
  · exact measurable_of_tendsto_metrizable' u (fun i => (hf i).Measurable) limUnder
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : IsSeparable (closure (⋃ i, range (f (v i)))) :=
      (is_separable_Union fun i => (hf (v i)).isSeparable_range).closure
    apply this.mono
    rintro _ ⟨x, rfl⟩
    rw [tendsto_pi_nhds] at lim
    apply mem_closure_of_tendsto ((limUnder x).comp hv)
    apply eventually_of_forall fun n => _
    apply mem_Union_of_mem n
    exact mem_range_self _
#align strongly_measurable_of_tendsto stronglyMeasurable_of_tendsto

/- warning: measure_theory.strongly_measurable.piecewise -> MeasureTheory.StronglyMeasurable.piecewise is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : α -> β} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} {_x : DecidablePred.{succ u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x s)}, (MeasurableSet.{u1} α m s) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m g) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m (Set.piecewise.{u1, succ u2} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _x j)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : α -> β} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} {_x : DecidablePred.{succ u2} α (fun (_x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) _x s)}, (MeasurableSet.{u2} α m s) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m g) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m (Set.piecewise.{u2, succ u1} α (fun (ᾰ : α) => β) s f g (fun (j : α) => _x j)))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.piecewise MeasureTheory.StronglyMeasurable.piecewiseₓ'. -/
protected theorem piecewise {m : MeasurableSpace α} [TopologicalSpace β] {s : Set α}
    {_ : DecidablePred (· ∈ s)} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (Set.piecewise s f g) :=
  by
  refine' ⟨fun n => simple_func.piecewise s hs (hf.approx n) (hg.approx n), fun x => _⟩
  by_cases hx : x ∈ s
  · simpa [hx] using hf.tendsto_approx x
  · simpa [hx] using hg.tendsto_approx x
#align measure_theory.strongly_measurable.piecewise MeasureTheory.StronglyMeasurable.piecewise

/- warning: measure_theory.strongly_measurable.ite -> MeasureTheory.StronglyMeasurable.ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {g : α -> β} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] {p : α -> Prop} {_x : DecidablePred.{succ u1} α p}, (MeasurableSet.{u1} α m (setOf.{u1} α (fun (a : α) => p a))) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m g) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m (fun (x : α) => ite.{succ u2} β (p x) (_x x) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {g : α -> β} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] {p : α -> Prop} {_x : DecidablePred.{succ u2} α p}, (MeasurableSet.{u2} α m (setOf.{u2} α (fun (a : α) => p a))) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m g) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m (fun (x : α) => ite.{succ u1} β (p x) (_x x) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.ite MeasureTheory.StronglyMeasurable.iteₓ'. -/
/-- this is slightly different from `strongly_measurable.piecewise`. It can be used to show
`strongly_measurable (ite (x=0) 0 1)` by
`exact strongly_measurable.ite (measurable_set_singleton 0) strongly_measurable_const
strongly_measurable_const`, but replacing `strongly_measurable.ite` by
`strongly_measurable.piecewise` in that example proof does not work. -/
protected theorem ite {m : MeasurableSpace α} [TopologicalSpace β] {p : α → Prop}
    {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a }) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable fun x => ite (p x) (f x) (g x) :=
  StronglyMeasurable.piecewise hp hf hg
#align measure_theory.strongly_measurable.ite MeasureTheory.StronglyMeasurable.ite

/- warning: strongly_measurable_of_strongly_measurable_union_cover -> stronglyMeasurable_of_stronglyMeasurable_union_cover is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} (s : Set.{u1} α) (t : Set.{u1} α), (MeasurableSet.{u1} α m s) -> (MeasurableSet.{u1} α m t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.univ.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β _inst_2 (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) m) (fun (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) a))) -> (MeasureTheory.StronglyMeasurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) β _inst_2 (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) m) (fun (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) => f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t))))) a))) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} (s : Set.{u2} α) (t : Set.{u2} α), (MeasurableSet.{u2} α m s) -> (MeasurableSet.{u2} α m t) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Set.univ.{u2} α) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s t)) -> (MeasureTheory.StronglyMeasurable.{u2, u1} (Set.Elem.{u2} α s) β _inst_2 (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) m) (fun (a : Set.Elem.{u2} α s) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) a))) -> (MeasureTheory.StronglyMeasurable.{u2, u1} (Set.Elem.{u2} α t) β _inst_2 (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) m) (fun (a : Set.Elem.{u2} α t) => f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x t) a))) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f)
Case conversion may be inaccurate. Consider using '#align strongly_measurable_of_strongly_measurable_union_cover stronglyMeasurable_of_stronglyMeasurable_union_coverₓ'. -/
theorem stronglyMeasurable_of_stronglyMeasurable_union_cover {m : MeasurableSpace α}
    [TopologicalSpace β] {f : α → β} (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : univ ⊆ s ∪ t) (hc : StronglyMeasurable fun a : s => f a)
    (hd : StronglyMeasurable fun a : t => f a) : StronglyMeasurable f := by
  classical
    let f : ℕ → α →ₛ β := fun n =>
      { toFun := fun x =>
          if hx : x ∈ s then hc.approx n ⟨x, hx⟩
          else hd.approx n ⟨x, by simpa [hx] using h (mem_univ x)⟩
        measurableSet_fiber' := by
          intro x
          convert(hs.subtype_image ((hc.approx n).measurableSet_fiber x)).union
              ((ht.subtype_image ((hd.approx n).measurableSet_fiber x)).diffₓ hs)
          ext1 y
          simp only [mem_union, mem_preimage, mem_singleton_iff, mem_image, SetCoe.exists,
            Subtype.coe_mk, exists_and_right, exists_eq_right, mem_diff]
          by_cases hy : y ∈ s
          · rw [dif_pos hy]
            simp only [hy, exists_true_left, not_true, and_false_iff, or_false_iff]
          · rw [dif_neg hy]
            have A : y ∈ t := by simpa [hy] using h (mem_univ y)
            simp only [A, hy, false_or_iff, IsEmpty.exists_iff, not_false_iff, and_true_iff,
              exists_true_left]
        finite_range' :=
          by
          apply ((hc.approx n).finite_range.union (hd.approx n).finite_range).Subset
          rintro - ⟨y, rfl⟩
          dsimp
          by_cases hy : y ∈ s
          · left
            rw [dif_pos hy]
            exact mem_range_self _
          · right
            rw [dif_neg hy]
            exact mem_range_self _ }
    refine' ⟨f, fun y => _⟩
    by_cases hy : y ∈ s
    · convert hc.tendsto_approx ⟨y, hy⟩ using 1
      ext1 n
      simp only [dif_pos hy, simple_func.apply_mk]
    · have A : y ∈ t := by simpa [hy] using h (mem_univ y)
      convert hd.tendsto_approx ⟨y, A⟩ using 1
      ext1 n
      simp only [dif_neg hy, simple_func.apply_mk]
#align strongly_measurable_of_strongly_measurable_union_cover stronglyMeasurable_of_stronglyMeasurable_union_cover

/- warning: strongly_measurable_of_restrict_of_restrict_compl -> stronglyMeasurable_of_restrict_of_restrict_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (MeasureTheory.StronglyMeasurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β _inst_2 (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) m) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) s f)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) β _inst_2 (Subtype.instMeasurableSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) m) (Set.restrict.{u1, u2} α (fun (ᾰ : α) => β) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) f)) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α}, (MeasurableSet.{u2} α m s) -> (MeasureTheory.StronglyMeasurable.{u2, u1} (Set.Elem.{u2} α s) β _inst_2 (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) m) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) s f)) -> (MeasureTheory.StronglyMeasurable.{u2, u1} (Set.Elem.{u2} α (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) β _inst_2 (Subtype.instMeasurableSpace.{u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) m) (Set.restrict.{u2, u1} α (fun (ᾰ : α) => β) (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s) f)) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f)
Case conversion may be inaccurate. Consider using '#align strongly_measurable_of_restrict_of_restrict_compl stronglyMeasurable_of_restrict_of_restrict_complₓ'. -/
theorem stronglyMeasurable_of_restrict_of_restrict_compl {m : MeasurableSpace α}
    [TopologicalSpace β] {f : α → β} {s : Set α} (hs : MeasurableSet s)
    (h₁ : StronglyMeasurable (s.restrict f)) (h₂ : StronglyMeasurable (sᶜ.restrict f)) :
    StronglyMeasurable f :=
  stronglyMeasurable_of_stronglyMeasurable_union_cover s (sᶜ) hs hs.compl (union_compl_self s).ge h₁
    h₂
#align strongly_measurable_of_restrict_of_restrict_compl stronglyMeasurable_of_restrict_of_restrict_compl

/- warning: measure_theory.strongly_measurable.indicator -> MeasureTheory.StronglyMeasurable.indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Zero.{u2} β], (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (forall {s : Set.{u1} α}, (MeasurableSet.{u1} α m s) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m (Set.indicator.{u1, u2} α β _inst_3 s f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : Zero.{u1} β], (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) -> (forall {s : Set.{u2} α}, (MeasurableSet.{u2} α m s) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m (Set.indicator.{u2, u1} α β _inst_3 s f)))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.indicator MeasureTheory.StronglyMeasurable.indicatorₓ'. -/
protected theorem indicator {m : MeasurableSpace α} [TopologicalSpace β] [Zero β]
    (hf : StronglyMeasurable f) {s : Set α} (hs : MeasurableSet s) :
    StronglyMeasurable (s.indicator f) :=
  hf.piecewise hs stronglyMeasurable_const
#align measure_theory.strongly_measurable.indicator MeasureTheory.StronglyMeasurable.indicator

/- warning: measure_theory.strongly_measurable.dist -> MeasureTheory.StronglyMeasurable.dist is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {β : Type.{u2}} [_inst_2 : PseudoMetricSpace.{u2} β] {f : α -> β} {g : α -> β}, (MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) m f) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β _inst_2)) m g) -> (MeasureTheory.StronglyMeasurable.{u1, 0} α Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) m (fun (x : α) => Dist.dist.{u2} β (PseudoMetricSpace.toHasDist.{u2} β _inst_2) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {β : Type.{u1}} [_inst_2 : PseudoMetricSpace.{u1} β] {f : α -> β} {g : α -> β}, (MeasureTheory.StronglyMeasurable.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β _inst_2)) m f) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β _inst_2)) m g) -> (MeasureTheory.StronglyMeasurable.{u2, 0} α Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) m (fun (x : α) => Dist.dist.{u1} β (PseudoMetricSpace.toDist.{u1} β _inst_2) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.dist MeasureTheory.StronglyMeasurable.distₓ'. -/
protected theorem dist {m : MeasurableSpace α} {β : Type _} [PseudoMetricSpace β] {f g : α → β}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => dist (f x) (g x) :=
  continuous_dist.comp_stronglyMeasurable (hf.prod_mk hg)
#align measure_theory.strongly_measurable.dist MeasureTheory.StronglyMeasurable.dist

/- warning: measure_theory.strongly_measurable.norm -> MeasureTheory.StronglyMeasurable.norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {β : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} β] {f : α -> β}, (MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_2))) m f) -> (MeasureTheory.StronglyMeasurable.{u1, 0} α Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) m (fun (x : α) => Norm.norm.{u2} β (SeminormedAddCommGroup.toHasNorm.{u2} β _inst_2) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {β : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} β] {f : α -> β}, (MeasureTheory.StronglyMeasurable.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} β _inst_2))) m f) -> (MeasureTheory.StronglyMeasurable.{u2, 0} α Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) m (fun (x : α) => Norm.norm.{u1} β (SeminormedAddCommGroup.toNorm.{u1} β _inst_2) (f x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.norm MeasureTheory.StronglyMeasurable.normₓ'. -/
protected theorem norm {m : MeasurableSpace α} {β : Type _} [SeminormedAddCommGroup β] {f : α → β}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ‖f x‖ :=
  continuous_norm.comp_stronglyMeasurable hf
#align measure_theory.strongly_measurable.norm MeasureTheory.StronglyMeasurable.norm

/- warning: measure_theory.strongly_measurable.nnnorm -> MeasureTheory.StronglyMeasurable.nnnorm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {β : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} β] {f : α -> β}, (MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_2))) m f) -> (MeasureTheory.StronglyMeasurable.{u1, 0} α NNReal NNReal.topologicalSpace m (fun (x : α) => NNNorm.nnnorm.{u2} β (SeminormedAddGroup.toNNNorm.{u2} β (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} β _inst_2)) (f x)))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {β : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} β] {f : α -> β}, (MeasureTheory.StronglyMeasurable.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} β _inst_2))) m f) -> (MeasureTheory.StronglyMeasurable.{u2, 0} α NNReal NNReal.instTopologicalSpaceNNReal m (fun (x : α) => NNNorm.nnnorm.{u1} β (SeminormedAddGroup.toNNNorm.{u1} β (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} β _inst_2)) (f x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.nnnorm MeasureTheory.StronglyMeasurable.nnnormₓ'. -/
protected theorem nnnorm {m : MeasurableSpace α} {β : Type _} [SeminormedAddCommGroup β] {f : α → β}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ‖f x‖₊ :=
  continuous_nnnorm.comp_stronglyMeasurable hf
#align measure_theory.strongly_measurable.nnnorm MeasureTheory.StronglyMeasurable.nnnorm

/- warning: measure_theory.strongly_measurable.ennnorm -> MeasureTheory.StronglyMeasurable.ennnorm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {β : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} β] {f : α -> β}, (MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_2))) m f) -> (Measurable.{u1, 0} α ENNReal m ENNReal.measurableSpace (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (NNNorm.nnnorm.{u2} β (SeminormedAddGroup.toNNNorm.{u2} β (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} β _inst_2)) (f a))))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {β : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} β] {f : α -> β}, (MeasureTheory.StronglyMeasurable.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u1} β (PseudoMetricSpace.toUniformSpace.{u1} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} β _inst_2))) m f) -> (Measurable.{u2, 0} α ENNReal m ENNReal.measurableSpace (fun (a : α) => ENNReal.some (NNNorm.nnnorm.{u1} β (SeminormedAddGroup.toNNNorm.{u1} β (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} β _inst_2)) (f a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.ennnorm MeasureTheory.StronglyMeasurable.ennnormₓ'. -/
protected theorem ennnorm {m : MeasurableSpace α} {β : Type _} [SeminormedAddCommGroup β]
    {f : α → β} (hf : StronglyMeasurable f) : Measurable fun a => (‖f a‖₊ : ℝ≥0∞) :=
  (ENNReal.continuous_coe.comp_stronglyMeasurable hf.nnnorm).Measurable
#align measure_theory.strongly_measurable.ennnorm MeasureTheory.StronglyMeasurable.ennnorm

/- warning: measure_theory.strongly_measurable.real_to_nnreal -> MeasureTheory.StronglyMeasurable.real_toNNReal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> Real}, (MeasureTheory.StronglyMeasurable.{u1, 0} α Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) m f) -> (MeasureTheory.StronglyMeasurable.{u1, 0} α NNReal NNReal.topologicalSpace m (fun (x : α) => Real.toNNReal (f x)))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {f : α -> Real}, (MeasureTheory.StronglyMeasurable.{u1, 0} α Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) m f) -> (MeasureTheory.StronglyMeasurable.{u1, 0} α NNReal NNReal.instTopologicalSpaceNNReal m (fun (x : α) => Real.toNNReal (f x)))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.real_to_nnreal MeasureTheory.StronglyMeasurable.real_toNNRealₓ'. -/
protected theorem real_toNNReal {m : MeasurableSpace α} {f : α → ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => (f x).toNNReal :=
  continuous_real_toNNReal.comp_stronglyMeasurable hf
#align measure_theory.strongly_measurable.real_to_nnreal MeasureTheory.StronglyMeasurable.real_toNNReal

/- warning: measurable_embedding.strongly_measurable_extend -> MeasurableEmbedding.stronglyMeasurable_extend is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β} {g : α -> γ} {g' : γ -> β} {mα : MeasurableSpace.{u1} α} {mγ : MeasurableSpace.{u3} γ} [_inst_2 : TopologicalSpace.{u2} β], (MeasurableEmbedding.{u1, u3} α γ mα mγ g) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 mα f) -> (MeasureTheory.StronglyMeasurable.{u3, u2} γ β _inst_2 mγ g') -> (MeasureTheory.StronglyMeasurable.{u3, u2} γ β _inst_2 mγ (Function.extend.{succ u1, succ u3, succ u2} α γ β g f g'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {f : α -> β} {g : α -> γ} {g' : γ -> β} {mα : MeasurableSpace.{u3} α} {mγ : MeasurableSpace.{u2} γ} [_inst_2 : TopologicalSpace.{u1} β], (MeasurableEmbedding.{u3, u2} α γ mα mγ g) -> (MeasureTheory.StronglyMeasurable.{u3, u1} α β _inst_2 mα f) -> (MeasureTheory.StronglyMeasurable.{u2, u1} γ β _inst_2 mγ g') -> (MeasureTheory.StronglyMeasurable.{u2, u1} γ β _inst_2 mγ (Function.extend.{succ u3, succ u2, succ u1} α γ β g f g'))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.strongly_measurable_extend MeasurableEmbedding.stronglyMeasurable_extendₓ'. -/
theorem MeasurableEmbedding.stronglyMeasurable_extend {f : α → β} {g : α → γ} {g' : γ → β}
    {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} [TopologicalSpace β]
    (hg : MeasurableEmbedding g) (hf : StronglyMeasurable f) (hg' : StronglyMeasurable g') :
    StronglyMeasurable (Function.extend g f g') :=
  by
  refine' ⟨fun n => simple_func.extend (hf.approx n) g hg (hg'.approx n), _⟩
  intro x
  by_cases hx : ∃ y, g y = x
  · rcases hx with ⟨y, rfl⟩
    simpa only [simple_func.extend_apply, hg.injective, injective.extend_apply] using
      hf.tendsto_approx y
  ·
    simpa only [hx, simple_func.extend_apply', not_false_iff, extend_apply'] using
      hg'.tendsto_approx x
#align measurable_embedding.strongly_measurable_extend MeasurableEmbedding.stronglyMeasurable_extend

/- warning: measurable_embedding.exists_strongly_measurable_extend -> MeasurableEmbedding.exists_stronglyMeasurable_extend is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β} {g : α -> γ} {mα : MeasurableSpace.{u1} α} {mγ : MeasurableSpace.{u3} γ} [_inst_2 : TopologicalSpace.{u2} β], (MeasurableEmbedding.{u1, u3} α γ mα mγ g) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 mα f) -> (γ -> (Nonempty.{succ u2} β)) -> (Exists.{max (succ u3) (succ u2)} (γ -> β) (fun (f' : γ -> β) => And (MeasureTheory.StronglyMeasurable.{u3, u2} γ β _inst_2 mγ f') (Eq.{max (succ u1) (succ u2)} (α -> β) (Function.comp.{succ u1, succ u3, succ u2} α γ β f' g) f)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {f : α -> β} {g : α -> γ} {mα : MeasurableSpace.{u3} α} {mγ : MeasurableSpace.{u2} γ} [_inst_2 : TopologicalSpace.{u1} β], (MeasurableEmbedding.{u3, u2} α γ mα mγ g) -> (MeasureTheory.StronglyMeasurable.{u3, u1} α β _inst_2 mα f) -> (γ -> (Nonempty.{succ u1} β)) -> (Exists.{max (succ u1) (succ u2)} (γ -> β) (fun (f' : γ -> β) => And (MeasureTheory.StronglyMeasurable.{u2, u1} γ β _inst_2 mγ f') (Eq.{max (succ u3) (succ u1)} (α -> β) (Function.comp.{succ u3, succ u2, succ u1} α γ β f' g) f)))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.exists_strongly_measurable_extend MeasurableEmbedding.exists_stronglyMeasurable_extendₓ'. -/
theorem MeasurableEmbedding.exists_stronglyMeasurable_extend {f : α → β} {g : α → γ}
    {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} [TopologicalSpace β]
    (hg : MeasurableEmbedding g) (hf : StronglyMeasurable f) (hne : γ → Nonempty β) :
    ∃ f' : γ → β, StronglyMeasurable f' ∧ f' ∘ g = f :=
  ⟨Function.extend g f fun x => Classical.choice (hne x),
    hg.stronglyMeasurable_extend hf (stronglyMeasurable_const' fun _ _ => rfl),
    funext fun x => hg.Injective.extend_apply _ _ _⟩
#align measurable_embedding.exists_strongly_measurable_extend MeasurableEmbedding.exists_stronglyMeasurable_extend

/- warning: measure_theory.strongly_measurable.measurable_set_eq_fun -> MeasureTheory.StronglyMeasurable.measurableSet_eq_fun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {E : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} E] [_inst_3 : TopologicalSpace.MetrizableSpace.{u2} E _inst_2] {f : α -> E} {g : α -> E}, (MeasureTheory.StronglyMeasurable.{u1, u2} α E _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α E _inst_2 m g) -> (MeasurableSet.{u1} α m (setOf.{u1} α (fun (x : α) => Eq.{succ u2} E (f x) (g x))))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {E : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} E] [_inst_3 : TopologicalSpace.MetrizableSpace.{u1} E _inst_2] {f : α -> E} {g : α -> E}, (MeasureTheory.StronglyMeasurable.{u2, u1} α E _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α E _inst_2 m g) -> (MeasurableSet.{u2} α m (setOf.{u2} α (fun (x : α) => Eq.{succ u1} E (f x) (g x))))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.measurable_set_eq_fun MeasureTheory.StronglyMeasurable.measurableSet_eq_funₓ'. -/
theorem measurableSet_eq_fun {m : MeasurableSpace α} {E} [TopologicalSpace E] [MetrizableSpace E]
    {f g : α → E} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    MeasurableSet { x | f x = g x } := by
  borelize (E × E)
  exact (hf.prod_mk hg).Measurable is_closed_diagonal.measurable_set
#align measure_theory.strongly_measurable.measurable_set_eq_fun MeasureTheory.StronglyMeasurable.measurableSet_eq_fun

/- warning: measure_theory.strongly_measurable.measurable_set_lt -> MeasureTheory.StronglyMeasurable.measurableSet_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : LinearOrder.{u2} β] [_inst_4 : OrderClosedTopology.{u2} β _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_3))))] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] {f : α -> β} {g : α -> β}, (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m g) -> (MeasurableSet.{u1} α m (setOf.{u1} α (fun (a : α) => LT.lt.{u2} β (Preorder.toHasLt.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_3))))) (f a) (g a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : LinearOrder.{u1} β] [_inst_4 : OrderClosedTopology.{u1} β _inst_2 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_3)))))] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u1} β _inst_2] {f : α -> β} {g : α -> β}, (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m g) -> (MeasurableSet.{u2} α m (setOf.{u2} α (fun (a : α) => LT.lt.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_3)))))) (f a) (g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.measurable_set_lt MeasureTheory.StronglyMeasurable.measurableSet_ltₓ'. -/
theorem measurableSet_lt {m : MeasurableSpace α} [TopologicalSpace β] [LinearOrder β]
    [OrderClosedTopology β] [PseudoMetrizableSpace β] {f g : α → β} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : MeasurableSet { a | f a < g a } :=
  by
  borelize (β × β)
  exact (hf.prod_mk hg).Measurable is_open_lt_prod.measurable_set
#align measure_theory.strongly_measurable.measurable_set_lt MeasureTheory.StronglyMeasurable.measurableSet_lt

/- warning: measure_theory.strongly_measurable.measurable_set_le -> MeasureTheory.StronglyMeasurable.measurableSet_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Preorder.{u2} β] [_inst_4 : OrderClosedTopology.{u2} β _inst_2 _inst_3] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] {f : α -> β} {g : α -> β}, (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m g) -> (MeasurableSet.{u1} α m (setOf.{u1} α (fun (a : α) => LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_3) (f a) (g a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : Preorder.{u1} β] [_inst_4 : OrderClosedTopology.{u1} β _inst_2 _inst_3] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u1} β _inst_2] {f : α -> β} {g : α -> β}, (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m g) -> (MeasurableSet.{u2} α m (setOf.{u2} α (fun (a : α) => LE.le.{u1} β (Preorder.toLE.{u1} β _inst_3) (f a) (g a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.measurable_set_le MeasureTheory.StronglyMeasurable.measurableSet_leₓ'. -/
theorem measurableSet_le {m : MeasurableSpace α} [TopologicalSpace β] [Preorder β]
    [OrderClosedTopology β] [PseudoMetrizableSpace β] {f g : α → β} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : MeasurableSet { a | f a ≤ g a } :=
  by
  borelize (β × β)
  exact (hf.prod_mk hg).Measurable is_closed_le_prod.measurable_set
#align measure_theory.strongly_measurable.measurable_set_le MeasureTheory.StronglyMeasurable.measurableSet_le

/- warning: measure_theory.strongly_measurable.strongly_measurable_in_set -> MeasureTheory.StronglyMeasurable.stronglyMeasurable_in_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Zero.{u2} β] {s : Set.{u1} α} {f : α -> β}, (MeasurableSet.{u1} α m s) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) -> (forall (x : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) -> (Eq.{succ u2} β (f x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3))))) -> (Exists.{max 1 (succ u1) (succ u2)} (Nat -> (MeasureTheory.SimpleFunc.{u1, u2} α m β)) (fun (fs : Nat -> (MeasureTheory.SimpleFunc.{u1, u2} α m β)) => And (forall (x : α), Filter.Tendsto.{0, u2} Nat β (fun (n : Nat) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m) (fs n) x) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{u2} β _inst_2 (f x))) (forall (x : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) -> (forall (n : Nat), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m) (fs n) x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3)))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : Zero.{u1} β] {s : Set.{u2} α} {f : α -> β}, (MeasurableSet.{u2} α m s) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) -> (forall (x : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) -> (Eq.{succ u1} β (f x) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3)))) -> (Exists.{max (succ u2) (succ u1)} (Nat -> (MeasureTheory.SimpleFunc.{u2, u1} α m β)) (fun (fs : Nat -> (MeasureTheory.SimpleFunc.{u2, u1} α m β)) => And (forall (x : α), Filter.Tendsto.{0, u1} Nat β (fun (n : Nat) => MeasureTheory.SimpleFunc.toFun.{u2, u1} α m β (fs n) x) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{u1} β _inst_2 (f x))) (forall (x : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) -> (forall (n : Nat), Eq.{succ u1} β (MeasureTheory.SimpleFunc.toFun.{u2, u1} α m β (fs n) x) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.strongly_measurable_in_set MeasureTheory.StronglyMeasurable.stronglyMeasurable_in_setₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ∉ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ∉ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ∉ » s) -/
theorem stronglyMeasurable_in_set {m : MeasurableSpace α} [TopologicalSpace β] [Zero β] {s : Set α}
    {f : α → β} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hf_zero : ∀ (x) (_ : x ∉ s), f x = 0) :
    ∃ fs : ℕ → α →ₛ β,
      (∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) ∧ ∀ (x) (_ : x ∉ s) (n), fs n x = 0 :=
  by
  let g_seq_s : ℕ → @simple_func α m β := fun n => (hf.approx n).restrict s
  have hg_eq : ∀ x ∈ s, ∀ n, g_seq_s n x = hf.approx n x :=
    by
    intro x hx n
    rw [simple_func.coe_restrict _ hs, Set.indicator_of_mem hx]
  have hg_zero : ∀ (x) (_ : x ∉ s), ∀ n, g_seq_s n x = 0 :=
    by
    intro x hx n
    rw [simple_func.coe_restrict _ hs, Set.indicator_of_not_mem hx]
  refine' ⟨g_seq_s, fun x => _, hg_zero⟩
  by_cases hx : x ∈ s
  · simp_rw [hg_eq x hx]
    exact hf.tendsto_approx x
  · simp_rw [hg_zero x hx, hf_zero x hx]
    exact tendsto_const_nhds
#align measure_theory.strongly_measurable.strongly_measurable_in_set MeasureTheory.StronglyMeasurable.stronglyMeasurable_in_set

/- warning: measure_theory.strongly_measurable.strongly_measurable_of_measurable_space_le_on -> MeasureTheory.StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {m : MeasurableSpace.{u1} α} {m₂ : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} E] [_inst_3 : Zero.{u2} E] {s : Set.{u1} α} {f : α -> E}, (MeasurableSet.{u1} α m s) -> (forall (t : Set.{u1} α), (MeasurableSet.{u1} α m (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) -> (MeasurableSet.{u1} α m₂ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α E _inst_2 m f) -> (forall (x : α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) -> (Eq.{succ u2} E (f x) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E _inst_3))))) -> (MeasureTheory.StronglyMeasurable.{u1, u2} α E _inst_2 m₂ f)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {m : MeasurableSpace.{u2} α} {m₂ : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} E] [_inst_3 : Zero.{u1} E] {s : Set.{u2} α} {f : α -> E}, (MeasurableSet.{u2} α m s) -> (forall (t : Set.{u2} α), (MeasurableSet.{u2} α m (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t)) -> (MeasurableSet.{u2} α m₂ (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) s t))) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α E _inst_2 m f) -> (forall (x : α), (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s)) -> (Eq.{succ u1} E (f x) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E _inst_3)))) -> (MeasureTheory.StronglyMeasurable.{u2, u1} α E _inst_2 m₂ f)
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.strongly_measurable_of_measurable_space_le_on MeasureTheory.StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_onₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (x «expr ∉ » s) -/
/-- If the restriction to a set `s` of a σ-algebra `m` is included in the restriction to `s` of
another σ-algebra `m₂` (hypothesis `hs`), the set `s` is `m` measurable and a function `f` supported
on `s` is `m`-strongly-measurable, then `f` is also `m₂`-strongly-measurable. -/
theorem stronglyMeasurable_of_measurableSpace_le_on {α E} {m m₂ : MeasurableSpace α}
    [TopologicalSpace E] [Zero E] {s : Set α} {f : α → E} (hs_m : measurable_set[m] s)
    (hs : ∀ t, measurable_set[m] (s ∩ t) → measurable_set[m₂] (s ∩ t))
    (hf : strongly_measurable[m] f) (hf_zero : ∀ (x) (_ : x ∉ s), f x = 0) :
    strongly_measurable[m₂] f :=
  by
  have hs_m₂ : measurable_set[m₂] s := by
    rw [← Set.inter_univ s]
    refine' hs Set.univ _
    rwa [Set.inter_univ]
  obtain ⟨g_seq_s, hg_seq_tendsto, hg_seq_zero⟩ := strongly_measurable_in_set hs_m hf hf_zero
  let g_seq_s₂ : ℕ → @simple_func α m₂ E := fun n =>
    { toFun := g_seq_s n
      measurableSet_fiber' := fun x =>
        by
        rw [← Set.inter_univ (g_seq_s n ⁻¹' {x}), ← Set.union_compl_self s,
          Set.inter_union_distrib_left, Set.inter_comm (g_seq_s n ⁻¹' {x})]
        refine' MeasurableSet.union (hs _ (hs_m.inter _)) _
        · exact @simple_func.measurable_set_fiber _ _ m _ _
        by_cases hx : x = 0
        · suffices g_seq_s n ⁻¹' {x} ∩ sᶜ = sᶜ by
            rw [this]
            exact hs_m₂.compl
          ext1 y
          rw [hx, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
          exact ⟨fun h => h.2, fun h => ⟨hg_seq_zero y h n, h⟩⟩
        · suffices g_seq_s n ⁻¹' {x} ∩ sᶜ = ∅ by
            rw [this]
            exact MeasurableSet.empty
          ext1 y
          simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_compl_iff,
            mem_empty_iff_false, iff_false_iff, not_and, not_not_mem]
          refine' imp_of_not_imp_not _ _ fun hys => _
          rw [hg_seq_zero y hys n]
          exact Ne.symm hx
      finite_range' := @simple_func.finite_range _ _ m (g_seq_s n) }
  have hg_eq : ∀ x n, g_seq_s₂ n x = g_seq_s n x := fun x n => rfl
  refine' ⟨g_seq_s₂, fun x => _⟩
  simp_rw [hg_eq]
  exact hg_seq_tendsto x
#align measure_theory.strongly_measurable.strongly_measurable_of_measurable_space_le_on MeasureTheory.StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on

/- warning: measure_theory.strongly_measurable.exists_spanning_measurable_set_norm_le -> MeasureTheory.StronglyMeasurable.exists_spanning_measurableSet_norm_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_2 : SeminormedAddCommGroup.{u2} β] {m : MeasurableSpace.{u1} α} {m0 : MeasurableSpace.{u1} α} (hm : LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) m m0), (MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_2))) m f) -> (forall (μ : MeasureTheory.Measure.{u1} α m0) [_inst_3 : MeasureTheory.SigmaFinite.{u1} α m (MeasureTheory.Measure.trim.{u1} α m m0 μ hm)], Exists.{succ u1} (Nat -> (Set.{u1} α)) (fun (s : Nat -> (Set.{u1} α)) => And (forall (n : Nat), And (MeasurableSet.{u1} α m (s n)) (And (LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (s n)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (s n)) -> (LE.le.{0} Real Real.hasLe (Norm.norm.{u2} β (SeminormedAddCommGroup.toHasNorm.{u2} β _inst_2) (f x)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n))))) (Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i)) (Set.univ.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_2 : SeminormedAddCommGroup.{u2} β] {m : MeasurableSpace.{u1} α} {m0 : MeasurableSpace.{u1} α} (hm : LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.instLEMeasurableSpace.{u1} α) m m0), (MeasureTheory.StronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_2))) m f) -> (forall (μ : MeasureTheory.Measure.{u1} α m0) [_inst_3 : MeasureTheory.SigmaFinite.{u1} α m (MeasureTheory.Measure.trim.{u1} α m m0 μ hm)], Exists.{succ u1} (Nat -> (Set.{u1} α)) (fun (s : Nat -> (Set.{u1} α)) => And (forall (n : Nat), And (MeasurableSet.{u1} α m (s n)) (And (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u1} α (MeasureTheory.Measure.toOuterMeasure.{u1} α m0 μ) (s n)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (s n)) -> (LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} β (SeminormedAddCommGroup.toNorm.{u2} β _inst_2) (f x)) (Nat.cast.{0} Real Real.natCast n))))) (Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (i : Nat) => s i)) (Set.univ.{u1} α))))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable.exists_spanning_measurable_set_norm_le MeasureTheory.StronglyMeasurable.exists_spanning_measurableSet_norm_leₓ'. -/
/-- If a function `f` is strongly measurable w.r.t. a sub-σ-algebra `m` and the measure is σ-finite
on `m`, then there exists spanning measurable sets with finite measure on which `f` has bounded
norm. In particular, `f` is integrable on each of those sets. -/
theorem exists_spanning_measurableSet_norm_le [SeminormedAddCommGroup β] {m m0 : MeasurableSpace α}
    (hm : m ≤ m0) (hf : strongly_measurable[m] f) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    ∃ s : ℕ → Set α,
      (∀ n, measurable_set[m] (s n) ∧ μ (s n) < ∞ ∧ ∀ x ∈ s n, ‖f x‖ ≤ n) ∧ (⋃ i, s i) = Set.univ :=
  by
  let sigma_finite_sets := spanning_sets (μ.trim hm)
  let norm_sets := fun n : ℕ => { x | ‖f x‖ ≤ n }
  have norm_sets_spanning : (⋃ n, norm_sets n) = Set.univ :=
    by
    ext1 x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true_iff]
    exact ⟨⌈‖f x‖⌉₊, Nat.le_ceil ‖f x‖⟩
  let sets n := sigma_finite_sets n ∩ norm_sets n
  have h_meas : ∀ n, measurable_set[m] (sets n) :=
    by
    refine' fun n => MeasurableSet.inter _ _
    · exact measurable_spanning_sets (μ.trim hm) n
    · exact hf.norm.measurable_set_le strongly_measurable_const
  have h_finite : ∀ n, μ (sets n) < ∞ :=
    by
    refine' fun n => (measure_mono (Set.inter_subset_left _ _)).trans_lt _
    exact (le_trim hm).trans_lt (measure_spanning_sets_lt_top (μ.trim hm) n)
  refine' ⟨sets, fun n => ⟨h_meas n, h_finite n, _⟩, _⟩
  · exact fun x hx => hx.2
  · have :
      (⋃ i, sigma_finite_sets i ∩ norm_sets i) = (⋃ i, sigma_finite_sets i) ∩ ⋃ i, norm_sets i :=
      by
      refine' Set.iUnion_inter_of_monotone (monotone_spanning_sets (μ.trim hm)) fun i j hij x => _
      simp only [norm_sets, Set.mem_setOf_eq]
      refine' fun hif => hif.trans _
      exact_mod_cast hij
    rw [this, norm_sets_spanning, Union_spanning_sets (μ.trim hm), Set.inter_univ]
#align measure_theory.strongly_measurable.exists_spanning_measurable_set_norm_le MeasureTheory.StronglyMeasurable.exists_spanning_measurableSet_norm_le

end StronglyMeasurable

/-! ## Finitely strongly measurable functions -/


/- warning: measure_theory.fin_strongly_measurable_zero -> MeasureTheory.finStronglyMeasurable_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : Zero.{u2} β] [_inst_3 : TopologicalSpace.{u2} β], MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_3 _inst_2 m (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_2))))) μ
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : Zero.{u1} β] [_inst_3 : TopologicalSpace.{u1} β], MeasureTheory.FinStronglyMeasurable.{u2, u1} α β _inst_3 _inst_2 m (OfNat.ofNat.{max u2 u1} (α -> β) 0 (Zero.toOfNat0.{max u2 u1} (α -> β) (Pi.instZero.{u2, u1} α (fun (a._@.Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic._hyg.11808 : α) => β) (fun (i : α) => _inst_2)))) μ
Case conversion may be inaccurate. Consider using '#align measure_theory.fin_strongly_measurable_zero MeasureTheory.finStronglyMeasurable_zeroₓ'. -/
theorem finStronglyMeasurable_zero {α β} {m : MeasurableSpace α} {μ : Measure α} [Zero β]
    [TopologicalSpace β] : FinStronglyMeasurable (0 : α → β) μ :=
  ⟨0, by
    simp only [Pi.zero_apply, simple_func.coe_zero, support_zero', measure_empty,
      WithTop.zero_lt_top, forall_const],
    fun n => tendsto_const_nhds⟩
#align measure_theory.fin_strongly_measurable_zero MeasureTheory.finStronglyMeasurable_zero

namespace FinStronglyMeasurable

variable {m0 : MeasurableSpace α} {μ : Measure α} {f g : α → β}

#print MeasureTheory.FinStronglyMeasurable.aefinStronglyMeasurable /-
theorem aefinStronglyMeasurable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ) :
    AEFinStronglyMeasurable f μ :=
  ⟨f, hf, ae_eq_refl f⟩
#align measure_theory.fin_strongly_measurable.ae_fin_strongly_measurable MeasureTheory.FinStronglyMeasurable.aefinStronglyMeasurable
-/

section sequence

variable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ)

#print MeasureTheory.FinStronglyMeasurable.approx /-
/-- A sequence of simple functions such that `∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x))`
and `∀ n, μ (support (hf.approx n)) < ∞`. These properties are given by
`fin_strongly_measurable.tendsto_approx` and `fin_strongly_measurable.fin_support_approx`. -/
protected noncomputable def approx : ℕ → α →ₛ β :=
  hf.some
#align measure_theory.fin_strongly_measurable.approx MeasureTheory.FinStronglyMeasurable.approx
-/

/- warning: measure_theory.fin_strongly_measurable.fin_support_approx -> MeasureTheory.FinStronglyMeasurable.fin_support_approx is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} [_inst_2 : Zero.{u2} β] [_inst_3 : TopologicalSpace.{u2} β] (hf : MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_3 _inst_2 m0 f μ) (n : Nat), LT.lt.{0} ENNReal (Preorder.toHasLt.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (coeFn.{succ u1, succ u1} (MeasureTheory.Measure.{u1} α m0) (fun (_x : MeasureTheory.Measure.{u1} α m0) => (Set.{u1} α) -> ENNReal) (MeasureTheory.Measure.instCoeFun.{u1} α m0) μ (Function.support.{u1, u2} α β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m0 β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m0 β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m0) (MeasureTheory.FinStronglyMeasurable.approx.{u1, u2} α β m0 μ f _inst_2 _inst_3 hf n)))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m0 : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m0} {f : α -> β} [_inst_2 : Zero.{u1} β] [_inst_3 : TopologicalSpace.{u1} β] (hf : MeasureTheory.FinStronglyMeasurable.{u2, u1} α β _inst_3 _inst_2 m0 f μ) (n : Nat), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.OuterMeasure.measureOf.{u2} α (MeasureTheory.Measure.toOuterMeasure.{u2} α m0 μ) (Function.support.{u2, u1} α β _inst_2 (MeasureTheory.SimpleFunc.toFun.{u2, u1} α m0 β (MeasureTheory.FinStronglyMeasurable.approx.{u2, u1} α β m0 μ f _inst_2 _inst_3 hf n)))) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align measure_theory.fin_strongly_measurable.fin_support_approx MeasureTheory.FinStronglyMeasurable.fin_support_approxₓ'. -/
protected theorem fin_support_approx : ∀ n, μ (support (hf.approx n)) < ∞ :=
  hf.choose_spec.1
#align measure_theory.fin_strongly_measurable.fin_support_approx MeasureTheory.FinStronglyMeasurable.fin_support_approx

#print MeasureTheory.FinStronglyMeasurable.tendsto_approx /-
protected theorem tendsto_approx : ∀ x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x)) :=
  hf.choose_spec.2
#align measure_theory.fin_strongly_measurable.tendsto_approx MeasureTheory.FinStronglyMeasurable.tendsto_approx
-/

end sequence

#print MeasureTheory.FinStronglyMeasurable.stronglyMeasurable /-
protected theorem stronglyMeasurable [Zero β] [TopologicalSpace β]
    (hf : FinStronglyMeasurable f μ) : StronglyMeasurable f :=
  ⟨hf.approx, hf.tendsto_approx⟩
#align measure_theory.fin_strongly_measurable.strongly_measurable MeasureTheory.FinStronglyMeasurable.stronglyMeasurable
-/

/- warning: measure_theory.fin_strongly_measurable.exists_set_sigma_finite -> MeasureTheory.FinStronglyMeasurable.exists_set_sigmaFinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} [_inst_2 : Zero.{u2} β] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : T2Space.{u2} β _inst_3], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_3 _inst_2 m0 f μ) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (MeasurableSet.{u1} α m0 t) (And (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)) -> (Eq.{succ u2} β (f x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2))))) (MeasureTheory.SigmaFinite.{u1} α m0 (MeasureTheory.Measure.restrict.{u1} α m0 μ t)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} [_inst_2 : Zero.{u2} β] [_inst_3 : TopologicalSpace.{u2} β] [_inst_4 : T2Space.{u2} β _inst_3], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_3 _inst_2 m0 f μ) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (MeasurableSet.{u1} α m0 t) (And (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t)) -> (Eq.{succ u2} β (f x) (OfNat.ofNat.{u2} β 0 (Zero.toOfNat0.{u2} β _inst_2)))) (MeasureTheory.SigmaFinite.{u1} α m0 (MeasureTheory.Measure.restrict.{u1} α m0 μ t)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.fin_strongly_measurable.exists_set_sigma_finite MeasureTheory.FinStronglyMeasurable.exists_set_sigmaFiniteₓ'. -/
theorem exists_set_sigmaFinite [Zero β] [TopologicalSpace β] [T2Space β]
    (hf : FinStronglyMeasurable f μ) :
    ∃ t, MeasurableSet t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ SigmaFinite (μ.restrict t) :=
  by
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩
  let T n := support (fs n)
  have hT_meas : ∀ n, MeasurableSet (T n) := fun n => simple_func.measurable_set_support (fs n)
  let t := ⋃ n, T n
  refine' ⟨t, MeasurableSet.iUnion hT_meas, _, _⟩
  · have h_fs_zero : ∀ n, ∀ x ∈ tᶜ, fs n x = 0 :=
      by
      intro n x hxt
      rw [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hxt
      simpa using hxt n
    refine' fun x hxt => tendsto_nhds_unique (h_approx x) _
    rw [funext fun n => h_fs_zero n x hxt]
    exact tendsto_const_nhds
  · refine' ⟨⟨⟨fun n => tᶜ ∪ T n, fun n => trivial, fun n => _, _⟩⟩⟩
    · rw [measure.restrict_apply' (MeasurableSet.iUnion hT_meas), Set.union_inter_distrib_right,
        Set.compl_inter_self t, Set.empty_union]
      exact (measure_mono (Set.inter_subset_left _ _)).trans_lt (hT_lt_top n)
    · rw [← Set.union_iUnion (tᶜ) T]
      exact Set.compl_union_self _
#align measure_theory.fin_strongly_measurable.exists_set_sigma_finite MeasureTheory.FinStronglyMeasurable.exists_set_sigmaFinite

#print MeasureTheory.FinStronglyMeasurable.measurable /-
/-- A finitely strongly measurable function is measurable. -/
protected theorem measurable [Zero β] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] (hf : FinStronglyMeasurable f μ) : Measurable f :=
  hf.StronglyMeasurable.Measurable
#align measure_theory.fin_strongly_measurable.measurable MeasureTheory.FinStronglyMeasurable.measurable
-/

section Arithmetic

variable [TopologicalSpace β]

/- warning: measure_theory.fin_strongly_measurable.mul -> MeasureTheory.FinStronglyMeasurable.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} {g : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : MonoidWithZero.{u2} β] [_inst_4 : ContinuousMul.{u2} β _inst_2 (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3)))], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))) m0 f μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))) m0 g μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))) m0 (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))))) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} {g : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : MonoidWithZero.{u2} β] [_inst_4 : ContinuousMul.{u2} β _inst_2 (MulZeroClass.toMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3)))], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (MonoidWithZero.toZero.{u2} β _inst_3) m0 f μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (MonoidWithZero.toZero.{u2} β _inst_3) m0 g μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (MonoidWithZero.toZero.{u2} β _inst_3) m0 (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))))) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.fin_strongly_measurable.mul MeasureTheory.FinStronglyMeasurable.mulₓ'. -/
protected theorem mul [MonoidWithZero β] [ContinuousMul β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f * g) μ :=
  by
  refine'
    ⟨fun n => hf.approx n * hg.approx n, _, fun x =>
      (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩
  intro n
  exact (measure_mono (support_mul_subset_left _ _)).trans_lt (hf.fin_support_approx n)
#align measure_theory.fin_strongly_measurable.mul MeasureTheory.FinStronglyMeasurable.mul

/- warning: measure_theory.fin_strongly_measurable.add -> MeasureTheory.FinStronglyMeasurable.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} {g : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : AddMonoid.{u2} β] [_inst_4 : ContinuousAdd.{u2} β _inst_2 (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3))], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)) m0 f μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)) m0 g μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)) m0 (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHAdd.{max u1 u2} (α -> β) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)))) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} {g : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : AddMonoid.{u2} β] [_inst_4 : ContinuousAdd.{u2} β _inst_2 (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3))], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddMonoid.toZero.{u2} β _inst_3) m0 f μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddMonoid.toZero.{u2} β _inst_3) m0 g μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddMonoid.toZero.{u2} β _inst_3) m0 (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHAdd.{max u1 u2} (α -> β) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)))) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.fin_strongly_measurable.add MeasureTheory.FinStronglyMeasurable.addₓ'. -/
protected theorem add [AddMonoid β] [ContinuousAdd β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f + g) μ :=
  ⟨fun n => hf.approx n + hg.approx n, fun n =>
    (measure_mono (Function.support_add _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩
#align measure_theory.fin_strongly_measurable.add MeasureTheory.FinStronglyMeasurable.add

/- warning: measure_theory.fin_strongly_measurable.neg -> MeasureTheory.FinStronglyMeasurable.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : AddGroup.{u2} β] [_inst_4 : TopologicalAddGroup.{u2} β _inst_2 _inst_3], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) m0 f μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) m0 (Neg.neg.{max u1 u2} (α -> β) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) f) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : AddGroup.{u2} β] [_inst_4 : TopologicalAddGroup.{u2} β _inst_2 _inst_3], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) m0 f μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) m0 (Neg.neg.{max u1 u2} (α -> β) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3))))) f) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.fin_strongly_measurable.neg MeasureTheory.FinStronglyMeasurable.negₓ'. -/
protected theorem neg [AddGroup β] [TopologicalAddGroup β] (hf : FinStronglyMeasurable f μ) :
    FinStronglyMeasurable (-f) μ :=
  by
  refine' ⟨fun n => -hf.approx n, fun n => _, fun x => (hf.tendsto_approx x).neg⟩
  suffices μ (Function.support fun x => -(hf.approx n) x) < ∞ by convert this
  rw [Function.support_neg (hf.approx n)]
  exact hf.fin_support_approx n
#align measure_theory.fin_strongly_measurable.neg MeasureTheory.FinStronglyMeasurable.neg

/- warning: measure_theory.fin_strongly_measurable.sub -> MeasureTheory.FinStronglyMeasurable.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} {g : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : AddGroup.{u2} β] [_inst_4 : ContinuousSub.{u2} β _inst_2 (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) m0 f μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) m0 g μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) m0 (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} {g : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : AddGroup.{u2} β] [_inst_4 : ContinuousSub.{u2} β _inst_2 (SubNegMonoid.toSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) m0 f μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) m0 g μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) m0 (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.fin_strongly_measurable.sub MeasureTheory.FinStronglyMeasurable.subₓ'. -/
protected theorem sub [AddGroup β] [ContinuousSub β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f - g) μ :=
  ⟨fun n => hf.approx n - hg.approx n, fun n =>
    (measure_mono (Function.support_sub _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩
#align measure_theory.fin_strongly_measurable.sub MeasureTheory.FinStronglyMeasurable.sub

/- warning: measure_theory.fin_strongly_measurable.const_smul -> MeasureTheory.FinStronglyMeasurable.const_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} [_inst_2 : TopologicalSpace.{u2} β] {𝕜 : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} 𝕜] [_inst_4 : AddMonoid.{u2} β] [_inst_5 : Monoid.{u3} 𝕜] [_inst_6 : DistribMulAction.{u3, u2} 𝕜 β _inst_5 _inst_4] [_inst_7 : ContinuousSMul.{u3, u2} 𝕜 β (SMulZeroClass.toHasSmul.{u3, u2} 𝕜 β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_4)) (DistribSMul.toSmulZeroClass.{u3, u2} 𝕜 β (AddMonoid.toAddZeroClass.{u2} β _inst_4) (DistribMulAction.toDistribSMul.{u3, u2} 𝕜 β _inst_5 _inst_4 _inst_6))) _inst_3 _inst_2], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_4)) m0 f μ) -> (forall (c : 𝕜), MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_4)) m0 (SMul.smul.{u3, max u1 u2} 𝕜 (α -> β) (Function.hasSMul.{u1, u3, u2} α 𝕜 β (SMulZeroClass.toHasSmul.{u3, u2} 𝕜 β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_4)) (DistribSMul.toSmulZeroClass.{u3, u2} 𝕜 β (AddMonoid.toAddZeroClass.{u2} β _inst_4) (DistribMulAction.toDistribSMul.{u3, u2} 𝕜 β _inst_5 _inst_4 _inst_6)))) c f) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} [_inst_2 : TopologicalSpace.{u2} β] {𝕜 : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} 𝕜] [_inst_4 : AddMonoid.{u2} β] [_inst_5 : Monoid.{u3} 𝕜] [_inst_6 : DistribMulAction.{u3, u2} 𝕜 β _inst_5 _inst_4] [_inst_7 : ContinuousSMul.{u3, u2} 𝕜 β (SMulZeroClass.toSMul.{u3, u2} 𝕜 β (AddMonoid.toZero.{u2} β _inst_4) (DistribSMul.toSMulZeroClass.{u3, u2} 𝕜 β (AddMonoid.toAddZeroClass.{u2} β _inst_4) (DistribMulAction.toDistribSMul.{u3, u2} 𝕜 β _inst_5 _inst_4 _inst_6))) _inst_3 _inst_2], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddMonoid.toZero.{u2} β _inst_4) m0 f μ) -> (forall (c : 𝕜), MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 (AddMonoid.toZero.{u2} β _inst_4) m0 (HSMul.hSMul.{u3, max u1 u2, max u1 u2} 𝕜 (α -> β) (α -> β) (instHSMul.{u3, max u1 u2} 𝕜 (α -> β) (Pi.instSMul.{u1, u2, u3} α 𝕜 (fun (a._@.Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic._hyg.13158 : α) => β) (fun (i : α) => SMulZeroClass.toSMul.{u3, u2} 𝕜 β (AddMonoid.toZero.{u2} β _inst_4) (DistribSMul.toSMulZeroClass.{u3, u2} 𝕜 β (AddMonoid.toAddZeroClass.{u2} β _inst_4) (DistribMulAction.toDistribSMul.{u3, u2} 𝕜 β _inst_5 _inst_4 _inst_6))))) c f) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.fin_strongly_measurable.const_smul MeasureTheory.FinStronglyMeasurable.const_smulₓ'. -/
protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [AddMonoid β] [Monoid 𝕜]
    [DistribMulAction 𝕜 β] [ContinuousSMul 𝕜 β] (hf : FinStronglyMeasurable f μ) (c : 𝕜) :
    FinStronglyMeasurable (c • f) μ :=
  by
  refine' ⟨fun n => c • hf.approx n, fun n => _, fun x => (hf.tendsto_approx x).const_smul c⟩
  rw [simple_func.coe_smul]
  refine' (measure_mono (support_smul_subset_right c _)).trans_lt (hf.fin_support_approx n)
#align measure_theory.fin_strongly_measurable.const_smul MeasureTheory.FinStronglyMeasurable.const_smul

end Arithmetic

section Order

variable [TopologicalSpace β] [Zero β]

/- warning: measure_theory.fin_strongly_measurable.sup -> MeasureTheory.FinStronglyMeasurable.sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} {g : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Zero.{u2} β] [_inst_4 : SemilatticeSup.{u2} β] [_inst_5 : ContinuousSup.{u2} β _inst_2 (SemilatticeSup.toHasSup.{u2} β _inst_4)], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m0 f μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m0 g μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m0 (Sup.sup.{max u1 u2} (α -> β) (Pi.hasSup.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SemilatticeSup.toHasSup.{u2} β _inst_4)) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} {g : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Zero.{u2} β] [_inst_4 : SemilatticeSup.{u2} β] [_inst_5 : ContinuousSup.{u2} β _inst_2 (SemilatticeSup.toSup.{u2} β _inst_4)], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m0 f μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m0 g μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m0 (Sup.sup.{max u2 u1} (α -> β) (Pi.instSupForAll.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SemilatticeSup.toSup.{u2} β _inst_4)) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.fin_strongly_measurable.sup MeasureTheory.FinStronglyMeasurable.supₓ'. -/
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f ⊔ g) μ :=
  by
  refine'
    ⟨fun n => hf.approx n ⊔ hg.approx n, fun n => _, fun x =>
      (hf.tendsto_approx x).sup_right_nhds (hg.tendsto_approx x)⟩
  refine' (measure_mono (support_sup _ _)).trans_lt _
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩
#align measure_theory.fin_strongly_measurable.sup MeasureTheory.FinStronglyMeasurable.sup

/- warning: measure_theory.fin_strongly_measurable.inf -> MeasureTheory.FinStronglyMeasurable.inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} {g : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Zero.{u2} β] [_inst_4 : SemilatticeInf.{u2} β] [_inst_5 : ContinuousInf.{u2} β _inst_2 (SemilatticeInf.toHasInf.{u2} β _inst_4)], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m0 f μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m0 g μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m0 (Inf.inf.{max u1 u2} (α -> β) (Pi.hasInf.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SemilatticeInf.toHasInf.{u2} β _inst_4)) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} {f : α -> β} {g : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Zero.{u2} β] [_inst_4 : SemilatticeInf.{u2} β] [_inst_5 : ContinuousInf.{u2} β _inst_2 (SemilatticeInf.toInf.{u2} β _inst_4)], (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m0 f μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m0 g μ) -> (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m0 (Inf.inf.{max u2 u1} (α -> β) (Pi.instInfForAll.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SemilatticeInf.toInf.{u2} β _inst_4)) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.fin_strongly_measurable.inf MeasureTheory.FinStronglyMeasurable.infₓ'. -/
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f ⊓ g) μ :=
  by
  refine'
    ⟨fun n => hf.approx n ⊓ hg.approx n, fun n => _, fun x =>
      (hf.tendsto_approx x).inf_right_nhds (hg.tendsto_approx x)⟩
  refine' (measure_mono (support_inf _ _)).trans_lt _
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩
#align measure_theory.fin_strongly_measurable.inf MeasureTheory.FinStronglyMeasurable.inf

end Order

end FinStronglyMeasurable

/- warning: measure_theory.fin_strongly_measurable_iff_strongly_measurable_and_exists_set_sigma_finite -> MeasureTheory.finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : T2Space.{u2} β _inst_2] [_inst_4 : Zero.{u2} β] {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m}, Iff (MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_4 m f μ) (And (MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m f) (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (MeasurableSet.{u1} α m t) (And (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)) -> (Eq.{succ u2} β (f x) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_4))))) (MeasureTheory.SigmaFinite.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ t))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : T2Space.{u1} β _inst_2] [_inst_4 : Zero.{u1} β] {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m}, Iff (MeasureTheory.FinStronglyMeasurable.{u2, u1} α β _inst_2 _inst_4 m f μ) (And (MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m f) (Exists.{succ u2} (Set.{u2} α) (fun (t : Set.{u2} α) => And (MeasurableSet.{u2} α m t) (And (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) t)) -> (Eq.{succ u1} β (f x) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_4)))) (MeasureTheory.SigmaFinite.{u2} α m (MeasureTheory.Measure.restrict.{u2} α m μ t))))))
Case conversion may be inaccurate. Consider using '#align measure_theory.fin_strongly_measurable_iff_strongly_measurable_and_exists_set_sigma_finite MeasureTheory.finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFiniteₓ'. -/
theorem finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite {α β} {f : α → β}
    [TopologicalSpace β] [T2Space β] [Zero β] {m : MeasurableSpace α} {μ : Measure α} :
    FinStronglyMeasurable f μ ↔
      StronglyMeasurable f ∧
        ∃ t, MeasurableSet t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ SigmaFinite (μ.restrict t) :=
  ⟨fun hf => ⟨hf.StronglyMeasurable, hf.exists_set_sigmaFinite⟩, fun hf =>
    hf.1.finStronglyMeasurable_of_set_sigmaFinite hf.2.choose_spec.1 hf.2.choose_spec.2.1
      hf.2.choose_spec.2.2⟩
#align measure_theory.fin_strongly_measurable_iff_strongly_measurable_and_exists_set_sigma_finite MeasureTheory.finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite

/- warning: measure_theory.ae_fin_strongly_measurable_zero -> MeasureTheory.aefinStronglyMeasurable_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m) [_inst_2 : Zero.{u2} β] [_inst_3 : TopologicalSpace.{u2} β], MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_3 _inst_2 m (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_2))))) μ
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} (μ : MeasureTheory.Measure.{u2} α m) [_inst_2 : Zero.{u1} β] [_inst_3 : TopologicalSpace.{u1} β], MeasureTheory.AEFinStronglyMeasurable.{u2, u1} α β _inst_3 _inst_2 m (OfNat.ofNat.{max u2 u1} (α -> β) 0 (Zero.toOfNat0.{max u2 u1} (α -> β) (Pi.instZero.{u2, u1} α (fun (a._@.Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic._hyg.13622 : α) => β) (fun (i : α) => _inst_2)))) μ
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable_zero MeasureTheory.aefinStronglyMeasurable_zeroₓ'. -/
theorem aefinStronglyMeasurable_zero {α β} {m : MeasurableSpace α} (μ : Measure α) [Zero β]
    [TopologicalSpace β] : AEFinStronglyMeasurable (0 : α → β) μ :=
  ⟨0, finStronglyMeasurable_zero, EventuallyEq.rfl⟩
#align measure_theory.ae_fin_strongly_measurable_zero MeasureTheory.aefinStronglyMeasurable_zero

/-! ## Almost everywhere strongly measurable functions -/


/- warning: measure_theory.ae_strongly_measurable_const -> MeasureTheory.aestronglyMeasurable_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {b : β}, MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (fun (a : α) => b) μ
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {b : β}, MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m (fun (a : α) => b) μ
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable_const MeasureTheory.aestronglyMeasurable_constₓ'. -/
theorem aestronglyMeasurable_const {α β} {m : MeasurableSpace α} {μ : Measure α}
    [TopologicalSpace β] {b : β} : AEStronglyMeasurable (fun a : α => b) μ :=
  stronglyMeasurable_const.AEStronglyMeasurable
#align measure_theory.ae_strongly_measurable_const MeasureTheory.aestronglyMeasurable_const

/- warning: measure_theory.ae_strongly_measurable_one -> MeasureTheory.aestronglyMeasurable_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : One.{u2} β], MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (OfNat.ofNat.{max u1 u2} (α -> β) 1 (OfNat.mk.{max u1 u2} (α -> β) 1 (One.one.{max u1 u2} (α -> β) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_3))))) μ
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : One.{u1} β], MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m (OfNat.ofNat.{max u2 u1} (α -> β) 1 (One.toOfNat1.{max u2 u1} (α -> β) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic._hyg.13692 : α) => β) (fun (i : α) => _inst_3)))) μ
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable_one MeasureTheory.aestronglyMeasurable_oneₓ'. -/
@[to_additive]
theorem aestronglyMeasurable_one {α β} {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β]
    [One β] : AEStronglyMeasurable (1 : α → β) μ :=
  stronglyMeasurable_one.AEStronglyMeasurable
#align measure_theory.ae_strongly_measurable_one MeasureTheory.aestronglyMeasurable_one
#align measure_theory.ae_strongly_measurable_zero MeasureTheory.aestronglyMeasurable_zero

/- warning: measure_theory.subsingleton.ae_strongly_measurable -> MeasureTheory.Subsingleton.aestronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Subsingleton.{succ u2} β] {μ : MeasureTheory.Measure.{u1} α m} (f : α -> β), MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : Subsingleton.{succ u1} β] {μ : MeasureTheory.Measure.{u2} α m} (f : α -> β), MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ
Case conversion may be inaccurate. Consider using '#align measure_theory.subsingleton.ae_strongly_measurable MeasureTheory.Subsingleton.aestronglyMeasurableₓ'. -/
@[simp]
theorem Subsingleton.aestronglyMeasurable {m : MeasurableSpace α} [TopologicalSpace β]
    [Subsingleton β] {μ : Measure α} (f : α → β) : AEStronglyMeasurable f μ :=
  (Subsingleton.stronglyMeasurable f).AEStronglyMeasurable
#align measure_theory.subsingleton.ae_strongly_measurable MeasureTheory.Subsingleton.aestronglyMeasurable

/- warning: measure_theory.subsingleton.ae_strongly_measurable' -> MeasureTheory.Subsingleton.aestronglyMeasurable' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : Subsingleton.{succ u1} α] {μ : MeasureTheory.Measure.{u1} α m} (f : α -> β), MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : Subsingleton.{succ u2} α] {μ : MeasureTheory.Measure.{u2} α m} (f : α -> β), MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ
Case conversion may be inaccurate. Consider using '#align measure_theory.subsingleton.ae_strongly_measurable' MeasureTheory.Subsingleton.aestronglyMeasurable'ₓ'. -/
@[simp]
theorem Subsingleton.aestronglyMeasurable' {m : MeasurableSpace α} [TopologicalSpace β]
    [Subsingleton α] {μ : Measure α} (f : α → β) : AEStronglyMeasurable f μ :=
  (Subsingleton.stronglyMeasurable' f).AEStronglyMeasurable
#align measure_theory.subsingleton.ae_strongly_measurable' MeasureTheory.Subsingleton.aestronglyMeasurable'

/- warning: measure_theory.ae_strongly_measurable_zero_measure -> MeasureTheory.aestronglyMeasurable_zero_measure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} α] [_inst_3 : TopologicalSpace.{u2} β] (f : α -> β), MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_3 _inst_2 f (OfNat.ofNat.{u1} (MeasureTheory.Measure.{u1} α _inst_2) 0 (OfNat.mk.{u1} (MeasureTheory.Measure.{u1} α _inst_2) 0 (Zero.zero.{u1} (MeasureTheory.Measure.{u1} α _inst_2) (MeasureTheory.Measure.instZero.{u1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : MeasurableSpace.{u2} α] [_inst_3 : TopologicalSpace.{u1} β] (f : α -> β), MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_3 _inst_2 f (OfNat.ofNat.{u2} (MeasureTheory.Measure.{u2} α _inst_2) 0 (Zero.toOfNat0.{u2} (MeasureTheory.Measure.{u2} α _inst_2) (MeasureTheory.Measure.instZero.{u2} α _inst_2)))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable_zero_measure MeasureTheory.aestronglyMeasurable_zero_measureₓ'. -/
@[simp]
theorem aestronglyMeasurable_zero_measure [MeasurableSpace α] [TopologicalSpace β] (f : α → β) :
    AEStronglyMeasurable f (0 : Measure α) :=
  by
  nontriviality α
  inhabit α
  exact ⟨fun x => f default, strongly_measurable_const, rfl⟩
#align measure_theory.ae_strongly_measurable_zero_measure MeasureTheory.aestronglyMeasurable_zero_measure

/- warning: measure_theory.simple_func.ae_strongly_measurable -> MeasureTheory.SimpleFunc.aestronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] (f : MeasureTheory.SimpleFunc.{u1, u2} α m β), MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MeasureTheory.SimpleFunc.{u1, u2} α m β) (fun (_x : MeasureTheory.SimpleFunc.{u1, u2} α m β) => α -> β) (MeasureTheory.SimpleFunc.instCoeFun.{u1, u2} α β m) f) μ
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] (f : MeasureTheory.SimpleFunc.{u2, u1} α m β), MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m (MeasureTheory.SimpleFunc.toFun.{u2, u1} α m β f) μ
Case conversion may be inaccurate. Consider using '#align measure_theory.simple_func.ae_strongly_measurable MeasureTheory.SimpleFunc.aestronglyMeasurableₓ'. -/
theorem SimpleFunc.aestronglyMeasurable {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β]
    (f : α →ₛ β) : AEStronglyMeasurable f μ :=
  f.StronglyMeasurable.AEStronglyMeasurable
#align measure_theory.simple_func.ae_strongly_measurable MeasureTheory.SimpleFunc.aestronglyMeasurable

namespace AeStronglyMeasurable

variable {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] [TopologicalSpace γ]
  {f g : α → β}

section Mk

#print MeasureTheory.AEStronglyMeasurable.mk /-
/-- A `strongly_measurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`strongly_measurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : AEStronglyMeasurable f μ) : α → β :=
  hf.some
#align measure_theory.ae_strongly_measurable.mk MeasureTheory.AEStronglyMeasurable.mk
-/

/- warning: measure_theory.ae_strongly_measurable.strongly_measurable_mk -> MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ), MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 m (MeasureTheory.AEStronglyMeasurable.mk.{u1, u2} α β m μ _inst_2 f hf)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ), MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 m (MeasureTheory.AEStronglyMeasurable.mk.{u2, u1} α β m μ _inst_2 f hf)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.strongly_measurable_mk MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mkₓ'. -/
theorem stronglyMeasurable_mk (hf : AEStronglyMeasurable f μ) : StronglyMeasurable (hf.mk f) :=
  hf.choose_spec.1
#align measure_theory.ae_strongly_measurable.strongly_measurable_mk MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk

#print MeasureTheory.AEStronglyMeasurable.measurable_mk /-
theorem measurable_mk [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf : AEStronglyMeasurable f μ) : Measurable (hf.mk f) :=
  hf.stronglyMeasurable_mk.Measurable
#align measure_theory.ae_strongly_measurable.measurable_mk MeasureTheory.AEStronglyMeasurable.measurable_mk
-/

/- warning: measure_theory.ae_strongly_measurable.ae_eq_mk -> MeasureTheory.AEStronglyMeasurable.ae_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ), Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m μ) f (MeasureTheory.AEStronglyMeasurable.mk.{u1, u2} α β m μ _inst_2 f hf)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ), Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α m μ) f (MeasureTheory.AEStronglyMeasurable.mk.{u2, u1} α β m μ _inst_2 f hf)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.ae_eq_mk MeasureTheory.AEStronglyMeasurable.ae_eq_mkₓ'. -/
theorem ae_eq_mk (hf : AEStronglyMeasurable f μ) : f =ᵐ[μ] hf.mk f :=
  hf.choose_spec.2
#align measure_theory.ae_strongly_measurable.ae_eq_mk MeasureTheory.AEStronglyMeasurable.ae_eq_mk

#print MeasureTheory.AEStronglyMeasurable.aemeasurable /-
protected theorem aemeasurable {β} [MeasurableSpace β] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [BorelSpace β] {f : α → β} (hf : AEStronglyMeasurable f μ) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk.Measurable, hf.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.ae_measurable MeasureTheory.AEStronglyMeasurable.aemeasurable
-/

end Mk

/- warning: measure_theory.ae_strongly_measurable.congr -> MeasureTheory.AEStronglyMeasurable.congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m μ) f g) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m g μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {g : α -> β}, (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ) -> (Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α m μ) f g) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m g μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.congr MeasureTheory.AEStronglyMeasurable.congrₓ'. -/
theorem congr (hf : AEStronglyMeasurable f μ) (h : f =ᵐ[μ] g) : AEStronglyMeasurable g μ :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk, h.symm.trans hf.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.congr MeasureTheory.AEStronglyMeasurable.congr

/- warning: ae_strongly_measurable_congr -> aestronglyMeasurable_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β}, (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m μ) f g) -> (Iff (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m g μ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {g : α -> β}, (Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α m μ) f g) -> (Iff (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ) (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m g μ))
Case conversion may be inaccurate. Consider using '#align ae_strongly_measurable_congr aestronglyMeasurable_congrₓ'. -/
theorem aestronglyMeasurable_congr (h : f =ᵐ[μ] g) :
    AEStronglyMeasurable f μ ↔ AEStronglyMeasurable g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩
#align ae_strongly_measurable_congr aestronglyMeasurable_congr

/- warning: measure_theory.ae_strongly_measurable.mono_measure -> MeasureTheory.AEStronglyMeasurable.mono_measure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {ν : MeasureTheory.Measure.{u1} α m}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (LE.le.{u1} (MeasureTheory.Measure.{u1} α m) (Preorder.toHasLe.{u1} (MeasureTheory.Measure.{u1} α m) (PartialOrder.toPreorder.{u1} (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instPartialOrder.{u1} α m))) ν μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f ν)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {ν : MeasureTheory.Measure.{u2} α m}, (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ) -> (LE.le.{u2} (MeasureTheory.Measure.{u2} α m) (Preorder.toLE.{u2} (MeasureTheory.Measure.{u2} α m) (PartialOrder.toPreorder.{u2} (MeasureTheory.Measure.{u2} α m) (MeasureTheory.Measure.instPartialOrder.{u2} α m))) ν μ) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f ν)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.mono_measure MeasureTheory.AEStronglyMeasurable.mono_measureₓ'. -/
theorem mono_measure {ν : Measure α} (hf : AEStronglyMeasurable f μ) (h : ν ≤ μ) :
    AEStronglyMeasurable f ν :=
  ⟨hf.mk f, hf.stronglyMeasurable_mk, Eventually.filter_mono (ae_mono h) hf.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.mono_measure MeasureTheory.AEStronglyMeasurable.mono_measure

/- warning: measure_theory.ae_strongly_measurable.mono' -> MeasureTheory.AEStronglyMeasurable.mono' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {ν : MeasureTheory.Measure.{u1} α m}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.Measure.AbsolutelyContinuous.{u1} α m ν μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f ν)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {ν : MeasureTheory.Measure.{u2} α m}, (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ) -> (MeasureTheory.Measure.AbsolutelyContinuous.{u2} α m ν μ) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f ν)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.mono' MeasureTheory.AEStronglyMeasurable.mono'ₓ'. -/
protected theorem mono' {ν : Measure α} (h : AEStronglyMeasurable f μ) (h' : ν ≪ μ) :
    AEStronglyMeasurable f ν :=
  ⟨h.mk f, h.stronglyMeasurable_mk, h' h.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.mono' MeasureTheory.AEStronglyMeasurable.mono'

/- warning: measure_theory.ae_strongly_measurable.mono_set -> MeasureTheory.AEStronglyMeasurable.mono_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u1} α m μ t)) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u1} α m μ s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u2} α m μ t)) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u2} α m μ s))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.mono_set MeasureTheory.AEStronglyMeasurable.mono_setₓ'. -/
theorem mono_set {s t} (h : s ⊆ t) (ht : AEStronglyMeasurable f (μ.restrict t)) :
    AEStronglyMeasurable f (μ.restrict s) :=
  ht.mono_measure (restrict_mono h le_rfl)
#align measure_theory.ae_strongly_measurable.mono_set MeasureTheory.AEStronglyMeasurable.mono_set

/- warning: measure_theory.ae_strongly_measurable.restrict -> MeasureTheory.AEStronglyMeasurable.restrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (forall {s : Set.{u1} α}, MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u1} α m μ s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ) -> (forall {s : Set.{u2} α}, MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u2} α m μ s))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.restrict MeasureTheory.AEStronglyMeasurable.restrictₓ'. -/
protected theorem restrict (hfm : AEStronglyMeasurable f μ) {s} :
    AEStronglyMeasurable f (μ.restrict s) :=
  hfm.mono_measure Measure.restrict_le_self
#align measure_theory.ae_strongly_measurable.restrict MeasureTheory.AEStronglyMeasurable.restrict

/- warning: measure_theory.ae_strongly_measurable.ae_mem_imp_eq_mk -> MeasureTheory.AEStronglyMeasurable.ae_mem_imp_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {s : Set.{u1} α} (h : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u1} α m μ s)), Filter.Eventually.{u1} α (fun (x : α) => (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Eq.{succ u2} β (f x) (MeasureTheory.AEStronglyMeasurable.mk.{u1, u2} α β m (MeasureTheory.Measure.restrict.{u1} α m μ s) _inst_2 f h x))) (MeasureTheory.Measure.ae.{u1} α m μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {s : Set.{u2} α} (h : MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u2} α m μ s)), Filter.Eventually.{u2} α (fun (x : α) => (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (Eq.{succ u1} β (f x) (MeasureTheory.AEStronglyMeasurable.mk.{u2, u1} α β m (MeasureTheory.Measure.restrict.{u2} α m μ s) _inst_2 f h x))) (MeasureTheory.Measure.ae.{u2} α m μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.ae_mem_imp_eq_mk MeasureTheory.AEStronglyMeasurable.ae_mem_imp_eq_mkₓ'. -/
theorem ae_mem_imp_eq_mk {s} (h : AEStronglyMeasurable f (μ.restrict s)) :
    ∀ᵐ x ∂μ, x ∈ s → f x = h.mk f x :=
  ae_imp_of_ae_restrict h.ae_eq_mk
#align measure_theory.ae_strongly_measurable.ae_mem_imp_eq_mk MeasureTheory.AEStronglyMeasurable.ae_mem_imp_eq_mk

/- warning: continuous.comp_ae_strongly_measurable -> Continuous.comp_aestronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {g : β -> γ} {f : α -> β}, (Continuous.{u2, u3} β γ _inst_2 _inst_3 g) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u3} α γ _inst_3 m (fun (x : α) => g (f x)) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] {g : β -> γ} {f : α -> β}, (Continuous.{u3, u2} β γ _inst_2 _inst_3 g) -> (MeasureTheory.AEStronglyMeasurable.{u1, u3} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α γ _inst_3 m (fun (x : α) => g (f x)) μ)
Case conversion may be inaccurate. Consider using '#align continuous.comp_ae_strongly_measurable Continuous.comp_aestronglyMeasurableₓ'. -/
/-- The composition of a continuous function and an ae strongly measurable function is ae strongly
measurable. -/
theorem Continuous.comp_aestronglyMeasurable {g : β → γ} {f : α → β} (hg : Continuous g)
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => g (f x)) μ :=
  ⟨_, hg.comp_stronglyMeasurable hf.stronglyMeasurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk g⟩
#align continuous.comp_ae_strongly_measurable Continuous.comp_aestronglyMeasurable

/- warning: continuous.ae_strongly_measurable -> Continuous.aestronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_4 : TopologicalSpace.{u1} α] [_inst_5 : OpensMeasurableSpace.{u1} α _inst_4 m] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_7 : SecondCountableTopologyEither.{u1, u2} α β _inst_4 _inst_2], (Continuous.{u1, u2} α β _inst_4 _inst_2 f) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} [_inst_4 : TopologicalSpace.{u2} α] [_inst_5 : OpensMeasurableSpace.{u2} α _inst_4 m] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u1} β _inst_2] [_inst_7 : SecondCountableTopologyEither.{u2, u1} α β _inst_4 _inst_2], (Continuous.{u2, u1} α β _inst_4 _inst_2 f) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ)
Case conversion may be inaccurate. Consider using '#align continuous.ae_strongly_measurable Continuous.aestronglyMeasurableₓ'. -/
/-- A continuous function from `α` to `β` is ae strongly measurable when one of the two spaces is
second countable. -/
theorem Continuous.aestronglyMeasurable [TopologicalSpace α] [OpensMeasurableSpace α]
    [PseudoMetrizableSpace β] [SecondCountableTopologyEither α β] (hf : Continuous f) :
    AEStronglyMeasurable f μ :=
  hf.StronglyMeasurable.AEStronglyMeasurable
#align continuous.ae_strongly_measurable Continuous.aestronglyMeasurable

/- warning: measure_theory.ae_strongly_measurable.prod_mk -> MeasureTheory.AEStronglyMeasurable.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {f : α -> β} {g : α -> γ}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u3} α γ _inst_3 m g μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) m (fun (x : α) => Prod.mk.{u2, u3} β γ (f x) (g x)) μ)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {m : MeasurableSpace.{u3} α} {μ : MeasureTheory.Measure.{u3} α m} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {f : α -> β} {g : α -> γ}, (MeasureTheory.AEStronglyMeasurable.{u3, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u3, u1} α γ _inst_3 m g μ) -> (MeasureTheory.AEStronglyMeasurable.{u3, max u1 u2} α (Prod.{u2, u1} β γ) (instTopologicalSpaceProd.{u2, u1} β γ _inst_2 _inst_3) m (fun (x : α) => Prod.mk.{u2, u1} β γ (f x) (g x)) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.prod_mk MeasureTheory.AEStronglyMeasurable.prod_mkₓ'. -/
protected theorem prod_mk {f : α → β} {g : α → γ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (fun x => (f x, g x)) μ :=
  ⟨fun x => (hf.mk f x, hg.mk g x), hf.stronglyMeasurable_mk.prod_mk hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.prod_mk hg.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.prod_mk MeasureTheory.AEStronglyMeasurable.prod_mk

/- warning: measurable.ae_strongly_measurable -> Measurable.aestronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_4 : MeasurableSpace.{u2} β] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_6 : TopologicalSpace.SecondCountableTopology.{u2} β _inst_2] [_inst_7 : OpensMeasurableSpace.{u2} β _inst_2 _inst_4], (Measurable.{u1, u2} α β m _inst_4 f) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_4 : MeasurableSpace.{u1} β] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u1} β _inst_2] [_inst_6 : TopologicalSpace.SecondCountableTopology.{u1} β _inst_2] [_inst_7 : OpensMeasurableSpace.{u1} β _inst_2 _inst_4], (Measurable.{u2, u1} α β m _inst_4 f) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ)
Case conversion may be inaccurate. Consider using '#align measurable.ae_strongly_measurable Measurable.aestronglyMeasurableₓ'. -/
/-- In a space with second countable topology, measurable implies ae strongly measurable. -/
theorem Measurable.aestronglyMeasurable {m : MeasurableSpace α} {μ : Measure α} [MeasurableSpace β]
    [PseudoMetrizableSpace β] [SecondCountableTopology β] [OpensMeasurableSpace β]
    (hf : Measurable f) : AEStronglyMeasurable f μ :=
  hf.StronglyMeasurable.AEStronglyMeasurable
#align measurable.ae_strongly_measurable Measurable.aestronglyMeasurable

section Arithmetic

#print MeasureTheory.AEStronglyMeasurable.mul /-
@[to_additive]
protected theorem mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f * g) μ :=
  ⟨hf.mk f * hg.mk g, hf.stronglyMeasurable_mk.mul hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.mul hg.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.mul MeasureTheory.AEStronglyMeasurable.mul
#align measure_theory.ae_strongly_measurable.add MeasureTheory.AEStronglyMeasurable.add
-/

#print MeasureTheory.AEStronglyMeasurable.mul_const /-
@[to_additive]
protected theorem mul_const [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable f μ) (c : β) :
    AEStronglyMeasurable (fun x => f x * c) μ :=
  hf.mul aestronglyMeasurable_const
#align measure_theory.ae_strongly_measurable.mul_const MeasureTheory.AEStronglyMeasurable.mul_const
#align measure_theory.ae_strongly_measurable.add_const MeasureTheory.AEStronglyMeasurable.add_const
-/

#print MeasureTheory.AEStronglyMeasurable.const_mul /-
@[to_additive]
protected theorem const_mul [Mul β] [ContinuousMul β] (hf : AEStronglyMeasurable f μ) (c : β) :
    AEStronglyMeasurable (fun x => c * f x) μ :=
  aestronglyMeasurable_const.mul hf
#align measure_theory.ae_strongly_measurable.const_mul MeasureTheory.AEStronglyMeasurable.const_mul
#align measure_theory.ae_strongly_measurable.const_add MeasureTheory.AEStronglyMeasurable.const_add
-/

/- warning: measure_theory.ae_strongly_measurable.inv -> MeasureTheory.AEStronglyMeasurable.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_4 : Group.{u2} β] [_inst_5 : TopologicalGroup.{u2} β _inst_2 _inst_4], (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (Inv.inv.{max u1 u2} (α -> β) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => DivInvMonoid.toHasInv.{u2} β (Group.toDivInvMonoid.{u2} β _inst_4))) f) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_4 : Group.{u2} β] [_inst_5 : TopologicalGroup.{u2} β _inst_2 _inst_4], (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (Inv.inv.{max u2 u1} (α -> β) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => InvOneClass.toInv.{u2} β (DivInvOneMonoid.toInvOneClass.{u2} β (DivisionMonoid.toDivInvOneMonoid.{u2} β (Group.toDivisionMonoid.{u2} β _inst_4))))) f) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.inv MeasureTheory.AEStronglyMeasurable.invₓ'. -/
@[to_additive]
protected theorem inv [Group β] [TopologicalGroup β] (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable f⁻¹ μ :=
  ⟨(hf.mk f)⁻¹, hf.stronglyMeasurable_mk.inv, hf.ae_eq_mk.inv⟩
#align measure_theory.ae_strongly_measurable.inv MeasureTheory.AEStronglyMeasurable.inv
#align measure_theory.ae_strongly_measurable.neg MeasureTheory.AEStronglyMeasurable.neg

/- warning: measure_theory.ae_strongly_measurable.div -> MeasureTheory.AEStronglyMeasurable.div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_4 : Group.{u2} β] [_inst_5 : TopologicalGroup.{u2} β _inst_2 _inst_4], (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m g μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHDiv.{max u1 u2} (α -> β) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} β (Group.toDivInvMonoid.{u2} β _inst_4)))) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_4 : Group.{u2} β] [_inst_5 : TopologicalGroup.{u2} β _inst_2 _inst_4], (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m g μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHDiv.{max u1 u2} (α -> β) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => DivInvMonoid.toDiv.{u2} β (Group.toDivInvMonoid.{u2} β _inst_4)))) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.div MeasureTheory.AEStronglyMeasurable.divₓ'. -/
@[to_additive]
protected theorem div [Group β] [TopologicalGroup β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f / g) μ :=
  ⟨hf.mk f / hg.mk g, hf.stronglyMeasurable_mk.div hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.div hg.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.div MeasureTheory.AEStronglyMeasurable.div
#align measure_theory.ae_strongly_measurable.sub MeasureTheory.AEStronglyMeasurable.sub

#print MeasureTheory.AEStronglyMeasurable.smul /-
@[to_additive]
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    {g : α → β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => f x • g x) μ :=
  continuous_smul.comp_aestronglyMeasurable (hf.prod_mk hg)
#align measure_theory.ae_strongly_measurable.smul MeasureTheory.AEStronglyMeasurable.smul
#align measure_theory.ae_strongly_measurable.vadd MeasureTheory.AEStronglyMeasurable.vadd
-/

#print MeasureTheory.AEStronglyMeasurable.const_smul /-
protected theorem const_smul {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β]
    (hf : AEStronglyMeasurable f μ) (c : 𝕜) : AEStronglyMeasurable (c • f) μ :=
  ⟨c • hf.mk f, hf.stronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩
#align measure_theory.ae_strongly_measurable.const_smul MeasureTheory.AEStronglyMeasurable.const_smul
-/

#print MeasureTheory.AEStronglyMeasurable.const_smul' /-
protected theorem const_smul' {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β]
    (hf : AEStronglyMeasurable f μ) (c : 𝕜) : AEStronglyMeasurable (fun x => c • f x) μ :=
  hf.const_smul c
#align measure_theory.ae_strongly_measurable.const_smul' MeasureTheory.AEStronglyMeasurable.const_smul'
-/

#print MeasureTheory.AEStronglyMeasurable.smul_const /-
@[to_additive]
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α → 𝕜}
    (hf : AEStronglyMeasurable f μ) (c : β) : AEStronglyMeasurable (fun x => f x • c) μ :=
  continuous_smul.comp_aestronglyMeasurable (hf.prod_mk aestronglyMeasurable_const)
#align measure_theory.ae_strongly_measurable.smul_const MeasureTheory.AEStronglyMeasurable.smul_const
#align measure_theory.ae_strongly_measurable.vadd_const MeasureTheory.AEStronglyMeasurable.vadd_const
-/

end Arithmetic

section Order

/- warning: measure_theory.ae_strongly_measurable.sup -> MeasureTheory.AEStronglyMeasurable.sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_4 : SemilatticeSup.{u2} β] [_inst_5 : ContinuousSup.{u2} β _inst_2 (SemilatticeSup.toHasSup.{u2} β _inst_4)], (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m g μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (Sup.sup.{max u1 u2} (α -> β) (Pi.hasSup.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SemilatticeSup.toHasSup.{u2} β _inst_4)) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_4 : SemilatticeSup.{u2} β] [_inst_5 : ContinuousSup.{u2} β _inst_2 (SemilatticeSup.toSup.{u2} β _inst_4)], (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m g μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (Sup.sup.{max u2 u1} (α -> β) (Pi.instSupForAll.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SemilatticeSup.toSup.{u2} β _inst_4)) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.sup MeasureTheory.AEStronglyMeasurable.supₓ'. -/
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f ⊔ g) μ :=
  ⟨hf.mk f ⊔ hg.mk g, hf.stronglyMeasurable_mk.sup hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.sup MeasureTheory.AEStronglyMeasurable.sup

/- warning: measure_theory.ae_strongly_measurable.inf -> MeasureTheory.AEStronglyMeasurable.inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_4 : SemilatticeInf.{u2} β] [_inst_5 : ContinuousInf.{u2} β _inst_2 (SemilatticeInf.toHasInf.{u2} β _inst_4)], (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m g μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (Inf.inf.{max u1 u2} (α -> β) (Pi.hasInf.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SemilatticeInf.toHasInf.{u2} β _inst_4)) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_4 : SemilatticeInf.{u2} β] [_inst_5 : ContinuousInf.{u2} β _inst_2 (SemilatticeInf.toInf.{u2} β _inst_4)], (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m g μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (Inf.inf.{max u2 u1} (α -> β) (Pi.instInfForAll.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SemilatticeInf.toInf.{u2} β _inst_4)) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.inf MeasureTheory.AEStronglyMeasurable.infₓ'. -/
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) : AEStronglyMeasurable (f ⊓ g) μ :=
  ⟨hf.mk f ⊓ hg.mk g, hf.stronglyMeasurable_mk.inf hg.stronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩
#align measure_theory.ae_strongly_measurable.inf MeasureTheory.AEStronglyMeasurable.inf

end Order

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M : Type _} [Monoid M] [TopologicalSpace M] [ContinuousMul M]

/- warning: list.ae_strongly_measurable_prod' -> List.aestronglyMeasurable_prod' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {M : Type.{u2}} [_inst_4 : Monoid.{u2} M] [_inst_5 : TopologicalSpace.{u2} M] [_inst_6 : ContinuousMul.{u2} M _inst_5 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_4))] (l : List.{max u1 u2} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u1 u2, max u1 u2} (α -> M) (List.{max u1 u2} (α -> M)) (List.hasMem.{max u1 u2} (α -> M)) f l) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α M _inst_5 m f μ)) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α M _inst_5 m (List.prod.{max u1 u2} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_4))) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_4))) l) μ)
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {M : Type.{u1}} [_inst_4 : Monoid.{u1} M] [_inst_5 : TopologicalSpace.{u1} M] [_inst_6 : ContinuousMul.{u1} M _inst_5 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4))] (l : List.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (List.{max u2 u1} (α -> M)) (List.instMembershipList.{max u2 u1} (α -> M)) f l) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α M _inst_5 m f μ)) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α M _inst_5 m (List.prod.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4))) (Pi.instOne.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => Monoid.toOne.{u1} M _inst_4)) l) μ)
Case conversion may be inaccurate. Consider using '#align list.ae_strongly_measurable_prod' List.aestronglyMeasurable_prod'ₓ'. -/
@[to_additive]
theorem List.aestronglyMeasurable_prod' (l : List (α → M))
    (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) : AEStronglyMeasurable l.Prod μ :=
  by
  induction' l with f l ihl; · exact ae_strongly_measurable_one
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.ae_strongly_measurable_prod' List.aestronglyMeasurable_prod'
#align list.ae_strongly_measurable_sum' List.aestronglyMeasurable_sum'

/- warning: list.ae_strongly_measurable_prod -> List.aestronglyMeasurable_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {M : Type.{u2}} [_inst_4 : Monoid.{u2} M] [_inst_5 : TopologicalSpace.{u2} M] [_inst_6 : ContinuousMul.{u2} M _inst_5 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_4))] (l : List.{max u1 u2} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u1 u2, max u1 u2} (α -> M) (List.{max u1 u2} (α -> M)) (List.hasMem.{max u1 u2} (α -> M)) f l) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α M _inst_5 m f μ)) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α M _inst_5 m (fun (x : α) => List.prod.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_4)) (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M _inst_4)) (List.map.{max u1 u2, u2} (α -> M) M (fun (f : α -> M) => f x) l)) μ)
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {M : Type.{u1}} [_inst_4 : Monoid.{u1} M] [_inst_5 : TopologicalSpace.{u1} M] [_inst_6 : ContinuousMul.{u1} M _inst_5 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4))] (l : List.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (List.{max u2 u1} (α -> M)) (List.instMembershipList.{max u2 u1} (α -> M)) f l) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α M _inst_5 m f μ)) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α M _inst_5 m (fun (x : α) => List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_4)) (Monoid.toOne.{u1} M _inst_4) (List.map.{max u2 u1, u1} (α -> M) M (fun (f : α -> M) => f x) l)) μ)
Case conversion may be inaccurate. Consider using '#align list.ae_strongly_measurable_prod List.aestronglyMeasurable_prodₓ'. -/
@[to_additive]
theorem List.aestronglyMeasurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (l.map fun f : α → M => f x).Prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.ae_strongly_measurable_prod' hl
#align list.ae_strongly_measurable_prod List.aestronglyMeasurable_prod
#align list.ae_strongly_measurable_sum List.aestronglyMeasurable_sum

end Monoid

section CommMonoid

variable {M : Type _} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]

/- warning: multiset.ae_strongly_measurable_prod' -> Multiset.aestronglyMeasurable_prod' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {M : Type.{u2}} [_inst_4 : CommMonoid.{u2} M] [_inst_5 : TopologicalSpace.{u2} M] [_inst_6 : ContinuousMul.{u2} M _inst_5 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))] (l : Multiset.{max u1 u2} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u1 u2, max u1 u2} (α -> M) (Multiset.{max u1 u2} (α -> M)) (Multiset.hasMem.{max u1 u2} (α -> M)) f l) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α M _inst_5 m f μ)) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α M _inst_5 m (Multiset.prod.{max u1 u2} (α -> M) (Pi.commMonoid.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_4)) l) μ)
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] [_inst_5 : TopologicalSpace.{u1} M] [_inst_6 : ContinuousMul.{u1} M _inst_5 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))] (l : Multiset.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (Multiset.{max u2 u1} (α -> M)) (Multiset.instMembershipMultiset.{max u2 u1} (α -> M)) f l) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α M _inst_5 m f μ)) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α M _inst_5 m (Multiset.prod.{max u2 u1} (α -> M) (Pi.commMonoid.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_4)) l) μ)
Case conversion may be inaccurate. Consider using '#align multiset.ae_strongly_measurable_prod' Multiset.aestronglyMeasurable_prod'ₓ'. -/
@[to_additive]
theorem Multiset.aestronglyMeasurable_prod' (l : Multiset (α → M))
    (hl : ∀ f ∈ l, AEStronglyMeasurable f μ) : AEStronglyMeasurable l.Prod μ :=
  by
  rcases l with ⟨l⟩
  simpa using l.ae_strongly_measurable_prod' (by simpa using hl)
#align multiset.ae_strongly_measurable_prod' Multiset.aestronglyMeasurable_prod'
#align multiset.ae_strongly_measurable_sum' Multiset.aestronglyMeasurable_sum'

/- warning: multiset.ae_strongly_measurable_prod -> Multiset.aestronglyMeasurable_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {M : Type.{u2}} [_inst_4 : CommMonoid.{u2} M] [_inst_5 : TopologicalSpace.{u2} M] [_inst_6 : ContinuousMul.{u2} M _inst_5 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))] (s : Multiset.{max u1 u2} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u1 u2, max u1 u2} (α -> M) (Multiset.{max u1 u2} (α -> M)) (Multiset.hasMem.{max u1 u2} (α -> M)) f s) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α M _inst_5 m f μ)) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α M _inst_5 m (fun (x : α) => Multiset.prod.{u2} M _inst_4 (Multiset.map.{max u1 u2, u2} (α -> M) M (fun (f : α -> M) => f x) s)) μ)
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] [_inst_5 : TopologicalSpace.{u1} M] [_inst_6 : ContinuousMul.{u1} M _inst_5 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))] (s : Multiset.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (Multiset.{max u2 u1} (α -> M)) (Multiset.instMembershipMultiset.{max u2 u1} (α -> M)) f s) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α M _inst_5 m f μ)) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α M _inst_5 m (fun (x : α) => Multiset.prod.{u1} M _inst_4 (Multiset.map.{max u2 u1, u1} (α -> M) M (fun (f : α -> M) => f x) s)) μ)
Case conversion may be inaccurate. Consider using '#align multiset.ae_strongly_measurable_prod Multiset.aestronglyMeasurable_prodₓ'. -/
@[to_additive]
theorem Multiset.aestronglyMeasurable_prod (s : Multiset (α → M))
    (hs : ∀ f ∈ s, AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (s.map fun f : α → M => f x).Prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.ae_strongly_measurable_prod' hs
#align multiset.ae_strongly_measurable_prod Multiset.aestronglyMeasurable_prod
#align multiset.ae_strongly_measurable_sum Multiset.aestronglyMeasurable_sum

/- warning: finset.ae_strongly_measurable_prod' -> Finset.aestronglyMeasurable_prod' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {M : Type.{u2}} [_inst_4 : CommMonoid.{u2} M] [_inst_5 : TopologicalSpace.{u2} M] [_inst_6 : ContinuousMul.{u2} M _inst_5 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))] {ι : Type.{u3}} {f : ι -> α -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α M _inst_5 m (f i) μ)) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α M _inst_5 m (Finset.prod.{max u1 u2, u3} (α -> M) ι (Pi.commMonoid.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_4)) s (fun (i : ι) => f i)) μ)
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] [_inst_5 : TopologicalSpace.{u1} M] [_inst_6 : ContinuousMul.{u1} M _inst_5 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))] {ι : Type.{u3}} {f : ι -> α -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α M _inst_5 m (f i) μ)) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α M _inst_5 m (Finset.prod.{max u1 u2, u3} (α -> M) ι (Pi.commMonoid.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_4)) s (fun (i : ι) => f i)) μ)
Case conversion may be inaccurate. Consider using '#align finset.ae_strongly_measurable_prod' Finset.aestronglyMeasurable_prod'ₓ'. -/
@[to_additive]
theorem Finset.aestronglyMeasurable_prod' {ι : Type _} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) : AEStronglyMeasurable (∏ i in s, f i) μ :=
  Multiset.aestronglyMeasurable_prod' _ fun g hg =>
    let ⟨i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi
#align finset.ae_strongly_measurable_prod' Finset.aestronglyMeasurable_prod'
#align finset.ae_strongly_measurable_sum' Finset.aestronglyMeasurable_sum'

/- warning: finset.ae_strongly_measurable_prod -> Finset.aestronglyMeasurable_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {M : Type.{u2}} [_inst_4 : CommMonoid.{u2} M] [_inst_5 : TopologicalSpace.{u2} M] [_inst_6 : ContinuousMul.{u2} M _inst_5 (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))] {ι : Type.{u3}} {f : ι -> α -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) i s) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α M _inst_5 m (f i) μ)) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α M _inst_5 m (fun (a : α) => Finset.prod.{u2, u3} M ι _inst_4 s (fun (i : ι) => f i a)) μ)
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] [_inst_5 : TopologicalSpace.{u1} M] [_inst_6 : ContinuousMul.{u1} M _inst_5 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))] {ι : Type.{u3}} {f : ι -> α -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α M _inst_5 m (f i) μ)) -> (MeasureTheory.AEStronglyMeasurable.{u2, u1} α M _inst_5 m (fun (a : α) => Finset.prod.{u1, u3} M ι _inst_4 s (fun (i : ι) => f i a)) μ)
Case conversion may be inaccurate. Consider using '#align finset.ae_strongly_measurable_prod Finset.aestronglyMeasurable_prodₓ'. -/
@[to_additive]
theorem Finset.aestronglyMeasurable_prod {ι : Type _} {f : ι → α → M} (s : Finset ι)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun a => ∏ i in s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.ae_strongly_measurable_prod' hf
#align finset.ae_strongly_measurable_prod Finset.aestronglyMeasurable_prod
#align finset.ae_strongly_measurable_sum Finset.aestronglyMeasurable_sum

end CommMonoid

section SecondCountableAeStronglyMeasurable

variable [MeasurableSpace β]

#print AEMeasurable.aestronglyMeasurable /-
/-- In a space with second countable topology, measurable implies strongly measurable. -/
theorem AEMeasurable.aestronglyMeasurable [PseudoMetrizableSpace β] [OpensMeasurableSpace β]
    [SecondCountableTopology β] (hf : AEMeasurable f μ) : AEStronglyMeasurable f μ :=
  ⟨hf.mk f, hf.measurable_mk.StronglyMeasurable, hf.ae_eq_mk⟩
#align ae_measurable.ae_strongly_measurable AEMeasurable.aestronglyMeasurable
-/

#print aestronglyMeasurable_id /-
theorem aestronglyMeasurable_id {α : Type _} [TopologicalSpace α] [PseudoMetrizableSpace α]
    {m : MeasurableSpace α} [OpensMeasurableSpace α] [SecondCountableTopology α] {μ : Measure α} :
    AEStronglyMeasurable (id : α → α) μ :=
  aemeasurable_id.AEStronglyMeasurable
#align ae_strongly_measurable_id aestronglyMeasurable_id
-/

#print aestronglyMeasurable_iff_aemeasurable /-
/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
theorem aestronglyMeasurable_iff_aemeasurable [PseudoMetrizableSpace β] [BorelSpace β]
    [SecondCountableTopology β] : AEStronglyMeasurable f μ ↔ AEMeasurable f μ :=
  ⟨fun h => h.AEMeasurable, fun h => h.AEStronglyMeasurable⟩
#align ae_strongly_measurable_iff_ae_measurable aestronglyMeasurable_iff_aemeasurable
-/

end SecondCountableAeStronglyMeasurable

#print MeasureTheory.AEStronglyMeasurable.dist /-
protected theorem dist {β : Type _} [PseudoMetricSpace β] {f g : α → β}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => dist (f x) (g x)) μ :=
  continuous_dist.comp_aestronglyMeasurable (hf.prod_mk hg)
#align measure_theory.ae_strongly_measurable.dist MeasureTheory.AEStronglyMeasurable.dist
-/

#print MeasureTheory.AEStronglyMeasurable.norm /-
protected theorem norm {β : Type _} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => ‖f x‖) μ :=
  continuous_norm.comp_aestronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.norm MeasureTheory.AEStronglyMeasurable.norm
-/

/- warning: measure_theory.ae_strongly_measurable.nnnorm -> MeasureTheory.AEStronglyMeasurable.nnnorm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {β : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u2} β] {f : α -> β}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_4))) m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, 0} α NNReal NNReal.topologicalSpace m (fun (x : α) => NNNorm.nnnorm.{u2} β (SeminormedAddGroup.toNNNorm.{u2} β (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} β _inst_4)) (f x)) μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {β : Type.{u2}} [_inst_4 : SeminormedAddCommGroup.{u2} β] {f : α -> β}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u2} β (PseudoMetricSpace.toUniformSpace.{u2} β (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} β _inst_4))) m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, 0} α NNReal NNReal.instTopologicalSpaceNNReal m (fun (x : α) => NNNorm.nnnorm.{u2} β (SeminormedAddGroup.toNNNorm.{u2} β (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} β _inst_4)) (f x)) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.nnnorm MeasureTheory.AEStronglyMeasurable.nnnormₓ'. -/
protected theorem nnnorm {β : Type _} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => ‖f x‖₊) μ :=
  continuous_nnnorm.comp_aestronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.nnnorm MeasureTheory.AEStronglyMeasurable.nnnorm

#print MeasureTheory.AEStronglyMeasurable.ennnorm /-
protected theorem ennnorm {β : Type _} [SeminormedAddCommGroup β] {f : α → β}
    (hf : AEStronglyMeasurable f μ) : AEMeasurable (fun a => (‖f a‖₊ : ℝ≥0∞)) μ :=
  (ENNReal.continuous_coe.comp_aestronglyMeasurable hf.nnnorm).AEMeasurable
#align measure_theory.ae_strongly_measurable.ennnorm MeasureTheory.AEStronglyMeasurable.ennnorm
-/

#print MeasureTheory.AEStronglyMeasurable.edist /-
protected theorem edist {β : Type _} [SeminormedAddCommGroup β] {f g : α → β}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEMeasurable (fun a => edist (f a) (g a)) μ :=
  (continuous_edist.comp_aestronglyMeasurable (hf.prod_mk hg)).AEMeasurable
#align measure_theory.ae_strongly_measurable.edist MeasureTheory.AEStronglyMeasurable.edist
-/

/- warning: measure_theory.ae_strongly_measurable.real_to_nnreal -> MeasureTheory.AEStronglyMeasurable.real_toNNReal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> Real}, (MeasureTheory.AEStronglyMeasurable.{u1, 0} α Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, 0} α NNReal NNReal.topologicalSpace m (fun (x : α) => Real.toNNReal (f x)) μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {f : α -> Real}, (MeasureTheory.AEStronglyMeasurable.{u1, 0} α Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, 0} α NNReal NNReal.instTopologicalSpaceNNReal m (fun (x : α) => Real.toNNReal (f x)) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.real_to_nnreal MeasureTheory.AEStronglyMeasurable.real_toNNRealₓ'. -/
protected theorem real_toNNReal {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => (f x).toNNReal) μ :=
  continuous_real_toNNReal.comp_aestronglyMeasurable hf
#align measure_theory.ae_strongly_measurable.real_to_nnreal MeasureTheory.AEStronglyMeasurable.real_toNNReal

#print aestronglyMeasurable_indicator_iff /-
theorem aestronglyMeasurable_indicator_iff [Zero β] {s : Set α} (hs : MeasurableSet s) :
    AEStronglyMeasurable (indicator s f) μ ↔ AEStronglyMeasurable f (μ.restrict s) :=
  by
  constructor
  · intro h
    exact (h.mono_measure measure.restrict_le_self).congr (indicator_ae_eq_restrict hs)
  · intro h
    refine' ⟨indicator s (h.mk f), h.strongly_measurable_mk.indicator hs, _⟩
    have A : s.indicator f =ᵐ[μ.restrict s] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict hs).trans (h.ae_eq_mk.trans <| (indicator_ae_eq_restrict hs).symm)
    have B : s.indicator f =ᵐ[μ.restrict (sᶜ)] s.indicator (h.mk f) :=
      (indicator_ae_eq_restrict_compl hs).trans (indicator_ae_eq_restrict_compl hs).symm
    exact ae_of_ae_restrict_of_ae_restrict_compl _ A B
#align ae_strongly_measurable_indicator_iff aestronglyMeasurable_indicator_iff
-/

#print MeasureTheory.AEStronglyMeasurable.indicator /-
protected theorem indicator [Zero β] (hfm : AEStronglyMeasurable f μ) {s : Set α}
    (hs : MeasurableSet s) : AEStronglyMeasurable (s.indicator f) μ :=
  (aestronglyMeasurable_indicator_iff hs).mpr hfm.restrict
#align measure_theory.ae_strongly_measurable.indicator MeasureTheory.AEStronglyMeasurable.indicator
-/

#print MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_eq_fun /-
theorem nullMeasurableSet_eq_fun {E} [TopologicalSpace E] [MetrizableSpace E] {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { x | f x = g x } μ :=
  by
  apply
    (hf.strongly_measurable_mk.measurable_set_eq_fun
          hg.strongly_measurable_mk).NullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk]with x hfx hgx
  change (hf.mk f x = hg.mk g x) = (f x = g x)
  simp only [hfx, hgx]
#align measure_theory.ae_strongly_measurable.null_measurable_set_eq_fun MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_eq_fun
-/

/- warning: measure_theory.ae_strongly_measurable.null_measurable_set_lt -> MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : LinearOrder.{u2} β] [_inst_5 : OrderClosedTopology.{u2} β _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_4))))] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] {f : α -> β} {g : α -> β}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m g μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m (setOf.{u1} α (fun (a : α) => LT.lt.{u2} β (Preorder.toHasLt.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_4))))) (f a) (g a))) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : LinearOrder.{u2} β] [_inst_5 : OrderClosedTopology.{u2} β _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_4)))))] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] {f : α -> β} {g : α -> β}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m g μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m (setOf.{u1} α (fun (a : α) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_4)))))) (f a) (g a))) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.null_measurable_set_lt MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_ltₓ'. -/
theorem nullMeasurableSet_lt [LinearOrder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
    {f g : α → β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { a | f a < g a } μ :=
  by
  apply
    (hf.strongly_measurable_mk.measurable_set_lt hg.strongly_measurable_mk).NullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk]with x hfx hgx
  change (hf.mk f x < hg.mk g x) = (f x < g x)
  simp only [hfx, hgx]
#align measure_theory.ae_strongly_measurable.null_measurable_set_lt MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_lt

/- warning: measure_theory.ae_strongly_measurable.null_measurable_set_le -> MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] [_inst_5 : OrderClosedTopology.{u2} β _inst_2 _inst_4] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] {f : α -> β} {g : α -> β}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m g μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m (setOf.{u1} α (fun (a : α) => LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_4) (f a) (g a))) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : Preorder.{u2} β] [_inst_5 : OrderClosedTopology.{u2} β _inst_2 _inst_4] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] {f : α -> β} {g : α -> β}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m g μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m (setOf.{u1} α (fun (a : α) => LE.le.{u2} β (Preorder.toLE.{u2} β _inst_4) (f a) (g a))) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.null_measurable_set_le MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_leₓ'. -/
theorem nullMeasurableSet_le [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β]
    {f g : α → β} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    NullMeasurableSet { a | f a ≤ g a } μ :=
  by
  apply
    (hf.strongly_measurable_mk.measurable_set_le hg.strongly_measurable_mk).NullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk]with x hfx hgx
  change (hf.mk f x ≤ hg.mk g x) = (f x ≤ g x)
  simp only [hfx, hgx]
#align measure_theory.ae_strongly_measurable.null_measurable_set_le MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_le

#print aestronglyMeasurable_of_aestronglyMeasurable_trim /-
theorem aestronglyMeasurable_of_aestronglyMeasurable_trim {α} {m m0 : MeasurableSpace α}
    {μ : Measure α} (hm : m ≤ m0) {f : α → β} (hf : AEStronglyMeasurable f (μ.trim hm)) :
    AEStronglyMeasurable f μ :=
  ⟨hf.mk f, StronglyMeasurable.mono hf.stronglyMeasurable_mk hm, ae_eq_of_ae_eq_trim hf.ae_eq_mk⟩
#align ae_strongly_measurable_of_ae_strongly_measurable_trim aestronglyMeasurable_of_aestronglyMeasurable_trim
-/

/- warning: measure_theory.ae_strongly_measurable.comp_ae_measurable -> MeasureTheory.AEStronglyMeasurable.comp_aemeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {g : α -> β} {γ : Type.{u3}} {mγ : MeasurableSpace.{u3} γ} {mα : MeasurableSpace.{u1} α} {f : γ -> α} {μ : MeasureTheory.Measure.{u3} γ mγ}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 mα g (MeasureTheory.Measure.map.{u3, u1} γ α mα mγ f μ)) -> (AEMeasurable.{u3, u1} γ α mα mγ f μ) -> (MeasureTheory.AEStronglyMeasurable.{u3, u2} γ β _inst_2 mγ (Function.comp.{succ u3, succ u1, succ u2} γ α β g f) μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {g : α -> β} {γ : Type.{u3}} {mγ : MeasurableSpace.{u3} γ} {mα : MeasurableSpace.{u2} α} {f : γ -> α} {μ : MeasureTheory.Measure.{u3} γ mγ}, (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 mα g (MeasureTheory.Measure.map.{u3, u2} γ α mα mγ f μ)) -> (AEMeasurable.{u3, u2} γ α mα mγ f μ) -> (MeasureTheory.AEStronglyMeasurable.{u3, u1} γ β _inst_2 mγ (Function.comp.{succ u3, succ u2, succ u1} γ α β g f) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.comp_ae_measurable MeasureTheory.AEStronglyMeasurable.comp_aemeasurableₓ'. -/
theorem comp_aemeasurable {γ : Type _} {mγ : MeasurableSpace γ} {mα : MeasurableSpace α} {f : γ → α}
    {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    AEStronglyMeasurable (g ∘ f) μ :=
  ⟨hg.mk g ∘ hf.mk f, hg.stronglyMeasurable_mk.comp_measurable hf.measurable_mk,
    (ae_eq_comp hf hg.ae_eq_mk).trans (hf.ae_eq_mk.fun_comp (hg.mk g))⟩
#align measure_theory.ae_strongly_measurable.comp_ae_measurable MeasureTheory.AEStronglyMeasurable.comp_aemeasurable

/- warning: measure_theory.ae_strongly_measurable.comp_measurable -> MeasureTheory.AEStronglyMeasurable.comp_measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {g : α -> β} {γ : Type.{u3}} {mγ : MeasurableSpace.{u3} γ} {mα : MeasurableSpace.{u1} α} {f : γ -> α} {μ : MeasureTheory.Measure.{u3} γ mγ}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 mα g (MeasureTheory.Measure.map.{u3, u1} γ α mα mγ f μ)) -> (Measurable.{u3, u1} γ α mγ mα f) -> (MeasureTheory.AEStronglyMeasurable.{u3, u2} γ β _inst_2 mγ (Function.comp.{succ u3, succ u1, succ u2} γ α β g f) μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {g : α -> β} {γ : Type.{u3}} {mγ : MeasurableSpace.{u3} γ} {mα : MeasurableSpace.{u2} α} {f : γ -> α} {μ : MeasureTheory.Measure.{u3} γ mγ}, (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 mα g (MeasureTheory.Measure.map.{u3, u2} γ α mα mγ f μ)) -> (Measurable.{u3, u2} γ α mγ mα f) -> (MeasureTheory.AEStronglyMeasurable.{u3, u1} γ β _inst_2 mγ (Function.comp.{succ u3, succ u2, succ u1} γ α β g f) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.comp_measurable MeasureTheory.AEStronglyMeasurable.comp_measurableₓ'. -/
theorem comp_measurable {γ : Type _} {mγ : MeasurableSpace γ} {mα : MeasurableSpace α} {f : γ → α}
    {μ : Measure γ} (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : Measurable f) :
    AEStronglyMeasurable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.AEMeasurable
#align measure_theory.ae_strongly_measurable.comp_measurable MeasureTheory.AEStronglyMeasurable.comp_measurable

/- warning: measure_theory.ae_strongly_measurable.comp_quasi_measure_preserving -> MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {g : α -> β} {γ : Type.{u3}} {mγ : MeasurableSpace.{u3} γ} {mα : MeasurableSpace.{u1} α} {f : γ -> α} {μ : MeasureTheory.Measure.{u3} γ mγ} {ν : MeasureTheory.Measure.{u1} α mα}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 mα g ν) -> (MeasureTheory.Measure.QuasiMeasurePreserving.{u3, u1} γ α mα mγ f μ ν) -> (MeasureTheory.AEStronglyMeasurable.{u3, u2} γ β _inst_2 mγ (Function.comp.{succ u3, succ u1, succ u2} γ α β g f) μ)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {g : α -> β} {γ : Type.{u3}} {mγ : MeasurableSpace.{u3} γ} {mα : MeasurableSpace.{u2} α} {f : γ -> α} {μ : MeasureTheory.Measure.{u3} γ mγ} {ν : MeasureTheory.Measure.{u2} α mα}, (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 mα g ν) -> (MeasureTheory.Measure.QuasiMeasurePreserving.{u3, u2} γ α mα mγ f μ ν) -> (MeasureTheory.AEStronglyMeasurable.{u3, u1} γ β _inst_2 mγ (Function.comp.{succ u3, succ u2, succ u1} γ α β g f) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.comp_quasi_measure_preserving MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreservingₓ'. -/
theorem comp_quasiMeasurePreserving {γ : Type _} {mγ : MeasurableSpace γ} {mα : MeasurableSpace α}
    {f : γ → α} {μ : Measure γ} {ν : Measure α} (hg : AEStronglyMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) : AEStronglyMeasurable (g ∘ f) μ :=
  (hg.mono' hf.AbsolutelyContinuous).comp_measurable hf.Measurable
#align measure_theory.ae_strongly_measurable.comp_quasi_measure_preserving MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving

/- warning: measure_theory.ae_strongly_measurable.is_separable_ae_range -> MeasureTheory.AEStronglyMeasurable.isSeparable_ae_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β}, (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (Exists.{succ u2} (Set.{u2} β) (fun (t : Set.{u2} β) => And (TopologicalSpace.IsSeparable.{u2} β _inst_2 t) (Filter.Eventually.{u1} α (fun (x : α) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (f x) t) (MeasureTheory.Measure.ae.{u1} α m μ))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β}, (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ) -> (Exists.{succ u1} (Set.{u1} β) (fun (t : Set.{u1} β) => And (TopologicalSpace.IsSeparable.{u1} β _inst_2 t) (Filter.Eventually.{u2} α (fun (x : α) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (f x) t) (MeasureTheory.Measure.ae.{u2} α m μ))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.is_separable_ae_range MeasureTheory.AEStronglyMeasurable.isSeparable_ae_rangeₓ'. -/
theorem isSeparable_ae_range (hf : AEStronglyMeasurable f μ) :
    ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t :=
  by
  refine' ⟨range (hf.mk f), hf.strongly_measurable_mk.is_separable_range, _⟩
  filter_upwards [hf.ae_eq_mk]with x hx
  simp [hx]
#align measure_theory.ae_strongly_measurable.is_separable_ae_range MeasureTheory.AEStronglyMeasurable.isSeparable_ae_range

#print aestronglyMeasurable_iff_aemeasurable_separable /-
/-- A function is almost everywhere strongly measurable if and only if it is almost everywhere
measurable, and up to a zero measure set its range is contained in a separable set. -/
theorem aestronglyMeasurable_iff_aemeasurable_separable [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] :
    AEStronglyMeasurable f μ ↔ AEMeasurable f μ ∧ ∃ t : Set β, IsSeparable t ∧ ∀ᵐ x ∂μ, f x ∈ t :=
  by
  refine' ⟨fun H => ⟨H.AEMeasurable, H.isSeparable_ae_range⟩, _⟩
  rintro ⟨H, ⟨t, t_sep, ht⟩⟩
  rcases eq_empty_or_nonempty t with (rfl | h₀)
  · simp only [mem_empty_iff_false, eventually_false_iff_eq_bot, ae_eq_bot] at ht
    rw [ht]
    exact ae_strongly_measurable_zero_measure f
  · obtain ⟨g, g_meas, gt, fg⟩ : ∃ g : α → β, Measurable g ∧ range g ⊆ t ∧ f =ᵐ[μ] g :=
      H.exists_ae_eq_range_subset ht h₀
    refine' ⟨g, _, fg⟩
    exact stronglyMeasurable_iff_measurable_separable.2 ⟨g_meas, t_sep.mono GT.gt⟩
#align ae_strongly_measurable_iff_ae_measurable_separable aestronglyMeasurable_iff_aemeasurable_separable
-/

/- warning: measurable_embedding.ae_strongly_measurable_map_iff -> MeasurableEmbedding.aestronglyMeasurable_map_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} β] {γ : Type.{u3}} {mγ : MeasurableSpace.{u3} γ} {mα : MeasurableSpace.{u1} α} {f : γ -> α} {μ : MeasureTheory.Measure.{u3} γ mγ}, (MeasurableEmbedding.{u3, u1} γ α mγ mα f) -> (forall {g : α -> β}, Iff (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 mα g (MeasureTheory.Measure.map.{u3, u1} γ α mα mγ f μ)) (MeasureTheory.AEStronglyMeasurable.{u3, u2} γ β _inst_2 mγ (Function.comp.{succ u3, succ u1, succ u2} γ α β g f) μ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {γ : Type.{u3}} {mγ : MeasurableSpace.{u3} γ} {mα : MeasurableSpace.{u2} α} {f : γ -> α} {μ : MeasureTheory.Measure.{u3} γ mγ}, (MeasurableEmbedding.{u3, u2} γ α mγ mα f) -> (forall {g : α -> β}, Iff (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 mα g (MeasureTheory.Measure.map.{u3, u2} γ α mα mγ f μ)) (MeasureTheory.AEStronglyMeasurable.{u3, u1} γ β _inst_2 mγ (Function.comp.{succ u3, succ u2, succ u1} γ α β g f) μ))
Case conversion may be inaccurate. Consider using '#align measurable_embedding.ae_strongly_measurable_map_iff MeasurableEmbedding.aestronglyMeasurable_map_iffₓ'. -/
theorem MeasurableEmbedding.aestronglyMeasurable_map_iff {γ : Type _} {mγ : MeasurableSpace γ}
    {mα : MeasurableSpace α} {f : γ → α} {μ : Measure γ} (hf : MeasurableEmbedding f) {g : α → β} :
    AEStronglyMeasurable g (Measure.map f μ) ↔ AEStronglyMeasurable (g ∘ f) μ :=
  by
  refine' ⟨fun H => H.comp_measurable hf.measurable, _⟩
  rintro ⟨g₁, hgm₁, heq⟩
  rcases hf.exists_strongly_measurable_extend hgm₁ fun x => ⟨g x⟩ with ⟨g₂, hgm₂, rfl⟩
  exact ⟨g₂, hgm₂, hf.ae_map_iff.2 HEq⟩
#align measurable_embedding.ae_strongly_measurable_map_iff MeasurableEmbedding.aestronglyMeasurable_map_iff

/- warning: embedding.ae_strongly_measurable_comp_iff -> Embedding.aestronglyMeasurable_comp_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u3} γ _inst_3] {g : β -> γ} {f : α -> β}, (Embedding.{u2, u3} β γ _inst_2 _inst_3 g) -> (Iff (MeasureTheory.AEStronglyMeasurable.{u1, u3} α γ _inst_3 m (fun (x : α) => g (f x)) μ) (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u2} γ _inst_3] {g : β -> γ} {f : α -> β}, (Embedding.{u3, u2} β γ _inst_2 _inst_3 g) -> (Iff (MeasureTheory.AEStronglyMeasurable.{u1, u2} α γ _inst_3 m (fun (x : α) => g (f x)) μ) (MeasureTheory.AEStronglyMeasurable.{u1, u3} α β _inst_2 m f μ))
Case conversion may be inaccurate. Consider using '#align embedding.ae_strongly_measurable_comp_iff Embedding.aestronglyMeasurable_comp_iffₓ'. -/
theorem Embedding.aestronglyMeasurable_comp_iff [PseudoMetrizableSpace β] [PseudoMetrizableSpace γ]
    {g : β → γ} {f : α → β} (hg : Embedding g) :
    AEStronglyMeasurable (fun x => g (f x)) μ ↔ AEStronglyMeasurable f μ :=
  by
  letI := pseudo_metrizable_space_pseudo_metric γ
  borelize β γ
  refine'
    ⟨fun H => aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨_, _⟩, fun H =>
      hg.continuous.comp_ae_strongly_measurable H⟩
  · let G : β → range g := cod_restrict g (range g) mem_range_self
    have hG : ClosedEmbedding G :=
      { hg.cod_restrict _ _ with
        closed_range := by
          convert isClosed_univ
          apply eq_univ_of_forall
          rintro ⟨-, ⟨x, rfl⟩⟩
          exact mem_range_self x }
    have : AEMeasurable (G ∘ f) μ := AEMeasurable.subtype_mk H.ae_measurable
    exact hG.measurable_embedding.ae_measurable_comp_iff.1 this
  · rcases(aestronglyMeasurable_iff_aemeasurable_separable.1 H).2 with ⟨t, ht, h't⟩
    exact ⟨g ⁻¹' t, hg.is_separable_preimage ht, h't⟩
#align embedding.ae_strongly_measurable_comp_iff Embedding.aestronglyMeasurable_comp_iff

/- warning: measure_theory.measure_preserving.ae_strongly_measurable_comp_iff -> MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_3 : TopologicalSpace.{u2} γ] {β : Type.{u3}} {f : α -> β} {mα : MeasurableSpace.{u1} α} {μa : MeasureTheory.Measure.{u1} α mα} {mβ : MeasurableSpace.{u3} β} {μb : MeasureTheory.Measure.{u3} β mβ}, (MeasureTheory.MeasurePreserving.{u1, u3} α β mα mβ f μa μb) -> (MeasurableEmbedding.{u1, u3} α β mα mβ f) -> (forall {g : β -> γ}, Iff (MeasureTheory.AEStronglyMeasurable.{u1, u2} α γ _inst_3 mα (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) μa) (MeasureTheory.AEStronglyMeasurable.{u3, u2} β γ _inst_3 mβ g μb))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_3 : TopologicalSpace.{u1} γ] {β : Type.{u3}} {f : α -> β} {mα : MeasurableSpace.{u2} α} {μa : MeasureTheory.Measure.{u2} α mα} {mβ : MeasurableSpace.{u3} β} {μb : MeasureTheory.Measure.{u3} β mβ}, (MeasureTheory.MeasurePreserving.{u2, u3} α β mα mβ f μa μb) -> (MeasurableEmbedding.{u2, u3} α β mα mβ f) -> (forall {g : β -> γ}, Iff (MeasureTheory.AEStronglyMeasurable.{u2, u1} α γ _inst_3 mα (Function.comp.{succ u2, succ u3, succ u1} α β γ g f) μa) (MeasureTheory.AEStronglyMeasurable.{u3, u1} β γ _inst_3 mβ g μb))
Case conversion may be inaccurate. Consider using '#align measure_theory.measure_preserving.ae_strongly_measurable_comp_iff MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iffₓ'. -/
theorem MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff {β : Type _} {f : α → β}
    {mα : MeasurableSpace α} {μa : Measure α} {mβ : MeasurableSpace β} {μb : Measure β}
    (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) {g : β → γ} :
    AEStronglyMeasurable (g ∘ f) μa ↔ AEStronglyMeasurable g μb := by
  rw [← hf.map_eq, h₂.ae_strongly_measurable_map_iff]
#align measure_theory.measure_preserving.ae_strongly_measurable_comp_iff MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff

#print aestronglyMeasurable_of_tendsto_ae /-
/-- An almost everywhere sequential limit of almost everywhere strongly measurable functions is
almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_of_tendsto_ae {ι : Type _} [PseudoMetrizableSpace β] (u : Filter ι)
    [NeBot u] [IsCountablyGenerated u] {f : ι → α → β} {g : α → β}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (lim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) :
    AEStronglyMeasurable g μ := by
  borelize β
  refine' aestronglyMeasurable_iff_aemeasurable_separable.2 ⟨_, _⟩
  · exact aemeasurable_of_tendsto_metrizable_ae _ (fun n => (hf n).AEMeasurable) limUnder
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : ∀ n : ℕ, ∃ t : Set β, IsSeparable t ∧ f (v n) ⁻¹' t ∈ μ.ae := fun n =>
      (aestronglyMeasurable_iff_aemeasurable_separable.1 (hf (v n))).2
    choose t t_sep ht using this
    refine' ⟨closure (⋃ i, t i), (is_separable_Union fun i => t_sep i).closure, _⟩
    filter_upwards [ae_all_iff.2 ht, limUnder]with x hx h'x
    apply mem_closure_of_tendsto (h'x.comp hv)
    apply eventually_of_forall fun n => _
    apply mem_Union_of_mem n
    exact hx n
#align ae_strongly_measurable_of_tendsto_ae aestronglyMeasurable_of_tendsto_ae
-/

#print exists_stronglyMeasurable_limit_of_tendsto_ae /-
/-- If a sequence of almost everywhere strongly measurable functions converges almost everywhere,
one can select a strongly measurable function as the almost everywhere limit. -/
theorem exists_stronglyMeasurable_limit_of_tendsto_ae [PseudoMetrizableSpace β] {f : ℕ → α → β}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (h_ae_tendsto : ∀ᵐ x ∂μ, ∃ l : β, Tendsto (fun n => f n x) atTop (𝓝 l)) :
    ∃ (f_lim : α → β)(hf_lim_meas : StronglyMeasurable f_lim),
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x)) :=
  by
  borelize β
  obtain ⟨g, g_meas, hg⟩ :
    ∃ (g : α → β)(g_meas : Measurable g), ∀ᵐ x ∂μ, tendsto (fun n => f n x) at_top (𝓝 (g x)) :=
    measurable_limit_of_tendsto_metrizable_ae (fun n => (hf n).AEMeasurable) h_ae_tendsto
  have Hg : ae_strongly_measurable g μ := aestronglyMeasurable_of_tendsto_ae _ hf hg
  refine' ⟨Hg.mk g, Hg.strongly_measurable_mk, _⟩
  filter_upwards [hg, Hg.ae_eq_mk]with x hx h'x
  rwa [h'x] at hx
#align exists_strongly_measurable_limit_of_tendsto_ae exists_stronglyMeasurable_limit_of_tendsto_ae
-/

/- warning: measure_theory.ae_strongly_measurable.sum_measure -> MeasureTheory.AEStronglyMeasurable.sum_measure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Countable.{succ u3} ι] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_4 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] {m : MeasurableSpace.{u1} α} {μ : ι -> (MeasureTheory.Measure.{u1} α m)}, (forall (i : ι), MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (μ i)) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.sum.{u1, u3} α ι m μ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Type.{u1}} [_inst_1 : Countable.{succ u1} ι] [_inst_2 : TopologicalSpace.{u3} β] {f : α -> β} [_inst_4 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] {m : MeasurableSpace.{u2} α} {μ : ι -> (MeasureTheory.Measure.{u2} α m)}, (forall (i : ι), MeasureTheory.AEStronglyMeasurable.{u2, u3} α β _inst_2 m f (μ i)) -> (MeasureTheory.AEStronglyMeasurable.{u2, u3} α β _inst_2 m f (MeasureTheory.Measure.sum.{u2, u1} α ι m μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.sum_measure MeasureTheory.AEStronglyMeasurable.sum_measureₓ'. -/
theorem sum_measure [PseudoMetrizableSpace β] {m : MeasurableSpace α} {μ : ι → Measure α}
    (h : ∀ i, AEStronglyMeasurable f (μ i)) : AEStronglyMeasurable f (Measure.sum μ) :=
  by
  borelize β
  refine'
    aestronglyMeasurable_iff_aemeasurable_separable.2
      ⟨AEMeasurable.sum_measure fun i => (h i).AEMeasurable, _⟩
  have A : ∀ i : ι, ∃ t : Set β, IsSeparable t ∧ f ⁻¹' t ∈ (μ i).ae := fun i =>
    (aestronglyMeasurable_iff_aemeasurable_separable.1 (h i)).2
  choose t t_sep ht using A
  refine' ⟨⋃ i, t i, is_separable_Union t_sep, _⟩
  simp only [measure.ae_sum_eq, mem_Union, eventually_supr]
  intro i
  filter_upwards [ht i]with x hx
  exact ⟨i, hx⟩
#align measure_theory.ae_strongly_measurable.sum_measure MeasureTheory.AEStronglyMeasurable.sum_measure

/- warning: ae_strongly_measurable_sum_measure_iff -> aestronglyMeasurable_sum_measure_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Countable.{succ u3} ι] [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_4 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] {m : MeasurableSpace.{u1} α} {μ : ι -> (MeasureTheory.Measure.{u1} α m)}, Iff (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.sum.{u1, u3} α ι m μ)) (forall (i : ι), MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (μ i))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Type.{u1}} [_inst_1 : Countable.{succ u1} ι] [_inst_2 : TopologicalSpace.{u3} β] {f : α -> β} [_inst_4 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] {m : MeasurableSpace.{u2} α} {μ : ι -> (MeasureTheory.Measure.{u2} α m)}, Iff (MeasureTheory.AEStronglyMeasurable.{u2, u3} α β _inst_2 m f (MeasureTheory.Measure.sum.{u2, u1} α ι m μ)) (forall (i : ι), MeasureTheory.AEStronglyMeasurable.{u2, u3} α β _inst_2 m f (μ i))
Case conversion may be inaccurate. Consider using '#align ae_strongly_measurable_sum_measure_iff aestronglyMeasurable_sum_measure_iffₓ'. -/
@[simp]
theorem aestronglyMeasurable_sum_measure_iff [PseudoMetrizableSpace β] {m : MeasurableSpace α}
    {μ : ι → Measure α} : AEStronglyMeasurable f (Sum μ) ↔ ∀ i, AEStronglyMeasurable f (μ i) :=
  ⟨fun h i => h.mono_measure (Measure.le_sum _ _), sum_measure⟩
#align ae_strongly_measurable_sum_measure_iff aestronglyMeasurable_sum_measure_iff

#print aestronglyMeasurable_add_measure_iff /-
@[simp]
theorem aestronglyMeasurable_add_measure_iff [PseudoMetrizableSpace β] {ν : Measure α} :
    AEStronglyMeasurable f (μ + ν) ↔ AEStronglyMeasurable f μ ∧ AEStronglyMeasurable f ν :=
  by
  rw [← sum_cond, aestronglyMeasurable_sum_measure_iff, Bool.forall_bool, and_comm]
  rfl
#align ae_strongly_measurable_add_measure_iff aestronglyMeasurable_add_measure_iff
-/

#print MeasureTheory.AEStronglyMeasurable.add_measure /-
theorem add_measure [PseudoMetrizableSpace β] {ν : Measure α} {f : α → β}
    (hμ : AEStronglyMeasurable f μ) (hν : AEStronglyMeasurable f ν) :
    AEStronglyMeasurable f (μ + ν) :=
  aestronglyMeasurable_add_measure_iff.2 ⟨hμ, hν⟩
#align measure_theory.ae_strongly_measurable.add_measure MeasureTheory.AEStronglyMeasurable.add_measure
-/

/- warning: measure_theory.ae_strongly_measurable.Union -> MeasureTheory.AEStronglyMeasurable.iUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Countable.{succ u3} ι] {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_4 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] {s : ι -> (Set.{u1} α)}, (forall (i : ι), MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u1} α m μ (s i))) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u3} α ι (fun (i : ι) => s i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Type.{u1}} [_inst_1 : Countable.{succ u1} ι] {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u3} β] {f : α -> β} [_inst_4 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] {s : ι -> (Set.{u2} α)}, (forall (i : ι), MeasureTheory.AEStronglyMeasurable.{u2, u3} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u2} α m μ (s i))) -> (MeasureTheory.AEStronglyMeasurable.{u2, u3} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u2} α m μ (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => s i))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.Union MeasureTheory.AEStronglyMeasurable.iUnionₓ'. -/
protected theorem iUnion [PseudoMetrizableSpace β] {s : ι → Set α}
    (h : ∀ i, AEStronglyMeasurable f (μ.restrict (s i))) :
    AEStronglyMeasurable f (μ.restrict (⋃ i, s i)) :=
  (sum_measure h).mono_measure <| restrict_iUnion_le
#align measure_theory.ae_strongly_measurable.Union MeasureTheory.AEStronglyMeasurable.iUnion

/- warning: ae_strongly_measurable_Union_iff -> aestronglyMeasurable_iUnion_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_1 : Countable.{succ u3} ι] {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_4 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] {s : ι -> (Set.{u1} α)}, Iff (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u1} α m μ (Set.iUnion.{u1, succ u3} α ι (fun (i : ι) => s i)))) (forall (i : ι), MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u1} α m μ (s i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Type.{u1}} [_inst_1 : Countable.{succ u1} ι] {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u3} β] {f : α -> β} [_inst_4 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] {s : ι -> (Set.{u2} α)}, Iff (MeasureTheory.AEStronglyMeasurable.{u2, u3} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u2} α m μ (Set.iUnion.{u2, succ u1} α ι (fun (i : ι) => s i)))) (forall (i : ι), MeasureTheory.AEStronglyMeasurable.{u2, u3} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u2} α m μ (s i)))
Case conversion may be inaccurate. Consider using '#align ae_strongly_measurable_Union_iff aestronglyMeasurable_iUnion_iffₓ'. -/
@[simp]
theorem aestronglyMeasurable_iUnion_iff [PseudoMetrizableSpace β] {s : ι → Set α} :
    AEStronglyMeasurable f (μ.restrict (⋃ i, s i)) ↔
      ∀ i, AEStronglyMeasurable f (μ.restrict (s i)) :=
  ⟨fun h i => h.mono_measure <| restrict_mono (subset_iUnion _ _) le_rfl,
    AEStronglyMeasurable.iUnion⟩
#align ae_strongly_measurable_Union_iff aestronglyMeasurable_iUnion_iff

#print aestronglyMeasurable_union_iff /-
@[simp]
theorem aestronglyMeasurable_union_iff [PseudoMetrizableSpace β] {s t : Set α} :
    AEStronglyMeasurable f (μ.restrict (s ∪ t)) ↔
      AEStronglyMeasurable f (μ.restrict s) ∧ AEStronglyMeasurable f (μ.restrict t) :=
  by simp only [union_eq_Union, aestronglyMeasurable_iUnion_iff, Bool.forall_bool, cond, and_comm]
#align ae_strongly_measurable_union_iff aestronglyMeasurable_union_iff
-/

/- warning: measure_theory.ae_strongly_measurable.ae_strongly_measurable_uIoc_iff -> MeasureTheory.AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] [_inst_4 : LinearOrder.{u1} α] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] {f : α -> β} {a : α} {b : α}, Iff (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u1} α m μ (Set.uIoc.{u1} α _inst_4 a b))) (And (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u1} α m μ (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_4)))) a b))) (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u1} α m μ (Set.Ioc.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_4)))) b a))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] [_inst_4 : LinearOrder.{u2} α] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u1} β _inst_2] {f : α -> β} {a : α} {b : α}, Iff (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u2} α m μ (Set.uIoc.{u2} α _inst_4 a b))) (And (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u2} α m μ (Set.Ioc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_4))))) a b))) (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f (MeasureTheory.Measure.restrict.{u2} α m μ (Set.Ioc.{u2} α (PartialOrder.toPreorder.{u2} α (SemilatticeInf.toPartialOrder.{u2} α (Lattice.toSemilatticeInf.{u2} α (DistribLattice.toLattice.{u2} α (instDistribLattice.{u2} α _inst_4))))) b a))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.ae_strongly_measurable_uIoc_iff MeasureTheory.AEStronglyMeasurable.aestronglyMeasurable_uIoc_iffₓ'. -/
theorem aestronglyMeasurable_uIoc_iff [LinearOrder α] [PseudoMetrizableSpace β] {f : α → β}
    {a b : α} :
    AEStronglyMeasurable f (μ.restrict <| uIoc a b) ↔
      AEStronglyMeasurable f (μ.restrict <| Ioc a b) ∧
        AEStronglyMeasurable f (μ.restrict <| Ioc b a) :=
  by rw [uIoc_eq_union, aestronglyMeasurable_union_iff]
#align measure_theory.ae_strongly_measurable.ae_strongly_measurable_uIoc_iff MeasureTheory.AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff

/- warning: measure_theory.ae_strongly_measurable.smul_measure -> MeasureTheory.AEStronglyMeasurable.smul_measure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {R : Type.{u3}} [_inst_4 : Monoid.{u3} R] [_inst_5 : DistribMulAction.{u3, 0} R ENNReal _inst_4 (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))] [_inst_6 : IsScalarTower.{u3, 0, 0} R ENNReal ENNReal (SMulZeroClass.toHasSmul.{u3, 0} R ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))) (DistribSMul.toSmulZeroClass.{u3, 0} R ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))) (DistribMulAction.toDistribSMul.{u3, 0} R ENNReal _inst_4 (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)) _inst_5))) (Mul.toSMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (SMulZeroClass.toHasSmul.{u3, 0} R ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))) (DistribSMul.toSmulZeroClass.{u3, 0} R ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))) (DistribMulAction.toDistribSMul.{u3, 0} R ENNReal _inst_4 (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)) _inst_5)))], (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ) -> (forall (c : R), MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f (SMul.smul.{u3, u1} R (MeasureTheory.Measure.{u1} α m) (MeasureTheory.Measure.instSMul.{u1, u3} α R (SMulZeroClass.toHasSmul.{u3, 0} R ENNReal (AddZeroClass.toHasZero.{0} ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))) (DistribSMul.toSmulZeroClass.{u3, 0} R ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))) (DistribMulAction.toDistribSMul.{u3, 0} R ENNReal _inst_4 (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)) _inst_5))) _inst_6 m) c μ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {R : Type.{u3}} [_inst_4 : Monoid.{u3} R] [_inst_5 : DistribMulAction.{u3, 0} R ENNReal _inst_4 (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instENNRealAddCommMonoidWithOne))] [_inst_6 : IsScalarTower.{u3, 0, 0} R ENNReal ENNReal (SMulZeroClass.toSMul.{u3, 0} R ENNReal instENNRealZero (DistribSMul.toSMulZeroClass.{u3, 0} R ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instENNRealAddCommMonoidWithOne))) (DistribMulAction.toDistribSMul.{u3, 0} R ENNReal _inst_4 (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instENNRealAddCommMonoidWithOne)) _inst_5))) (Algebra.toSMul.{0, 0} ENNReal ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal) (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (Algebra.id.{0} ENNReal (CanonicallyOrderedCommSemiring.toCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))) (SMulZeroClass.toSMul.{u3, 0} R ENNReal instENNRealZero (DistribSMul.toSMulZeroClass.{u3, 0} R ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instENNRealAddCommMonoidWithOne))) (DistribMulAction.toDistribSMul.{u3, 0} R ENNReal _inst_4 (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instENNRealAddCommMonoidWithOne)) _inst_5)))], (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ) -> (forall (c : R), MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f (HSMul.hSMul.{u3, u2, u2} R (MeasureTheory.Measure.{u2} α m) (MeasureTheory.Measure.{u2} α m) (instHSMul.{u3, u2} R (MeasureTheory.Measure.{u2} α m) (MeasureTheory.Measure.instSMul.{u2, u3} α R (SMulZeroClass.toSMul.{u3, 0} R ENNReal instENNRealZero (DistribSMul.toSMulZeroClass.{u3, 0} R ENNReal (AddMonoid.toAddZeroClass.{0} ENNReal (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instENNRealAddCommMonoidWithOne))) (DistribMulAction.toDistribSMul.{u3, 0} R ENNReal _inst_4 (AddMonoidWithOne.toAddMonoid.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal instENNRealAddCommMonoidWithOne)) _inst_5))) _inst_6 m)) c μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.smul_measure MeasureTheory.AEStronglyMeasurable.smul_measureₓ'. -/
theorem smul_measure {R : Type _} [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : AEStronglyMeasurable f μ) (c : R) : AEStronglyMeasurable f (c • μ) :=
  ⟨h.mk f, h.stronglyMeasurable_mk, ae_smul_measure h.ae_eq_mk c⟩
#align measure_theory.ae_strongly_measurable.smul_measure MeasureTheory.AEStronglyMeasurable.smul_measure

section NormedSpace

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/- warning: ae_strongly_measurable_smul_const_iff -> aestronglyMeasurable_smul_const_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {𝕜 : Type.{u2}} [_inst_4 : NontriviallyNormedField.{u2} 𝕜] [_inst_5 : CompleteSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))] {E : Type.{u3}} [_inst_6 : NormedAddCommGroup.{u3} E] [_inst_7 : NormedSpace.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_6)] {f : α -> 𝕜} {c : E}, (Ne.{succ u3} E c (OfNat.ofNat.{u3} E 0 (OfNat.mk.{u3} E 0 (Zero.zero.{u3} E (AddZeroClass.toHasZero.{u3} E (AddMonoid.toAddZeroClass.{u3} E (SubNegMonoid.toAddMonoid.{u3} E (AddGroup.toSubNegMonoid.{u3} E (NormedAddGroup.toAddGroup.{u3} E (NormedAddCommGroup.toNormedAddGroup.{u3} E _inst_6)))))))))) -> (Iff (MeasureTheory.AEStronglyMeasurable.{u1, u3} α E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_6)))) m (fun (x : α) => SMul.smul.{u2, u3} 𝕜 E (SMulZeroClass.toHasSmul.{u2, u3} 𝕜 E (AddZeroClass.toHasZero.{u3} E (AddMonoid.toAddZeroClass.{u3} E (AddCommMonoid.toAddMonoid.{u3} E (AddCommGroup.toAddCommMonoid.{u3} E (SeminormedAddCommGroup.toAddCommGroup.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_6)))))) (SMulWithZero.toSmulZeroClass.{u2, u3} 𝕜 E (MulZeroClass.toHasZero.{u2} 𝕜 (MulZeroOneClass.toMulZeroClass.{u2} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u3} E (AddMonoid.toAddZeroClass.{u3} E (AddCommMonoid.toAddMonoid.{u3} E (AddCommGroup.toAddCommMonoid.{u3} E (SeminormedAddCommGroup.toAddCommGroup.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_6)))))) (MulActionWithZero.toSMulWithZero.{u2, u3} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u3} E (AddMonoid.toAddZeroClass.{u3} E (AddCommMonoid.toAddMonoid.{u3} E (AddCommGroup.toAddCommMonoid.{u3} E (SeminormedAddCommGroup.toAddCommGroup.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_6)))))) (Module.toMulActionWithZero.{u2, u3} 𝕜 E (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} E (SeminormedAddCommGroup.toAddCommGroup.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_6))) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_6) _inst_7))))) (f x) c) μ) (MeasureTheory.AEStronglyMeasurable.{u1, u2} α 𝕜 (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) m f μ))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {𝕜 : Type.{u1}} [_inst_4 : NontriviallyNormedField.{u1} 𝕜] [_inst_5 : CompleteSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_4))))))] {E : Type.{u3}} [_inst_6 : NormedAddCommGroup.{u3} E] [_inst_7 : NormedSpace.{u1, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_6)] {f : α -> 𝕜} {c : E}, (Ne.{succ u3} E c (OfNat.ofNat.{u3} E 0 (Zero.toOfNat0.{u3} E (NegZeroClass.toZero.{u3} E (SubNegZeroMonoid.toNegZeroClass.{u3} E (SubtractionMonoid.toSubNegZeroMonoid.{u3} E (SubtractionCommMonoid.toSubtractionMonoid.{u3} E (AddCommGroup.toDivisionAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_6))))))))) -> (Iff (MeasureTheory.AEStronglyMeasurable.{u2, u3} α E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_6)))) m (fun (x : α) => HSMul.hSMul.{u1, u3, u3} 𝕜 E E (instHSMul.{u1, u3} 𝕜 E (SMulZeroClass.toSMul.{u1, u3} 𝕜 E (NegZeroClass.toZero.{u3} E (SubNegZeroMonoid.toNegZeroClass.{u3} E (SubtractionMonoid.toSubNegZeroMonoid.{u3} E (SubtractionCommMonoid.toSubtractionMonoid.{u3} E (AddCommGroup.toDivisionAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_6)))))) (SMulWithZero.toSMulZeroClass.{u1, u3} 𝕜 E (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} E (SubNegZeroMonoid.toNegZeroClass.{u3} E (SubtractionMonoid.toSubNegZeroMonoid.{u3} E (SubtractionCommMonoid.toSubtractionMonoid.{u3} E (AddCommGroup.toDivisionAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_6)))))) (MulActionWithZero.toSMulWithZero.{u1, u3} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} E (SubNegZeroMonoid.toNegZeroClass.{u3} E (SubtractionMonoid.toSubNegZeroMonoid.{u3} E (SubtractionCommMonoid.toSubtractionMonoid.{u3} E (AddCommGroup.toDivisionAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_6)))))) (Module.toMulActionWithZero.{u1, u3} 𝕜 E (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_6)) (NormedSpace.toModule.{u1, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_6) _inst_7)))))) (f x) c) μ) (MeasureTheory.AEStronglyMeasurable.{u2, u1} α 𝕜 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_4))))))) m f μ))
Case conversion may be inaccurate. Consider using '#align ae_strongly_measurable_smul_const_iff aestronglyMeasurable_smul_const_iffₓ'. -/
theorem aestronglyMeasurable_smul_const_iff {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
    AEStronglyMeasurable (fun x => f x • c) μ ↔ AEStronglyMeasurable f μ :=
  (closedEmbedding_smul_left hc).toEmbedding.aestronglyMeasurable_comp_iff
#align ae_strongly_measurable_smul_const_iff aestronglyMeasurable_smul_const_iff

end NormedSpace

section MulAction

variable {M G G₀ : Type _}

variable [Monoid M] [MulAction M β] [ContinuousConstSMul M β]

variable [Group G] [MulAction G β] [ContinuousConstSMul G β]

variable [GroupWithZero G₀] [MulAction G₀ β] [ContinuousConstSMul G₀ β]

/- warning: ae_strongly_measurable_const_smul_iff -> aestronglyMeasurable_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {G : Type.{u3}} [_inst_7 : Group.{u3} G] [_inst_8 : MulAction.{u3, u2} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_7))] [_inst_9 : ContinuousConstSMul.{u3, u2} G β _inst_2 (MulAction.toHasSmul.{u3, u2} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_7)) _inst_8)] (c : G), Iff (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (fun (x : α) => SMul.smul.{u3, u2} G β (MulAction.toHasSmul.{u3, u2} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_7)) _inst_8) c (f x)) μ) (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {m : MeasurableSpace.{u3} α} {μ : MeasureTheory.Measure.{u3} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {G : Type.{u1}} [_inst_7 : Group.{u1} G] [_inst_8 : MulAction.{u1, u2} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_7))] [_inst_9 : ContinuousConstSMul.{u1, u2} G β _inst_2 (MulAction.toSMul.{u1, u2} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_7)) _inst_8)] (c : G), Iff (MeasureTheory.AEStronglyMeasurable.{u3, u2} α β _inst_2 m (fun (x : α) => HSMul.hSMul.{u1, u2, u2} G β β (instHSMul.{u1, u2} G β (MulAction.toSMul.{u1, u2} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_7)) _inst_8)) c (f x)) μ) (MeasureTheory.AEStronglyMeasurable.{u3, u2} α β _inst_2 m f μ)
Case conversion may be inaccurate. Consider using '#align ae_strongly_measurable_const_smul_iff aestronglyMeasurable_const_smul_iffₓ'. -/
theorem aestronglyMeasurable_const_smul_iff (c : G) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align ae_strongly_measurable_const_smul_iff aestronglyMeasurable_const_smul_iff

theorem IsUnit.aEStronglyMeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aestronglyMeasurable_const_smul_iff u
#align is_unit.ae_strongly_measurable_const_smul_iff IsUnit.aEStronglyMeasurable_const_smul_iff

/- warning: ae_strongly_measurable_const_smul_iff₀ -> aestronglyMeasurable_const_smul_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {G₀ : Type.{u3}} [_inst_10 : GroupWithZero.{u3} G₀] [_inst_11 : MulAction.{u3, u2} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_10))] [_inst_12 : ContinuousConstSMul.{u3, u2} G₀ β _inst_2 (MulAction.toHasSmul.{u3, u2} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_10)) _inst_11)] {c : G₀}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_10)))))))) -> (Iff (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m (fun (x : α) => SMul.smul.{u3, u2} G₀ β (MulAction.toHasSmul.{u3, u2} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_10)) _inst_11) c (f x)) μ) (MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 m f μ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {G₀ : Type.{u3}} [_inst_10 : GroupWithZero.{u3} G₀] [_inst_11 : MulAction.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_10))] [_inst_12 : ContinuousConstSMul.{u3, u1} G₀ β _inst_2 (MulAction.toSMul.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_10)) _inst_11)] {c : G₀}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (Zero.toOfNat0.{u3} G₀ (MonoidWithZero.toZero.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_10))))) -> (Iff (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m (fun (x : α) => HSMul.hSMul.{u3, u1, u1} G₀ β β (instHSMul.{u3, u1} G₀ β (MulAction.toSMul.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_10)) _inst_11)) c (f x)) μ) (MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 m f μ))
Case conversion may be inaccurate. Consider using '#align ae_strongly_measurable_const_smul_iff₀ aestronglyMeasurable_const_smul_iff₀ₓ'. -/
theorem aestronglyMeasurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    AEStronglyMeasurable (fun x => c • f x) μ ↔ AEStronglyMeasurable f μ :=
  (IsUnit.mk0 _ hc).aestronglyMeasurable_const_smul_iff
#align ae_strongly_measurable_const_smul_iff₀ aestronglyMeasurable_const_smul_iff₀

end MulAction

section ContinuousLinearMapNontriviallyNormedField

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/- warning: strongly_measurable.apply_continuous_linear_map -> StronglyMeasurable.apply_continuousLinearMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {𝕜 : Type.{u2}} [_inst_4 : NontriviallyNormedField.{u2} 𝕜] {E : Type.{u3}} [_inst_5 : NormedAddCommGroup.{u3} E] [_inst_6 : NormedSpace.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)] {F : Type.{u4}} [_inst_7 : NormedAddCommGroup.{u4} F] [_inst_8 : NormedSpace.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)] {m : MeasurableSpace.{u1} α} {φ : α -> (ContinuousLinearMap.{u2, u2, u4, u3} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6))}, (MeasureTheory.StronglyMeasurable.{u1, max u4 u3} α (ContinuousLinearMap.{u2, u2, u4, u3} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6)) (ContinuousLinearMap.topologicalSpace.{u2, u2, u4, u3} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F E (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6) (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5))) m φ) -> (forall (v : F), MeasureTheory.StronglyMeasurable.{u1, u3} α E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) m (fun (a : α) => coeFn.{max (succ u4) (succ u3), max (succ u4) (succ u3)} (ContinuousLinearMap.{u2, u2, u4, u3} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6)) (fun (_x : ContinuousLinearMap.{u2, u2, u4, u3} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6)) => F -> E) (ContinuousLinearMap.toFun.{u2, u2, u4, u3} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6)) (φ a) v))
but is expected to have type
  forall {α : Type.{u4}} {𝕜 : Type.{u3}} [_inst_4 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u1}} [_inst_5 : NormedAddCommGroup.{u1} E] [_inst_6 : NormedSpace.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)] {F : Type.{u2}} [_inst_7 : NormedAddCommGroup.{u2} F] [_inst_8 : NormedSpace.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)] {m : MeasurableSpace.{u4} α} {φ : α -> (ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_5)) (NormedSpace.toModule.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6))}, (MeasureTheory.StronglyMeasurable.{u4, max u1 u2} α (ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_5)) (NormedSpace.toModule.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6)) (ContinuousLinearMap.topologicalSpace.{u3, u3, u2, u1} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))))) F E (SeminormedAddCommGroup.toAddCommGroup.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (SeminormedAddCommGroup.toAddCommGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)) (NormedSpace.toModule.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6) (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5))) m φ) -> (forall (v : F), MeasureTheory.StronglyMeasurable.{u4, u1} α ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => E) v) (UniformSpace.toTopologicalSpace.{u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => E) v) (PseudoMetricSpace.toUniformSpace.{u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => E) v) (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => E) v) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => E) v) _inst_5)))) m (fun (a : α) => FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_5)) (NormedSpace.toModule.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6)) F (fun (_x : F) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => E) _x) (ContinuousMapClass.toFunLike.{max u1 u2, u2, u1} (ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_5)) (NormedSpace.toModule.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6)) F E (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)))) (ContinuousSemilinearMapClass.toContinuousMapClass.{max u1 u2, u3, u3, u2, u1} (ContinuousLinearMap.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_5)) (NormedSpace.toModule.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6)) 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_5)) (NormedSpace.toModule.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6) (ContinuousLinearMap.continuousSemilinearMapClass.{u3, u3, u2, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_5)) (NormedSpace.toModule.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u3, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_5) _inst_6)))) (φ a) v))
Case conversion may be inaccurate. Consider using '#align strongly_measurable.apply_continuous_linear_map StronglyMeasurable.apply_continuousLinearMapₓ'. -/
theorem StronglyMeasurable.apply_continuousLinearMap {m : MeasurableSpace α} {φ : α → F →L[𝕜] E}
    (hφ : StronglyMeasurable φ) (v : F) : StronglyMeasurable fun a => φ a v :=
  (ContinuousLinearMap.apply 𝕜 E v).Continuous.comp_stronglyMeasurable hφ
#align strongly_measurable.apply_continuous_linear_map StronglyMeasurable.apply_continuousLinearMap

/- warning: measure_theory.ae_strongly_measurable.apply_continuous_linear_map -> MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {𝕜 : Type.{u2}} [_inst_4 : NontriviallyNormedField.{u2} 𝕜] {E : Type.{u3}} [_inst_5 : NormedAddCommGroup.{u3} E] [_inst_6 : NormedSpace.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)] {F : Type.{u4}} [_inst_7 : NormedAddCommGroup.{u4} F] [_inst_8 : NormedSpace.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)] {φ : α -> (ContinuousLinearMap.{u2, u2, u4, u3} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6))}, (MeasureTheory.AEStronglyMeasurable.{u1, max u4 u3} α (ContinuousLinearMap.{u2, u2, u4, u3} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6)) (ContinuousLinearMap.topologicalSpace.{u2, u2, u4, u3} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F E (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6) (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5))) m φ μ) -> (forall (v : F), MeasureTheory.AEStronglyMeasurable.{u1, u3} α E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) m (fun (a : α) => coeFn.{max (succ u4) (succ u3), max (succ u4) (succ u3)} (ContinuousLinearMap.{u2, u2, u4, u3} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6)) (fun (_x : ContinuousLinearMap.{u2, u2, u4, u3} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6)) => F -> E) (ContinuousLinearMap.toFun.{u2, u2, u4, u3} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6)) (φ a) v) μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {𝕜 : Type.{u4}} [_inst_4 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u2}} [_inst_5 : NormedAddCommGroup.{u2} E] [_inst_6 : NormedSpace.{u4, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)] {F : Type.{u3}} [_inst_7 : NormedAddCommGroup.{u3} F] [_inst_8 : NormedSpace.{u4, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7)] {φ : α -> (ContinuousLinearMap.{u4, u4, u3, u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (RingHom.id.{u4} 𝕜 (Semiring.toNonAssocSemiring.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_5)) (NormedSpace.toModule.{u4, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7) _inst_8) (NormedSpace.toModule.{u4, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6))}, (MeasureTheory.AEStronglyMeasurable.{u1, max u2 u3} α (ContinuousLinearMap.{u4, u4, u3, u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (RingHom.id.{u4} 𝕜 (Semiring.toNonAssocSemiring.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_5)) (NormedSpace.toModule.{u4, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7) _inst_8) (NormedSpace.toModule.{u4, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6)) (ContinuousLinearMap.topologicalSpace.{u4, u4, u3, u2} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (RingHom.id.{u4} 𝕜 (Semiring.toNonAssocSemiring.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))))) F E (SeminormedAddCommGroup.toAddCommGroup.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7)) (NormedSpace.toModule.{u4, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7) _inst_8) (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)) (NormedSpace.toModule.{u4, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5))) m φ μ) -> (forall (v : F), MeasureTheory.AEStronglyMeasurable.{u1, u2} α ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => E) v) (UniformSpace.toTopologicalSpace.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => E) v) (PseudoMetricSpace.toUniformSpace.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => E) v) (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => E) v) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => E) v) _inst_5)))) m (fun (a : α) => FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (ContinuousLinearMap.{u4, u4, u3, u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (RingHom.id.{u4} 𝕜 (Semiring.toNonAssocSemiring.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_5)) (NormedSpace.toModule.{u4, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7) _inst_8) (NormedSpace.toModule.{u4, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6)) F (fun (_x : F) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => E) _x) (ContinuousMapClass.toFunLike.{max u2 u3, u3, u2} (ContinuousLinearMap.{u4, u4, u3, u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (RingHom.id.{u4} 𝕜 (Semiring.toNonAssocSemiring.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_5)) (NormedSpace.toModule.{u4, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7) _inst_8) (NormedSpace.toModule.{u4, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6)) F E (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)))) (ContinuousSemilinearMapClass.toContinuousMapClass.{max u2 u3, u4, u4, u3, u2} (ContinuousLinearMap.{u4, u4, u3, u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (RingHom.id.{u4} 𝕜 (Semiring.toNonAssocSemiring.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_5)) (NormedSpace.toModule.{u4, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7) _inst_8) (NormedSpace.toModule.{u4, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6)) 𝕜 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (RingHom.id.{u4} 𝕜 (Semiring.toNonAssocSemiring.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_5)) (NormedSpace.toModule.{u4, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7) _inst_8) (NormedSpace.toModule.{u4, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6) (ContinuousLinearMap.continuousSemilinearMapClass.{u4, u4, u3, u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))) (RingHom.id.{u4} 𝕜 (Semiring.toNonAssocSemiring.{u4} 𝕜 (DivisionSemiring.toSemiring.{u4} 𝕜 (Semifield.toDivisionSemiring.{u4} 𝕜 (Field.toSemifield.{u4} 𝕜 (NormedField.toField.{u4} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_7)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_5)) (NormedSpace.toModule.{u4, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_7) _inst_8) (NormedSpace.toModule.{u4, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_5) _inst_6)))) (φ a) v) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_strongly_measurable.apply_continuous_linear_map MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMapₓ'. -/
theorem apply_continuousLinearMap {φ : α → F →L[𝕜] E} (hφ : AEStronglyMeasurable φ μ) (v : F) :
    AEStronglyMeasurable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply 𝕜 E v).Continuous.comp_aestronglyMeasurable hφ
#align measure_theory.ae_strongly_measurable.apply_continuous_linear_map MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap

/- warning: continuous_linear_map.ae_strongly_measurable_comp₂ -> ContinuousLinearMap.aestronglyMeasurable_comp₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {𝕜 : Type.{u2}} [_inst_4 : NontriviallyNormedField.{u2} 𝕜] {E : Type.{u3}} [_inst_5 : NormedAddCommGroup.{u3} E] [_inst_6 : NormedSpace.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)] {F : Type.{u4}} [_inst_7 : NormedAddCommGroup.{u4} F] [_inst_8 : NormedSpace.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)] {G : Type.{u5}} [_inst_9 : NormedAddCommGroup.{u5} G] [_inst_10 : NormedSpace.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)] (L : ContinuousLinearMap.{u2, u2, u3, max u4 u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (ContinuousLinearMap.{u2, u2, u4, u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10)) (ContinuousLinearMap.topologicalSpace.{u2, u2, u4, u5} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F G (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))) (ContinuousLinearMap.addCommMonoid.{u2, u2, u4, u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (LipschitzAdd.continuousAdd.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)) (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (NormedAddGroup.toAddGroup.{u5} G (NormedAddCommGroup.toNormedAddGroup.{u5} G _inst_9)))) (SeminormedAddCommGroup.to_lipschitzAdd.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6) (ContinuousLinearMap.module.{u2, u2, u2, u4, u5} 𝕜 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (smulCommClass_self.{u2, u5} 𝕜 G (CommRing.toCommMonoid.{u2} 𝕜 (SeminormedCommRing.toCommRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (MulActionWithZero.toMulAction.{u2, u5} 𝕜 G (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (SeminormedAddCommGroup.toAddCommGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))))) (Module.toMulActionWithZero.{u2, u5} 𝕜 G (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u5} G (SeminormedAddCommGroup.toAddCommGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10)))) (ContinuousSMul.continuousConstSMul.{u2, u5} 𝕜 G (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (SMulZeroClass.toHasSmul.{u2, u5} 𝕜 G (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (SMulWithZero.toSmulZeroClass.{u2, u5} 𝕜 G (MulZeroClass.toHasZero.{u2} 𝕜 (MulZeroOneClass.toMulZeroClass.{u2} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (MulActionWithZero.toSMulWithZero.{u2, u5} 𝕜 G (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (Module.toMulActionWithZero.{u2, u5} 𝕜 G (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))))) (BoundedSMul.continuousSMul.{u2, u5} 𝕜 G (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)) (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (SeminormedAddGroup.toAddGroup.{u5} G (SeminormedAddCommGroup.toSeminormedAddGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))))))) (SMulZeroClass.toHasSmul.{u2, u5} 𝕜 G (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (SMulWithZero.toSmulZeroClass.{u2, u5} 𝕜 G (MulZeroClass.toHasZero.{u2} 𝕜 (MulZeroOneClass.toMulZeroClass.{u2} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (MulActionWithZero.toSMulWithZero.{u2, u5} 𝕜 G (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (Module.toMulActionWithZero.{u2, u5} 𝕜 G (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))))) (NormedSpace.boundedSMul.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) (LipschitzAdd.continuousAdd.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)) (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (NormedAddGroup.toAddGroup.{u5} G (NormedAddCommGroup.toNormedAddGroup.{u5} G _inst_9)))) (SeminormedAddCommGroup.to_lipschitzAdd.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))))) {f : α -> E} {g : α -> F}, (MeasureTheory.AEStronglyMeasurable.{u1, u3} α E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u4} α F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) m g μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u5} α G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) m (fun (x : α) => coeFn.{max (succ u4) (succ u5), max (succ u4) (succ u5)} (ContinuousLinearMap.{u2, u2, u4, u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10)) (fun (_x : ContinuousLinearMap.{u2, u2, u4, u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10)) => F -> G) (ContinuousLinearMap.toFun.{u2, u2, u4, u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10)) (coeFn.{max (succ u3) (succ (max u4 u5)), max (succ u3) (succ (max u4 u5))} (ContinuousLinearMap.{u2, u2, u3, max u4 u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (ContinuousLinearMap.{u2, u2, u4, u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10)) (ContinuousLinearMap.topologicalSpace.{u2, u2, u4, u5} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F G (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))) (ContinuousLinearMap.addCommMonoid.{u2, u2, u4, u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (LipschitzAdd.continuousAdd.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)) (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (NormedAddGroup.toAddGroup.{u5} G (NormedAddCommGroup.toNormedAddGroup.{u5} G _inst_9)))) (SeminormedAddCommGroup.to_lipschitzAdd.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6) (ContinuousLinearMap.module.{u2, u2, u2, u4, u5} 𝕜 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (smulCommClass_self.{u2, u5} 𝕜 G (CommRing.toCommMonoid.{u2} 𝕜 (SeminormedCommRing.toCommRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (MulActionWithZero.toMulAction.{u2, u5} 𝕜 G (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (SeminormedAddCommGroup.toAddCommGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))))) (Module.toMulActionWithZero.{u2, u5} 𝕜 G (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u5} G (SeminormedAddCommGroup.toAddCommGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10)))) (ContinuousSMul.continuousConstSMul.{u2, u5} 𝕜 G (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (SMulZeroClass.toHasSmul.{u2, u5} 𝕜 G (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (SMulWithZero.toSmulZeroClass.{u2, u5} 𝕜 G (MulZeroClass.toHasZero.{u2} 𝕜 (MulZeroOneClass.toMulZeroClass.{u2} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (MulActionWithZero.toSMulWithZero.{u2, u5} 𝕜 G (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (Module.toMulActionWithZero.{u2, u5} 𝕜 G (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))))) (BoundedSMul.continuousSMul.{u2, u5} 𝕜 G (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)) (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (SeminormedAddGroup.toAddGroup.{u5} G (SeminormedAddCommGroup.toSeminormedAddGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))))))) (SMulZeroClass.toHasSmul.{u2, u5} 𝕜 G (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (SMulWithZero.toSmulZeroClass.{u2, u5} 𝕜 G (MulZeroClass.toHasZero.{u2} 𝕜 (MulZeroOneClass.toMulZeroClass.{u2} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (MulActionWithZero.toSMulWithZero.{u2, u5} 𝕜 G (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (Module.toMulActionWithZero.{u2, u5} 𝕜 G (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))))) (NormedSpace.boundedSMul.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) (LipschitzAdd.continuousAdd.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)) (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (NormedAddGroup.toAddGroup.{u5} G (NormedAddCommGroup.toNormedAddGroup.{u5} G _inst_9)))) (SeminormedAddCommGroup.to_lipschitzAdd.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))))) (fun (_x : ContinuousLinearMap.{u2, u2, u3, max u4 u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (ContinuousLinearMap.{u2, u2, u4, u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10)) (ContinuousLinearMap.topologicalSpace.{u2, u2, u4, u5} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F G (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))) (ContinuousLinearMap.addCommMonoid.{u2, u2, u4, u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (LipschitzAdd.continuousAdd.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)) (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (NormedAddGroup.toAddGroup.{u5} G (NormedAddCommGroup.toNormedAddGroup.{u5} G _inst_9)))) (SeminormedAddCommGroup.to_lipschitzAdd.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6) (ContinuousLinearMap.module.{u2, u2, u2, u4, u5} 𝕜 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (smulCommClass_self.{u2, u5} 𝕜 G (CommRing.toCommMonoid.{u2} 𝕜 (SeminormedCommRing.toCommRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (MulActionWithZero.toMulAction.{u2, u5} 𝕜 G (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (SeminormedAddCommGroup.toAddCommGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))))) (Module.toMulActionWithZero.{u2, u5} 𝕜 G (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u5} G (SeminormedAddCommGroup.toAddCommGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10)))) (ContinuousSMul.continuousConstSMul.{u2, u5} 𝕜 G (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (SMulZeroClass.toHasSmul.{u2, u5} 𝕜 G (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (SMulWithZero.toSmulZeroClass.{u2, u5} 𝕜 G (MulZeroClass.toHasZero.{u2} 𝕜 (MulZeroOneClass.toMulZeroClass.{u2} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (MulActionWithZero.toSMulWithZero.{u2, u5} 𝕜 G (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (Module.toMulActionWithZero.{u2, u5} 𝕜 G (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))))) (BoundedSMul.continuousSMul.{u2, u5} 𝕜 G (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)) (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (SeminormedAddGroup.toAddGroup.{u5} G (SeminormedAddCommGroup.toSeminormedAddGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))))))) (SMulZeroClass.toHasSmul.{u2, u5} 𝕜 G (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (SMulWithZero.toSmulZeroClass.{u2, u5} 𝕜 G (MulZeroClass.toHasZero.{u2} 𝕜 (MulZeroOneClass.toMulZeroClass.{u2} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (MulActionWithZero.toSMulWithZero.{u2, u5} 𝕜 G (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (Module.toMulActionWithZero.{u2, u5} 𝕜 G (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))))) (NormedSpace.boundedSMul.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) (LipschitzAdd.continuousAdd.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)) (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (NormedAddGroup.toAddGroup.{u5} G (NormedAddCommGroup.toNormedAddGroup.{u5} G _inst_9)))) (SeminormedAddCommGroup.to_lipschitzAdd.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))))) => E -> (ContinuousLinearMap.{u2, u2, u4, u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))) (ContinuousLinearMap.toFun.{u2, u2, u3, max u4 u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) E (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u3} E (NormedAddCommGroup.toAddCommGroup.{u3} E _inst_5)) (ContinuousLinearMap.{u2, u2, u4, u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10)) (ContinuousLinearMap.topologicalSpace.{u2, u2, u4, u5} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F G (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))) (ContinuousLinearMap.addCommMonoid.{u2, u2, u4, u5} 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (LipschitzAdd.continuousAdd.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)) (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (NormedAddGroup.toAddGroup.{u5} G (NormedAddCommGroup.toNormedAddGroup.{u5} G _inst_9)))) (SeminormedAddCommGroup.to_lipschitzAdd.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (NormedSpace.toModule.{u2, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_5) _inst_6) (ContinuousLinearMap.module.{u2, u2, u2, u4, u5} 𝕜 𝕜 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) F (UniformSpace.toTopologicalSpace.{u4} F (PseudoMetricSpace.toUniformSpace.{u4} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u4} F (NormedAddCommGroup.toAddCommGroup.{u4} F _inst_7)) (NormedSpace.toModule.{u2, u4} 𝕜 F (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} F _inst_7) _inst_8) G (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10) (smulCommClass_self.{u2, u5} 𝕜 G (CommRing.toCommMonoid.{u2} 𝕜 (SeminormedCommRing.toCommRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (MulActionWithZero.toMulAction.{u2, u5} 𝕜 G (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (SeminormedAddCommGroup.toAddCommGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))))) (Module.toMulActionWithZero.{u2, u5} 𝕜 G (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u5} G (SeminormedAddCommGroup.toAddCommGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10)))) (ContinuousSMul.continuousConstSMul.{u2, u5} 𝕜 G (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) (UniformSpace.toTopologicalSpace.{u5} G (PseudoMetricSpace.toUniformSpace.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)))) (SMulZeroClass.toHasSmul.{u2, u5} 𝕜 G (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (SMulWithZero.toSmulZeroClass.{u2, u5} 𝕜 G (MulZeroClass.toHasZero.{u2} 𝕜 (MulZeroOneClass.toMulZeroClass.{u2} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (MulActionWithZero.toSMulWithZero.{u2, u5} 𝕜 G (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (Module.toMulActionWithZero.{u2, u5} 𝕜 G (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))))) (BoundedSMul.continuousSMul.{u2, u5} 𝕜 G (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)) (MulZeroClass.toHasZero.{u2} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (SeminormedAddGroup.toAddGroup.{u5} G (SeminormedAddCommGroup.toSeminormedAddGroup.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))))))) (SMulZeroClass.toHasSmul.{u2, u5} 𝕜 G (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (SMulWithZero.toSmulZeroClass.{u2, u5} 𝕜 G (MulZeroClass.toHasZero.{u2} 𝕜 (MulZeroOneClass.toMulZeroClass.{u2} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (MulActionWithZero.toSMulWithZero.{u2, u5} 𝕜 G (Semiring.toMonoidWithZero.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4)))))) (AddZeroClass.toHasZero.{u5} G (AddMonoid.toAddZeroClass.{u5} G (AddCommMonoid.toAddMonoid.{u5} G (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9))))) (Module.toMulActionWithZero.{u2, u5} 𝕜 G (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u5} G (NormedAddCommGroup.toAddCommGroup.{u5} G _inst_9)) (NormedSpace.toModule.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))))) (NormedSpace.boundedSMul.{u2, u5} 𝕜 G (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9) _inst_10))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (Ring.toSemiring.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_4))))))) (LipschitzAdd.continuousAdd.{u5} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9)) (SubNegMonoid.toAddMonoid.{u5} G (AddGroup.toSubNegMonoid.{u5} G (NormedAddGroup.toAddGroup.{u5} G (NormedAddCommGroup.toNormedAddGroup.{u5} G _inst_9)))) (SeminormedAddCommGroup.to_lipschitzAdd.{u5} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u5} G _inst_9))))) L (f x)) (g x)) μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {𝕜 : Type.{u5}} [_inst_4 : NontriviallyNormedField.{u5} 𝕜] {E : Type.{u4}} [_inst_5 : NormedAddCommGroup.{u4} E] [_inst_6 : NormedSpace.{u5, u4} 𝕜 E (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5)] {F : Type.{u2}} [_inst_7 : NormedAddCommGroup.{u2} F] [_inst_8 : NormedSpace.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)] {G : Type.{u3}} [_inst_9 : NormedAddCommGroup.{u3} G] [_inst_10 : NormedSpace.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)] (L : ContinuousLinearMap.{u5, u5, u4, max u3 u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) E (UniformSpace.toTopologicalSpace.{u4} E (PseudoMetricSpace.toUniformSpace.{u4} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u4} E (NormedAddCommGroup.toAddCommGroup.{u4} E _inst_5)) (ContinuousLinearMap.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)) (ContinuousLinearMap.topologicalSpace.{u5, u5, u2, u3} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F G (SeminormedAddCommGroup.toAddCommGroup.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (SeminormedAddCommGroup.toAddCommGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9))) (ContinuousLinearMap.addCommMonoid.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (TopologicalAddGroup.toContinuousAdd.{u3} G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedAddGroup.toAddGroup.{u3} G (NormedAddCommGroup.toNormedAddGroup.{u3} G _inst_9)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedSpace.toModule.{u5, u4} 𝕜 E (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5) _inst_6) (ContinuousLinearMap.module.{u5, u5, u5, u2, u3} 𝕜 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (smulCommClass_self.{u5, u3} 𝕜 G (CommRing.toCommMonoid.{u5} 𝕜 (EuclideanDomain.toCommRing.{u5} 𝕜 (Field.toEuclideanDomain.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (MulActionWithZero.toMulAction.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (SubtractionCommMonoid.toSubtractionMonoid.{u3} G (AddCommGroup.toDivisionAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)))) (ContinuousSMul.continuousConstSMul.{u5, u3} 𝕜 G (UniformSpace.toTopologicalSpace.{u5} 𝕜 (PseudoMetricSpace.toUniformSpace.{u5} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u5} 𝕜 (SeminormedCommRing.toSeminormedRing.{u5} 𝕜 (NormedCommRing.toSeminormedCommRing.{u5} 𝕜 (NormedField.toNormedCommRing.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SMulZeroClass.toSMul.{u5, u3} 𝕜 G (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (SMulWithZero.toSMulZeroClass.{u5, u3} 𝕜 G (MonoidWithZero.toZero.{u5} 𝕜 (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))))) (BoundedSMul.continuousSMul.{u5, u3} 𝕜 G (SeminormedRing.toPseudoMetricSpace.{u5} 𝕜 (SeminormedCommRing.toSeminormedRing.{u5} 𝕜 (NormedCommRing.toSeminormedCommRing.{u5} 𝕜 (NormedField.toNormedCommRing.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (CommMonoidWithZero.toZero.{u5} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u5} 𝕜 (Semifield.toCommGroupWithZero.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (SubtractionCommMonoid.toSubtractionMonoid.{u3} G (AddCommGroup.toDivisionAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))))) (SMulZeroClass.toSMul.{u5, u3} 𝕜 G (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (SMulWithZero.toSMulZeroClass.{u5, u3} 𝕜 G (MonoidWithZero.toZero.{u5} 𝕜 (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))))) (NormedSpace.boundedSMul.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (TopologicalAddGroup.toContinuousAdd.{u3} G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedAddGroup.toAddGroup.{u3} G (NormedAddCommGroup.toNormedAddGroup.{u3} G _inst_9)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9))))) {f : α -> E} {g : α -> F}, (MeasureTheory.AEStronglyMeasurable.{u1, u4} α E (UniformSpace.toTopologicalSpace.{u4} E (PseudoMetricSpace.toUniformSpace.{u4} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5)))) m f μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u2} α F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) m g μ) -> (MeasureTheory.AEStronglyMeasurable.{u1, u3} α G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) m (fun (x : α) => FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : E) => ContinuousLinearMap.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)) (f x)) F (fun (_x : F) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : F) => G) _x) (ContinuousMapClass.toFunLike.{max u2 u3, u2, u3} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : E) => ContinuousLinearMap.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)) (f x)) F G (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (ContinuousSemilinearMapClass.toContinuousMapClass.{max u2 u3, u5, u5, u2, u3} ((fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : E) => ContinuousLinearMap.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)) (f x)) 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (ContinuousLinearMap.continuousSemilinearMapClass.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)))) (FunLike.coe.{max (max (succ u4) (succ u2)) (succ u3), succ u4, max (succ u2) (succ u3)} (ContinuousLinearMap.{u5, u5, u4, max u3 u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) E (UniformSpace.toTopologicalSpace.{u4} E (PseudoMetricSpace.toUniformSpace.{u4} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u4} E (NormedAddCommGroup.toAddCommGroup.{u4} E _inst_5)) (ContinuousLinearMap.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)) (ContinuousLinearMap.topologicalSpace.{u5, u5, u2, u3} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F G (SeminormedAddCommGroup.toAddCommGroup.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (SeminormedAddCommGroup.toAddCommGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9))) (ContinuousLinearMap.addCommMonoid.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (TopologicalAddGroup.toContinuousAdd.{u3} G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedAddGroup.toAddGroup.{u3} G (NormedAddCommGroup.toNormedAddGroup.{u3} G _inst_9)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedSpace.toModule.{u5, u4} 𝕜 E (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5) _inst_6) (ContinuousLinearMap.module.{u5, u5, u5, u2, u3} 𝕜 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (smulCommClass_self.{u5, u3} 𝕜 G (CommRing.toCommMonoid.{u5} 𝕜 (EuclideanDomain.toCommRing.{u5} 𝕜 (Field.toEuclideanDomain.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (MulActionWithZero.toMulAction.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (SubtractionCommMonoid.toSubtractionMonoid.{u3} G (AddCommGroup.toDivisionAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)))) (ContinuousSMul.continuousConstSMul.{u5, u3} 𝕜 G (UniformSpace.toTopologicalSpace.{u5} 𝕜 (PseudoMetricSpace.toUniformSpace.{u5} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u5} 𝕜 (SeminormedCommRing.toSeminormedRing.{u5} 𝕜 (NormedCommRing.toSeminormedCommRing.{u5} 𝕜 (NormedField.toNormedCommRing.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SMulZeroClass.toSMul.{u5, u3} 𝕜 G (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (SMulWithZero.toSMulZeroClass.{u5, u3} 𝕜 G (MonoidWithZero.toZero.{u5} 𝕜 (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))))) (BoundedSMul.continuousSMul.{u5, u3} 𝕜 G (SeminormedRing.toPseudoMetricSpace.{u5} 𝕜 (SeminormedCommRing.toSeminormedRing.{u5} 𝕜 (NormedCommRing.toSeminormedCommRing.{u5} 𝕜 (NormedField.toNormedCommRing.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (CommMonoidWithZero.toZero.{u5} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u5} 𝕜 (Semifield.toCommGroupWithZero.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (SubtractionCommMonoid.toSubtractionMonoid.{u3} G (AddCommGroup.toDivisionAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))))) (SMulZeroClass.toSMul.{u5, u3} 𝕜 G (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (SMulWithZero.toSMulZeroClass.{u5, u3} 𝕜 G (MonoidWithZero.toZero.{u5} 𝕜 (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))))) (NormedSpace.boundedSMul.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (TopologicalAddGroup.toContinuousAdd.{u3} G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedAddGroup.toAddGroup.{u3} G (NormedAddCommGroup.toNormedAddGroup.{u3} G _inst_9)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9))))) E (fun (_x : E) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : E) => ContinuousLinearMap.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)) _x) (ContinuousMapClass.toFunLike.{max (max u4 u2) u3, u4, max u2 u3} (ContinuousLinearMap.{u5, u5, u4, max u3 u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) E (UniformSpace.toTopologicalSpace.{u4} E (PseudoMetricSpace.toUniformSpace.{u4} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u4} E (NormedAddCommGroup.toAddCommGroup.{u4} E _inst_5)) (ContinuousLinearMap.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)) (ContinuousLinearMap.topologicalSpace.{u5, u5, u2, u3} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F G (SeminormedAddCommGroup.toAddCommGroup.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (SeminormedAddCommGroup.toAddCommGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9))) (ContinuousLinearMap.addCommMonoid.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (TopologicalAddGroup.toContinuousAdd.{u3} G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedAddGroup.toAddGroup.{u3} G (NormedAddCommGroup.toNormedAddGroup.{u3} G _inst_9)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedSpace.toModule.{u5, u4} 𝕜 E (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5) _inst_6) (ContinuousLinearMap.module.{u5, u5, u5, u2, u3} 𝕜 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (smulCommClass_self.{u5, u3} 𝕜 G (CommRing.toCommMonoid.{u5} 𝕜 (EuclideanDomain.toCommRing.{u5} 𝕜 (Field.toEuclideanDomain.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (MulActionWithZero.toMulAction.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (SubtractionCommMonoid.toSubtractionMonoid.{u3} G (AddCommGroup.toDivisionAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)))) (ContinuousSMul.continuousConstSMul.{u5, u3} 𝕜 G (UniformSpace.toTopologicalSpace.{u5} 𝕜 (PseudoMetricSpace.toUniformSpace.{u5} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u5} 𝕜 (SeminormedCommRing.toSeminormedRing.{u5} 𝕜 (NormedCommRing.toSeminormedCommRing.{u5} 𝕜 (NormedField.toNormedCommRing.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SMulZeroClass.toSMul.{u5, u3} 𝕜 G (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (SMulWithZero.toSMulZeroClass.{u5, u3} 𝕜 G (MonoidWithZero.toZero.{u5} 𝕜 (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))))) (BoundedSMul.continuousSMul.{u5, u3} 𝕜 G (SeminormedRing.toPseudoMetricSpace.{u5} 𝕜 (SeminormedCommRing.toSeminormedRing.{u5} 𝕜 (NormedCommRing.toSeminormedCommRing.{u5} 𝕜 (NormedField.toNormedCommRing.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (CommMonoidWithZero.toZero.{u5} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u5} 𝕜 (Semifield.toCommGroupWithZero.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (SubtractionCommMonoid.toSubtractionMonoid.{u3} G (AddCommGroup.toDivisionAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))))) (SMulZeroClass.toSMul.{u5, u3} 𝕜 G (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (SMulWithZero.toSMulZeroClass.{u5, u3} 𝕜 G (MonoidWithZero.toZero.{u5} 𝕜 (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))))) (NormedSpace.boundedSMul.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (TopologicalAddGroup.toContinuousAdd.{u3} G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedAddGroup.toAddGroup.{u3} G (NormedAddCommGroup.toNormedAddGroup.{u3} G _inst_9)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9))))) E (ContinuousLinearMap.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)) (UniformSpace.toTopologicalSpace.{u4} E (PseudoMetricSpace.toUniformSpace.{u4} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5)))) (ContinuousLinearMap.topologicalSpace.{u5, u5, u2, u3} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F G (SeminormedAddCommGroup.toAddCommGroup.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (SeminormedAddCommGroup.toAddCommGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9))) (ContinuousSemilinearMapClass.toContinuousMapClass.{max (max u4 u2) u3, u5, u5, u4, max u2 u3} (ContinuousLinearMap.{u5, u5, u4, max u3 u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) E (UniformSpace.toTopologicalSpace.{u4} E (PseudoMetricSpace.toUniformSpace.{u4} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u4} E (NormedAddCommGroup.toAddCommGroup.{u4} E _inst_5)) (ContinuousLinearMap.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)) (ContinuousLinearMap.topologicalSpace.{u5, u5, u2, u3} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F G (SeminormedAddCommGroup.toAddCommGroup.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (SeminormedAddCommGroup.toAddCommGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9))) (ContinuousLinearMap.addCommMonoid.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (TopologicalAddGroup.toContinuousAdd.{u3} G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedAddGroup.toAddGroup.{u3} G (NormedAddCommGroup.toNormedAddGroup.{u3} G _inst_9)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedSpace.toModule.{u5, u4} 𝕜 E (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5) _inst_6) (ContinuousLinearMap.module.{u5, u5, u5, u2, u3} 𝕜 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (smulCommClass_self.{u5, u3} 𝕜 G (CommRing.toCommMonoid.{u5} 𝕜 (EuclideanDomain.toCommRing.{u5} 𝕜 (Field.toEuclideanDomain.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (MulActionWithZero.toMulAction.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (SubtractionCommMonoid.toSubtractionMonoid.{u3} G (AddCommGroup.toDivisionAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)))) (ContinuousSMul.continuousConstSMul.{u5, u3} 𝕜 G (UniformSpace.toTopologicalSpace.{u5} 𝕜 (PseudoMetricSpace.toUniformSpace.{u5} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u5} 𝕜 (SeminormedCommRing.toSeminormedRing.{u5} 𝕜 (NormedCommRing.toSeminormedCommRing.{u5} 𝕜 (NormedField.toNormedCommRing.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SMulZeroClass.toSMul.{u5, u3} 𝕜 G (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (SMulWithZero.toSMulZeroClass.{u5, u3} 𝕜 G (MonoidWithZero.toZero.{u5} 𝕜 (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))))) (BoundedSMul.continuousSMul.{u5, u3} 𝕜 G (SeminormedRing.toPseudoMetricSpace.{u5} 𝕜 (SeminormedCommRing.toSeminormedRing.{u5} 𝕜 (NormedCommRing.toSeminormedCommRing.{u5} 𝕜 (NormedField.toNormedCommRing.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (CommMonoidWithZero.toZero.{u5} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u5} 𝕜 (Semifield.toCommGroupWithZero.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (SubtractionCommMonoid.toSubtractionMonoid.{u3} G (AddCommGroup.toDivisionAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))))) (SMulZeroClass.toSMul.{u5, u3} 𝕜 G (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (SMulWithZero.toSMulZeroClass.{u5, u3} 𝕜 G (MonoidWithZero.toZero.{u5} 𝕜 (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))))) (NormedSpace.boundedSMul.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (TopologicalAddGroup.toContinuousAdd.{u3} G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedAddGroup.toAddGroup.{u3} G (NormedAddCommGroup.toNormedAddGroup.{u3} G _inst_9)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9))))) 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) E (UniformSpace.toTopologicalSpace.{u4} E (PseudoMetricSpace.toUniformSpace.{u4} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u4} E (NormedAddCommGroup.toAddCommGroup.{u4} E _inst_5)) (ContinuousLinearMap.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)) (ContinuousLinearMap.topologicalSpace.{u5, u5, u2, u3} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F G (SeminormedAddCommGroup.toAddCommGroup.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (SeminormedAddCommGroup.toAddCommGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9))) (ContinuousLinearMap.addCommMonoid.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (TopologicalAddGroup.toContinuousAdd.{u3} G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedAddGroup.toAddGroup.{u3} G (NormedAddCommGroup.toNormedAddGroup.{u3} G _inst_9)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedSpace.toModule.{u5, u4} 𝕜 E (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5) _inst_6) (ContinuousLinearMap.module.{u5, u5, u5, u2, u3} 𝕜 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (smulCommClass_self.{u5, u3} 𝕜 G (CommRing.toCommMonoid.{u5} 𝕜 (EuclideanDomain.toCommRing.{u5} 𝕜 (Field.toEuclideanDomain.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (MulActionWithZero.toMulAction.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (SubtractionCommMonoid.toSubtractionMonoid.{u3} G (AddCommGroup.toDivisionAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)))) (ContinuousSMul.continuousConstSMul.{u5, u3} 𝕜 G (UniformSpace.toTopologicalSpace.{u5} 𝕜 (PseudoMetricSpace.toUniformSpace.{u5} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u5} 𝕜 (SeminormedCommRing.toSeminormedRing.{u5} 𝕜 (NormedCommRing.toSeminormedCommRing.{u5} 𝕜 (NormedField.toNormedCommRing.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SMulZeroClass.toSMul.{u5, u3} 𝕜 G (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (SMulWithZero.toSMulZeroClass.{u5, u3} 𝕜 G (MonoidWithZero.toZero.{u5} 𝕜 (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))))) (BoundedSMul.continuousSMul.{u5, u3} 𝕜 G (SeminormedRing.toPseudoMetricSpace.{u5} 𝕜 (SeminormedCommRing.toSeminormedRing.{u5} 𝕜 (NormedCommRing.toSeminormedCommRing.{u5} 𝕜 (NormedField.toNormedCommRing.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (CommMonoidWithZero.toZero.{u5} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u5} 𝕜 (Semifield.toCommGroupWithZero.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (SubtractionCommMonoid.toSubtractionMonoid.{u3} G (AddCommGroup.toDivisionAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))))) (SMulZeroClass.toSMul.{u5, u3} 𝕜 G (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (SMulWithZero.toSMulZeroClass.{u5, u3} 𝕜 G (MonoidWithZero.toZero.{u5} 𝕜 (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))))) (NormedSpace.boundedSMul.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (TopologicalAddGroup.toContinuousAdd.{u3} G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedAddGroup.toAddGroup.{u3} G (NormedAddCommGroup.toNormedAddGroup.{u3} G _inst_9)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (ContinuousLinearMap.continuousSemilinearMapClass.{u5, u5, u4, max u2 u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) E (UniformSpace.toTopologicalSpace.{u4} E (PseudoMetricSpace.toUniformSpace.{u4} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5)))) (AddCommGroup.toAddCommMonoid.{u4} E (NormedAddCommGroup.toAddCommGroup.{u4} E _inst_5)) (ContinuousLinearMap.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)) (ContinuousLinearMap.topologicalSpace.{u5, u5, u2, u3} 𝕜 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F G (SeminormedAddCommGroup.toAddCommGroup.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (SeminormedAddCommGroup.toAddCommGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9))) (ContinuousLinearMap.addCommMonoid.{u5, u5, u2, u3} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (TopologicalAddGroup.toContinuousAdd.{u3} G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedAddGroup.toAddGroup.{u3} G (NormedAddCommGroup.toNormedAddGroup.{u3} G _inst_9)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedSpace.toModule.{u5, u4} 𝕜 E (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} E _inst_5) _inst_6) (ContinuousLinearMap.module.{u5, u5, u5, u2, u3} 𝕜 𝕜 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) F (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7)))) (AddCommGroup.toAddCommMonoid.{u2} F (NormedAddCommGroup.toAddCommGroup.{u2} F _inst_7)) (NormedSpace.toModule.{u5, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_7) _inst_8) G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10) (smulCommClass_self.{u5, u3} 𝕜 G (CommRing.toCommMonoid.{u5} 𝕜 (EuclideanDomain.toCommRing.{u5} 𝕜 (Field.toEuclideanDomain.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (MulActionWithZero.toMulAction.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (SubtractionCommMonoid.toSubtractionMonoid.{u3} G (AddCommGroup.toDivisionAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10)))) (ContinuousSMul.continuousConstSMul.{u5, u3} 𝕜 G (UniformSpace.toTopologicalSpace.{u5} 𝕜 (PseudoMetricSpace.toUniformSpace.{u5} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u5} 𝕜 (SeminormedCommRing.toSeminormedRing.{u5} 𝕜 (NormedCommRing.toSeminormedCommRing.{u5} 𝕜 (NormedField.toNormedCommRing.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (SMulZeroClass.toSMul.{u5, u3} 𝕜 G (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (SMulWithZero.toSMulZeroClass.{u5, u3} 𝕜 G (MonoidWithZero.toZero.{u5} 𝕜 (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))))) (BoundedSMul.continuousSMul.{u5, u3} 𝕜 G (SeminormedRing.toPseudoMetricSpace.{u5} 𝕜 (SeminormedCommRing.toSeminormedRing.{u5} 𝕜 (NormedCommRing.toSeminormedCommRing.{u5} 𝕜 (NormedField.toNormedCommRing.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)) (CommMonoidWithZero.toZero.{u5} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u5} 𝕜 (Semifield.toCommGroupWithZero.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (NegZeroClass.toZero.{u3} G (SubNegZeroMonoid.toNegZeroClass.{u3} G (SubtractionMonoid.toSubNegZeroMonoid.{u3} G (SubtractionCommMonoid.toSubtractionMonoid.{u3} G (AddCommGroup.toDivisionAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))))) (SMulZeroClass.toSMul.{u5, u3} 𝕜 G (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (SMulWithZero.toSMulZeroClass.{u5, u3} 𝕜 G (MonoidWithZero.toZero.{u5} 𝕜 (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (MulActionWithZero.toSMulWithZero.{u5, u3} 𝕜 G (Semiring.toMonoidWithZero.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4)))))) (AddMonoid.toZero.{u3} G (AddCommMonoid.toAddMonoid.{u3} G (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)))) (Module.toMulActionWithZero.{u5, u3} 𝕜 G (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))) (AddCommGroup.toAddCommMonoid.{u3} G (NormedAddCommGroup.toAddCommGroup.{u3} G _inst_9)) (NormedSpace.toModule.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))))) (NormedSpace.boundedSMul.{u5, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9) _inst_10))) (RingHom.id.{u5} 𝕜 (Semiring.toNonAssocSemiring.{u5} 𝕜 (DivisionSemiring.toSemiring.{u5} 𝕜 (Semifield.toDivisionSemiring.{u5} 𝕜 (Field.toSemifield.{u5} 𝕜 (NormedField.toField.{u5} 𝕜 (NontriviallyNormedField.toNormedField.{u5} 𝕜 _inst_4))))))) (TopologicalAddGroup.toContinuousAdd.{u3} G (UniformSpace.toTopologicalSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9)))) (NormedAddGroup.toAddGroup.{u3} G (NormedAddCommGroup.toNormedAddGroup.{u3} G _inst_9)) (SeminormedAddCommGroup.toTopologicalAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_9))))))) L (f x)) (g x)) μ)
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.ae_strongly_measurable_comp₂ ContinuousLinearMap.aestronglyMeasurable_comp₂ₓ'. -/
theorem ContinuousLinearMap.aestronglyMeasurable_comp₂ (L : E →L[𝕜] F →L[𝕜] G) {f : α → E}
    {g : α → F} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => L (f x) (g x)) μ :=
  L.continuous₂.comp_aestronglyMeasurable <| hf.prod_mk hg
#align continuous_linear_map.ae_strongly_measurable_comp₂ ContinuousLinearMap.aestronglyMeasurable_comp₂

end ContinuousLinearMapNontriviallyNormedField

/- warning: ae_strongly_measurable_with_density_iff -> aestronglyMeasurable_withDensity_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {E : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} E] [_inst_5 : NormedSpace.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_4)] {f : α -> NNReal}, (Measurable.{u1, 0} α NNReal m NNReal.measurableSpace f) -> (forall {g : α -> E}, Iff (MeasureTheory.AEStronglyMeasurable.{u1, u2} α E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_4)))) m g (MeasureTheory.Measure.withDensity.{u1} α m μ (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) (f x)))) (MeasureTheory.AEStronglyMeasurable.{u1, u2} α E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_4)))) m (fun (x : α) => SMul.smul.{0, u2} Real E (SMulZeroClass.toHasSmul.{0, u2} Real E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u2} Real E (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real E (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_4)))))) (Module.toMulActionWithZero.{0, u2} Real E (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_4))) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_4) _inst_5))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (f x)) (g x)) μ))
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {E : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} E] [_inst_5 : NormedSpace.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_4)] {f : α -> NNReal}, (Measurable.{u1, 0} α NNReal m NNReal.measurableSpace f) -> (forall {g : α -> E}, Iff (MeasureTheory.AEStronglyMeasurable.{u1, u2} α E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_4)))) m g (MeasureTheory.Measure.withDensity.{u1} α m μ (fun (x : α) => ENNReal.some (f x)))) (MeasureTheory.AEStronglyMeasurable.{u1, u2} α E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_4)))) m (fun (x : α) => HSMul.hSMul.{0, u2, u2} Real E E (instHSMul.{0, u2} Real E (SMulZeroClass.toSMul.{0, u2} Real E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u2} Real E Real.instZeroReal (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u2} Real E Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_4)))))) (Module.toMulActionWithZero.{0, u2} Real E Real.semiring (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_4)) (NormedSpace.toModule.{0, u2} Real E Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_4) _inst_5)))))) (NNReal.toReal (f x)) (g x)) μ))
Case conversion may be inaccurate. Consider using '#align ae_strongly_measurable_with_density_iff aestronglyMeasurable_withDensity_iffₓ'. -/
theorem aestronglyMeasurable_withDensity_iff {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → ℝ≥0} (hf : Measurable f) {g : α → E} :
    AEStronglyMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEStronglyMeasurable (fun x => (f x : ℝ) • g x) μ :=
  by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x ≠ 0 } := (hf (measurable_set_singleton 0)).compl
    refine' ⟨fun x => (f x : ℝ) • g' x, hf.coe_nnreal_real.strongly_measurable.smul g'meas, _⟩
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ { x | f x ≠ 0 }
    · rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg']with a ha h'a
      have : (f a : ℝ≥0∞) ≠ 0 := by simpa only [Ne.def, ENNReal.coe_eq_zero] using h'a
      rw [ha this]
    · filter_upwards [ae_restrict_mem A.compl]with x hx
      simp only [Classical.not_not, mem_set_of_eq, mem_compl_iff] at hx
      simp [hx]
  · rintro ⟨g', g'meas, hg'⟩
    refine' ⟨fun x => (f x : ℝ)⁻¹ • g' x, hf.coe_nnreal_real.inv.strongly_measurable.smul g'meas, _⟩
    rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg']with x hx h'x
    rw [← hx, smul_smul, _root_.inv_mul_cancel, one_smul]
    simp only [Ne.def, ENNReal.coe_eq_zero] at h'x
    simpa only [NNReal.coe_eq_zero, Ne.def] using h'x
#align ae_strongly_measurable_with_density_iff aestronglyMeasurable_withDensity_iff

end AeStronglyMeasurable

/-! ## Almost everywhere finitely strongly measurable functions -/


namespace AeFinStronglyMeasurable

variable {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β] {f g : α → β}

section Mk

variable [Zero β]

#print MeasureTheory.AEFinStronglyMeasurable.mk /-
/-- A `fin_strongly_measurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`fin_strongly_measurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : AEFinStronglyMeasurable f μ) : α → β :=
  hf.some
#align measure_theory.ae_fin_strongly_measurable.mk MeasureTheory.AEFinStronglyMeasurable.mk
-/

/- warning: measure_theory.ae_fin_strongly_measurable.fin_strongly_measurable_mk -> MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_3 : Zero.{u2} β] (hf : MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m f μ), MeasureTheory.FinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m (MeasureTheory.AEFinStronglyMeasurable.mk.{u1, u2} α β m μ _inst_2 _inst_3 f hf) μ
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} [_inst_3 : Zero.{u1} β] (hf : MeasureTheory.AEFinStronglyMeasurable.{u2, u1} α β _inst_2 _inst_3 m f μ), MeasureTheory.FinStronglyMeasurable.{u2, u1} α β _inst_2 _inst_3 m (MeasureTheory.AEFinStronglyMeasurable.mk.{u2, u1} α β m μ _inst_2 _inst_3 f hf) μ
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable.fin_strongly_measurable_mk MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mkₓ'. -/
theorem finStronglyMeasurable_mk (hf : AEFinStronglyMeasurable f μ) :
    FinStronglyMeasurable (hf.mk f) μ :=
  hf.choose_spec.1
#align measure_theory.ae_fin_strongly_measurable.fin_strongly_measurable_mk MeasureTheory.AEFinStronglyMeasurable.finStronglyMeasurable_mk

/- warning: measure_theory.ae_fin_strongly_measurable.ae_eq_mk -> MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_3 : Zero.{u2} β] (hf : MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m f μ), Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m μ) f (MeasureTheory.AEFinStronglyMeasurable.mk.{u1, u2} α β m μ _inst_2 _inst_3 f hf)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} [_inst_3 : Zero.{u1} β] (hf : MeasureTheory.AEFinStronglyMeasurable.{u2, u1} α β _inst_2 _inst_3 m f μ), Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α m μ) f (MeasureTheory.AEFinStronglyMeasurable.mk.{u2, u1} α β m μ _inst_2 _inst_3 f hf)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable.ae_eq_mk MeasureTheory.AEFinStronglyMeasurable.ae_eq_mkₓ'. -/
theorem ae_eq_mk (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ] hf.mk f :=
  hf.choose_spec.2
#align measure_theory.ae_fin_strongly_measurable.ae_eq_mk MeasureTheory.AEFinStronglyMeasurable.ae_eq_mk

#print MeasureTheory.AEFinStronglyMeasurable.aemeasurable /-
protected theorem aemeasurable {β} [Zero β] [MeasurableSpace β] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [BorelSpace β] {f : α → β} (hf : AEFinStronglyMeasurable f μ) :
    AEMeasurable f μ :=
  ⟨hf.mk f, hf.finStronglyMeasurable_mk.Measurable, hf.ae_eq_mk⟩
#align measure_theory.ae_fin_strongly_measurable.ae_measurable MeasureTheory.AEFinStronglyMeasurable.aemeasurable
-/

end Mk

section Arithmetic

/- warning: measure_theory.ae_fin_strongly_measurable.mul -> MeasureTheory.AEFinStronglyMeasurable.mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_3 : MonoidWithZero.{u2} β] [_inst_4 : ContinuousMul.{u2} β _inst_2 (MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3)))], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))) m f μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))) m g μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (MulZeroClass.toHasZero.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))) m (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toHasMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))))) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_3 : MonoidWithZero.{u2} β] [_inst_4 : ContinuousMul.{u2} β _inst_2 (MulZeroClass.toMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3)))], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (MonoidWithZero.toZero.{u2} β _inst_3) m f μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (MonoidWithZero.toZero.{u2} β _inst_3) m g μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (MonoidWithZero.toZero.{u2} β _inst_3) m (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHMul.{max u1 u2} (α -> β) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => MulZeroClass.toMul.{u2} β (MulZeroOneClass.toMulZeroClass.{u2} β (MonoidWithZero.toMulZeroOneClass.{u2} β _inst_3))))) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable.mul MeasureTheory.AEFinStronglyMeasurable.mulₓ'. -/
protected theorem mul [MonoidWithZero β] [ContinuousMul β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f * g) μ :=
  ⟨hf.mk f * hg.mk g, hf.finStronglyMeasurable_mk.mul hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.mul hg.ae_eq_mk⟩
#align measure_theory.ae_fin_strongly_measurable.mul MeasureTheory.AEFinStronglyMeasurable.mul

/- warning: measure_theory.ae_fin_strongly_measurable.add -> MeasureTheory.AEFinStronglyMeasurable.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_3 : AddMonoid.{u2} β] [_inst_4 : ContinuousAdd.{u2} β _inst_2 (AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3))], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)) m f μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)) m g μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)) m (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHAdd.{max u1 u2} (α -> β) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toHasAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)))) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_3 : AddMonoid.{u2} β] [_inst_4 : ContinuousAdd.{u2} β _inst_2 (AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3))], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddMonoid.toZero.{u2} β _inst_3) m f μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddMonoid.toZero.{u2} β _inst_3) m g μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddMonoid.toZero.{u2} β _inst_3) m (HAdd.hAdd.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHAdd.{max u1 u2} (α -> β) (Pi.instAdd.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => AddZeroClass.toAdd.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_3)))) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable.add MeasureTheory.AEFinStronglyMeasurable.addₓ'. -/
protected theorem add [AddMonoid β] [ContinuousAdd β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f + g) μ :=
  ⟨hf.mk f + hg.mk g, hf.finStronglyMeasurable_mk.add hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.add hg.ae_eq_mk⟩
#align measure_theory.ae_fin_strongly_measurable.add MeasureTheory.AEFinStronglyMeasurable.add

/- warning: measure_theory.ae_fin_strongly_measurable.neg -> MeasureTheory.AEFinStronglyMeasurable.neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_3 : AddGroup.{u2} β] [_inst_4 : TopologicalAddGroup.{u2} β _inst_2 _inst_3], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) m f μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) m (Neg.neg.{max u1 u2} (α -> β) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))) f) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_3 : AddGroup.{u2} β] [_inst_4 : TopologicalAddGroup.{u2} β _inst_2 _inst_3], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) m f μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) m (Neg.neg.{max u1 u2} (α -> β) (Pi.instNeg.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3))))) f) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable.neg MeasureTheory.AEFinStronglyMeasurable.negₓ'. -/
protected theorem neg [AddGroup β] [TopologicalAddGroup β] (hf : AEFinStronglyMeasurable f μ) :
    AEFinStronglyMeasurable (-f) μ :=
  ⟨-hf.mk f, hf.finStronglyMeasurable_mk.neg, hf.ae_eq_mk.neg⟩
#align measure_theory.ae_fin_strongly_measurable.neg MeasureTheory.AEFinStronglyMeasurable.neg

/- warning: measure_theory.ae_fin_strongly_measurable.sub -> MeasureTheory.AEFinStronglyMeasurable.sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_3 : AddGroup.{u2} β] [_inst_4 : ContinuousSub.{u2} β _inst_2 (SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) m f μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) m g μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) m (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toHasSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_3 : AddGroup.{u2} β] [_inst_4 : ContinuousSub.{u2} β _inst_2 (SubNegMonoid.toSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3))], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) m f μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) m g μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_3)))) m (HSub.hSub.{max u1 u2, max u1 u2, max u1 u2} (α -> β) (α -> β) (α -> β) (instHSub.{max u1 u2} (α -> β) (Pi.instSub.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SubNegMonoid.toSub.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_3)))) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable.sub MeasureTheory.AEFinStronglyMeasurable.subₓ'. -/
protected theorem sub [AddGroup β] [ContinuousSub β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f - g) μ :=
  ⟨hf.mk f - hg.mk g, hf.finStronglyMeasurable_mk.sub hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sub hg.ae_eq_mk⟩
#align measure_theory.ae_fin_strongly_measurable.sub MeasureTheory.AEFinStronglyMeasurable.sub

/- warning: measure_theory.ae_fin_strongly_measurable.const_smul -> MeasureTheory.AEFinStronglyMeasurable.const_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {𝕜 : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} 𝕜] [_inst_4 : AddMonoid.{u2} β] [_inst_5 : Monoid.{u3} 𝕜] [_inst_6 : DistribMulAction.{u3, u2} 𝕜 β _inst_5 _inst_4] [_inst_7 : ContinuousSMul.{u3, u2} 𝕜 β (SMulZeroClass.toHasSmul.{u3, u2} 𝕜 β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_4)) (DistribSMul.toSmulZeroClass.{u3, u2} 𝕜 β (AddMonoid.toAddZeroClass.{u2} β _inst_4) (DistribMulAction.toDistribSMul.{u3, u2} 𝕜 β _inst_5 _inst_4 _inst_6))) _inst_3 _inst_2], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_4)) m f μ) -> (forall (c : 𝕜), MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_4)) m (SMul.smul.{u3, max u1 u2} 𝕜 (α -> β) (Function.hasSMul.{u1, u3, u2} α 𝕜 β (SMulZeroClass.toHasSmul.{u3, u2} 𝕜 β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β _inst_4)) (DistribSMul.toSmulZeroClass.{u3, u2} 𝕜 β (AddMonoid.toAddZeroClass.{u2} β _inst_4) (DistribMulAction.toDistribSMul.{u3, u2} 𝕜 β _inst_5 _inst_4 _inst_6)))) c f) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {𝕜 : Type.{u3}} [_inst_3 : TopologicalSpace.{u3} 𝕜] [_inst_4 : AddMonoid.{u2} β] [_inst_5 : Monoid.{u3} 𝕜] [_inst_6 : DistribMulAction.{u3, u2} 𝕜 β _inst_5 _inst_4] [_inst_7 : ContinuousSMul.{u3, u2} 𝕜 β (SMulZeroClass.toSMul.{u3, u2} 𝕜 β (AddMonoid.toZero.{u2} β _inst_4) (DistribSMul.toSMulZeroClass.{u3, u2} 𝕜 β (AddMonoid.toAddZeroClass.{u2} β _inst_4) (DistribMulAction.toDistribSMul.{u3, u2} 𝕜 β _inst_5 _inst_4 _inst_6))) _inst_3 _inst_2], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddMonoid.toZero.{u2} β _inst_4) m f μ) -> (forall (c : 𝕜), MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 (AddMonoid.toZero.{u2} β _inst_4) m (HSMul.hSMul.{u3, max u1 u2, max u1 u2} 𝕜 (α -> β) (α -> β) (instHSMul.{u3, max u1 u2} 𝕜 (α -> β) (Pi.instSMul.{u1, u2, u3} α 𝕜 (fun (a._@.Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic._hyg.21457 : α) => β) (fun (i : α) => SMulZeroClass.toSMul.{u3, u2} 𝕜 β (AddMonoid.toZero.{u2} β _inst_4) (DistribSMul.toSMulZeroClass.{u3, u2} 𝕜 β (AddMonoid.toAddZeroClass.{u2} β _inst_4) (DistribMulAction.toDistribSMul.{u3, u2} 𝕜 β _inst_5 _inst_4 _inst_6))))) c f) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable.const_smul MeasureTheory.AEFinStronglyMeasurable.const_smulₓ'. -/
protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [AddMonoid β] [Monoid 𝕜]
    [DistribMulAction 𝕜 β] [ContinuousSMul 𝕜 β] (hf : AEFinStronglyMeasurable f μ) (c : 𝕜) :
    AEFinStronglyMeasurable (c • f) μ :=
  ⟨c • hf.mk f, hf.finStronglyMeasurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩
#align measure_theory.ae_fin_strongly_measurable.const_smul MeasureTheory.AEFinStronglyMeasurable.const_smul

end Arithmetic

section Order

variable [Zero β]

/- warning: measure_theory.ae_fin_strongly_measurable.sup -> MeasureTheory.AEFinStronglyMeasurable.sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_3 : Zero.{u2} β] [_inst_4 : SemilatticeSup.{u2} β] [_inst_5 : ContinuousSup.{u2} β _inst_2 (SemilatticeSup.toHasSup.{u2} β _inst_4)], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m f μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m g μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m (Sup.sup.{max u1 u2} (α -> β) (Pi.hasSup.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SemilatticeSup.toHasSup.{u2} β _inst_4)) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_3 : Zero.{u2} β] [_inst_4 : SemilatticeSup.{u2} β] [_inst_5 : ContinuousSup.{u2} β _inst_2 (SemilatticeSup.toSup.{u2} β _inst_4)], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m f μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m g μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m (Sup.sup.{max u2 u1} (α -> β) (Pi.instSupForAll.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SemilatticeSup.toSup.{u2} β _inst_4)) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable.sup MeasureTheory.AEFinStronglyMeasurable.supₓ'. -/
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f ⊔ g) μ :=
  ⟨hf.mk f ⊔ hg.mk g, hf.finStronglyMeasurable_mk.sup hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.sup hg.ae_eq_mk⟩
#align measure_theory.ae_fin_strongly_measurable.sup MeasureTheory.AEFinStronglyMeasurable.sup

/- warning: measure_theory.ae_fin_strongly_measurable.inf -> MeasureTheory.AEFinStronglyMeasurable.inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_3 : Zero.{u2} β] [_inst_4 : SemilatticeInf.{u2} β] [_inst_5 : ContinuousInf.{u2} β _inst_2 (SemilatticeInf.toHasInf.{u2} β _inst_4)], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m f μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m g μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m (Inf.inf.{max u1 u2} (α -> β) (Pi.hasInf.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SemilatticeInf.toHasInf.{u2} β _inst_4)) f g) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} [_inst_3 : Zero.{u2} β] [_inst_4 : SemilatticeInf.{u2} β] [_inst_5 : ContinuousInf.{u2} β _inst_2 (SemilatticeInf.toInf.{u2} β _inst_4)], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m f μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m g μ) -> (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m (Inf.inf.{max u2 u1} (α -> β) (Pi.instInfForAll.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => SemilatticeInf.toInf.{u2} β _inst_4)) f g) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable.inf MeasureTheory.AEFinStronglyMeasurable.infₓ'. -/
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : AEFinStronglyMeasurable f μ)
    (hg : AEFinStronglyMeasurable g μ) : AEFinStronglyMeasurable (f ⊓ g) μ :=
  ⟨hf.mk f ⊓ hg.mk g, hf.finStronglyMeasurable_mk.inf hg.finStronglyMeasurable_mk,
    hf.ae_eq_mk.inf hg.ae_eq_mk⟩
#align measure_theory.ae_fin_strongly_measurable.inf MeasureTheory.AEFinStronglyMeasurable.inf

end Order

variable [Zero β] [T2Space β]

/- warning: measure_theory.ae_fin_strongly_measurable.exists_set_sigma_finite -> MeasureTheory.AEFinStronglyMeasurable.exists_set_sigmaFinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_3 : Zero.{u2} β] [_inst_4 : T2Space.{u2} β _inst_2], (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m f μ) -> (Exists.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (MeasurableSet.{u1} α m t) (And (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))) f (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_3)))))) (MeasureTheory.SigmaFinite.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ t)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} [_inst_3 : Zero.{u1} β] [_inst_4 : T2Space.{u1} β _inst_2], (MeasureTheory.AEFinStronglyMeasurable.{u2, u1} α β _inst_2 _inst_3 m f μ) -> (Exists.{succ u2} (Set.{u2} α) (fun (t : Set.{u2} α) => And (MeasurableSet.{u2} α m t) (And (Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α m (MeasureTheory.Measure.restrict.{u2} α m μ (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) t))) f (OfNat.ofNat.{max u2 u1} (α -> β) 0 (Zero.toOfNat0.{max u2 u1} (α -> β) (Pi.instZero.{u2, u1} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19136 : α) => β) (fun (i : α) => _inst_3))))) (MeasureTheory.SigmaFinite.{u2} α m (MeasureTheory.Measure.restrict.{u2} α m μ t)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable.exists_set_sigma_finite MeasureTheory.AEFinStronglyMeasurable.exists_set_sigmaFiniteₓ'. -/
theorem exists_set_sigmaFinite (hf : AEFinStronglyMeasurable f μ) :
    ∃ t, MeasurableSet t ∧ f =ᵐ[μ.restrict (tᶜ)] 0 ∧ SigmaFinite (μ.restrict t) :=
  by
  rcases hf with ⟨g, hg, hfg⟩
  obtain ⟨t, ht, hgt_zero, htμ⟩ := hg.exists_set_sigma_finite
  refine' ⟨t, ht, _, htμ⟩
  refine' eventually_eq.trans (ae_restrict_of_ae hfg) _
  rw [eventually_eq, ae_restrict_iff' ht.compl]
  exact eventually_of_forall hgt_zero
#align measure_theory.ae_fin_strongly_measurable.exists_set_sigma_finite MeasureTheory.AEFinStronglyMeasurable.exists_set_sigmaFinite

#print MeasureTheory.AEFinStronglyMeasurable.sigmaFiniteSet /-
/-- A measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0` and `sigma_finite (μ.restrict t)`. -/
def sigmaFiniteSet (hf : AEFinStronglyMeasurable f μ) : Set α :=
  hf.exists_set_sigmaFinite.some
#align measure_theory.ae_fin_strongly_measurable.sigma_finite_set MeasureTheory.AEFinStronglyMeasurable.sigmaFiniteSet
-/

/- warning: measure_theory.ae_fin_strongly_measurable.measurable_set -> MeasureTheory.AEFinStronglyMeasurable.measurableSet is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_3 : Zero.{u2} β] [_inst_4 : T2Space.{u2} β _inst_2] (hf : MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m f μ), MeasurableSet.{u1} α m (MeasureTheory.AEFinStronglyMeasurable.sigmaFiniteSet.{u1, u2} α β m μ _inst_2 f _inst_3 _inst_4 hf)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} [_inst_3 : Zero.{u1} β] [_inst_4 : T2Space.{u1} β _inst_2] (hf : MeasureTheory.AEFinStronglyMeasurable.{u2, u1} α β _inst_2 _inst_3 m f μ), MeasurableSet.{u2} α m (MeasureTheory.AEFinStronglyMeasurable.sigmaFiniteSet.{u2, u1} α β m μ _inst_2 f _inst_3 _inst_4 hf)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable.measurable_set MeasureTheory.AEFinStronglyMeasurable.measurableSetₓ'. -/
protected theorem measurableSet (hf : AEFinStronglyMeasurable f μ) :
    MeasurableSet hf.sigmaFiniteSet :=
  hf.exists_set_sigmaFinite.choose_spec.1
#align measure_theory.ae_fin_strongly_measurable.measurable_set MeasureTheory.AEFinStronglyMeasurable.measurableSet

/- warning: measure_theory.ae_fin_strongly_measurable.ae_eq_zero_compl -> MeasureTheory.AEFinStronglyMeasurable.ae_eq_zero_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} [_inst_3 : Zero.{u2} β] [_inst_4 : T2Space.{u2} β _inst_2] (hf : MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α β _inst_2 _inst_3 m f μ), Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α m (MeasureTheory.Measure.restrict.{u1} α m μ (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (MeasureTheory.AEFinStronglyMeasurable.sigmaFiniteSet.{u1, u2} α β m μ _inst_2 f _inst_3 _inst_4 hf)))) f (OfNat.ofNat.{max u1 u2} (α -> β) 0 (OfNat.mk.{max u1 u2} (α -> β) 0 (Zero.zero.{max u1 u2} (α -> β) (Pi.instZero.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_3)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} [_inst_3 : Zero.{u1} β] [_inst_4 : T2Space.{u1} β _inst_2] (hf : MeasureTheory.AEFinStronglyMeasurable.{u2, u1} α β _inst_2 _inst_3 m f μ), Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α m (MeasureTheory.Measure.restrict.{u2} α m μ (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) (MeasureTheory.AEFinStronglyMeasurable.sigmaFiniteSet.{u2, u1} α β m μ _inst_2 f _inst_3 _inst_4 hf)))) f (OfNat.ofNat.{max u2 u1} (α -> β) 0 (Zero.toOfNat0.{max u2 u1} (α -> β) (Pi.instZero.{u2, u1} α (fun (a._@.Mathlib.Order.Filter.Basic._hyg.19136 : α) => β) (fun (i : α) => _inst_3))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable.ae_eq_zero_compl MeasureTheory.AEFinStronglyMeasurable.ae_eq_zero_complₓ'. -/
theorem ae_eq_zero_compl (hf : AEFinStronglyMeasurable f μ) :
    f =ᵐ[μ.restrict (hf.sigmaFiniteSetᶜ)] 0 :=
  hf.exists_set_sigmaFinite.choose_spec.2.1
#align measure_theory.ae_fin_strongly_measurable.ae_eq_zero_compl MeasureTheory.AEFinStronglyMeasurable.ae_eq_zero_compl

#print MeasureTheory.AEFinStronglyMeasurable.sigmaFinite_restrict /-
instance sigmaFinite_restrict (hf : AEFinStronglyMeasurable f μ) :
    SigmaFinite (μ.restrict hf.sigmaFiniteSet) :=
  hf.exists_set_sigmaFinite.choose_spec.2.2
#align measure_theory.ae_fin_strongly_measurable.sigma_finite_restrict MeasureTheory.AEFinStronglyMeasurable.sigmaFinite_restrict
-/

end AeFinStronglyMeasurable

section SecondCountableTopology

variable {G : Type _} {p : ℝ≥0∞} {m m0 : MeasurableSpace α} {μ : Measure α}
  [SeminormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {f : α → G}

/- warning: measure_theory.fin_strongly_measurable_iff_measurable -> MeasureTheory.finStronglyMeasurable_iff_measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} G] [_inst_3 : MeasurableSpace.{u2} G] [_inst_4 : BorelSpace.{u2} G (UniformSpace.toTopologicalSpace.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_2))) _inst_3] [_inst_5 : TopologicalSpace.SecondCountableTopology.{u2} G (UniformSpace.toTopologicalSpace.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_2)))] {f : α -> G} {m0 : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m0) [_inst_6 : MeasureTheory.SigmaFinite.{u1} α m0 μ], Iff (MeasureTheory.FinStronglyMeasurable.{u1, u2} α G (UniformSpace.toTopologicalSpace.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_2))) (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G (SeminormedAddGroup.toAddGroup.{u2} G (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} G _inst_2)))))) m0 f μ) (Measurable.{u1, u2} α G m0 _inst_3 f)
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} G] [_inst_3 : MeasurableSpace.{u1} G] [_inst_4 : BorelSpace.{u1} G (UniformSpace.toTopologicalSpace.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_2))) _inst_3] [_inst_5 : TopologicalSpace.SecondCountableTopology.{u1} G (UniformSpace.toTopologicalSpace.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_2)))] {f : α -> G} {m0 : MeasurableSpace.{u2} α} (μ : MeasureTheory.Measure.{u2} α m0) [_inst_6 : MeasureTheory.SigmaFinite.{u2} α m0 μ], Iff (MeasureTheory.FinStronglyMeasurable.{u2, u1} α G (UniformSpace.toTopologicalSpace.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_2))) (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (SeminormedAddCommGroup.toAddCommGroup.{u1} G _inst_2)))))) m0 f μ) (Measurable.{u2, u1} α G m0 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align measure_theory.fin_strongly_measurable_iff_measurable MeasureTheory.finStronglyMeasurable_iff_measurableₓ'. -/
/-- In a space with second countable topology and a sigma-finite measure, `fin_strongly_measurable`
  and `measurable` are equivalent. -/
theorem finStronglyMeasurable_iff_measurable {m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] : FinStronglyMeasurable f μ ↔ Measurable f :=
  ⟨fun h => h.Measurable, fun h => (Measurable.stronglyMeasurable h).FinStronglyMeasurable μ⟩
#align measure_theory.fin_strongly_measurable_iff_measurable MeasureTheory.finStronglyMeasurable_iff_measurable

/- warning: measure_theory.ae_fin_strongly_measurable_iff_ae_measurable -> MeasureTheory.aefinStronglyMeasurable_iff_aemeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {G : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} G] [_inst_3 : MeasurableSpace.{u2} G] [_inst_4 : BorelSpace.{u2} G (UniformSpace.toTopologicalSpace.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_2))) _inst_3] [_inst_5 : TopologicalSpace.SecondCountableTopology.{u2} G (UniformSpace.toTopologicalSpace.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_2)))] {f : α -> G} {m0 : MeasurableSpace.{u1} α} (μ : MeasureTheory.Measure.{u1} α m0) [_inst_6 : MeasureTheory.SigmaFinite.{u1} α m0 μ], Iff (MeasureTheory.AEFinStronglyMeasurable.{u1, u2} α G (UniformSpace.toTopologicalSpace.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_2))) (AddZeroClass.toHasZero.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G (SeminormedAddGroup.toAddGroup.{u2} G (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} G _inst_2)))))) m0 f μ) (AEMeasurable.{u1, u2} α G _inst_3 m0 f μ)
but is expected to have type
  forall {α : Type.{u2}} {G : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} G] [_inst_3 : MeasurableSpace.{u1} G] [_inst_4 : BorelSpace.{u1} G (UniformSpace.toTopologicalSpace.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_2))) _inst_3] [_inst_5 : TopologicalSpace.SecondCountableTopology.{u1} G (UniformSpace.toTopologicalSpace.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_2)))] {f : α -> G} {m0 : MeasurableSpace.{u2} α} (μ : MeasureTheory.Measure.{u2} α m0) [_inst_6 : MeasureTheory.SigmaFinite.{u2} α m0 μ], Iff (MeasureTheory.AEFinStronglyMeasurable.{u2, u1} α G (UniformSpace.toTopologicalSpace.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_2))) (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (SubtractionCommMonoid.toSubtractionMonoid.{u1} G (AddCommGroup.toDivisionAddCommMonoid.{u1} G (SeminormedAddCommGroup.toAddCommGroup.{u1} G _inst_2)))))) m0 f μ) (AEMeasurable.{u2, u1} α G _inst_3 m0 f μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_fin_strongly_measurable_iff_ae_measurable MeasureTheory.aefinStronglyMeasurable_iff_aemeasurableₓ'. -/
/-- In a space with second countable topology and a sigma-finite measure,
  `ae_fin_strongly_measurable` and `ae_measurable` are equivalent. -/
theorem aefinStronglyMeasurable_iff_aemeasurable {m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] : AEFinStronglyMeasurable f μ ↔ AEMeasurable f μ := by
  simp_rw [ae_fin_strongly_measurable, AEMeasurable, fin_strongly_measurable_iff_measurable]
#align measure_theory.ae_fin_strongly_measurable_iff_ae_measurable MeasureTheory.aefinStronglyMeasurable_iff_aemeasurable

end SecondCountableTopology

/- warning: measure_theory.measurable_uncurry_of_continuous_of_measurable -> MeasureTheory.measurable_uncurry_of_continuous_of_measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_2 : TopologicalSpace.{u3} ι] [_inst_3 : TopologicalSpace.MetrizableSpace.{u3} ι _inst_2] [_inst_4 : MeasurableSpace.{u3} ι] [_inst_5 : TopologicalSpace.SecondCountableTopology.{u3} ι _inst_2] [_inst_6 : OpensMeasurableSpace.{u3} ι _inst_2 _inst_4] {mβ : MeasurableSpace.{u2} β} [_inst_7 : TopologicalSpace.{u2} β] [_inst_8 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_7] [_inst_9 : BorelSpace.{u2} β _inst_7 mβ] {m : MeasurableSpace.{u1} α} {u : ι -> α -> β}, (forall (x : α), Continuous.{u3, u2} ι β _inst_2 _inst_7 (fun (i : ι) => u i x)) -> (forall (i : ι), Measurable.{u1, u2} α β m mβ (u i)) -> (Measurable.{max u3 u1, u2} (Prod.{u3, u1} ι α) β (Prod.instMeasurableSpace.{u3, u1} ι α _inst_4 m) mβ (Function.uncurry.{u3, u1, u2} ι α β u))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} ι] [_inst_3 : TopologicalSpace.MetrizableSpace.{u1} ι _inst_2] [_inst_4 : MeasurableSpace.{u1} ι] [_inst_5 : TopologicalSpace.SecondCountableTopology.{u1} ι _inst_2] [_inst_6 : OpensMeasurableSpace.{u1} ι _inst_2 _inst_4] {mβ : MeasurableSpace.{u2} β} [_inst_7 : TopologicalSpace.{u2} β] [_inst_8 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_7] [_inst_9 : BorelSpace.{u2} β _inst_7 mβ] {m : MeasurableSpace.{u3} α} {u : ι -> α -> β}, (forall (x : α), Continuous.{u1, u2} ι β _inst_2 _inst_7 (fun (i : ι) => u i x)) -> (forall (i : ι), Measurable.{u3, u2} α β m mβ (u i)) -> (Measurable.{max u3 u1, u2} (Prod.{u1, u3} ι α) β (Prod.instMeasurableSpace.{u1, u3} ι α _inst_4 m) mβ (Function.uncurry.{u1, u3, u2} ι α β u))
Case conversion may be inaccurate. Consider using '#align measure_theory.measurable_uncurry_of_continuous_of_measurable MeasureTheory.measurable_uncurry_of_continuous_of_measurableₓ'. -/
theorem measurable_uncurry_of_continuous_of_measurable {α β ι : Type _} [TopologicalSpace ι]
    [MetrizableSpace ι] [MeasurableSpace ι] [SecondCountableTopology ι] [OpensMeasurableSpace ι]
    {mβ : MeasurableSpace β} [TopologicalSpace β] [PseudoMetrizableSpace β] [BorelSpace β]
    {m : MeasurableSpace α} {u : ι → α → β} (hu_cont : ∀ x, Continuous fun i => u i x)
    (h : ∀ i, Measurable (u i)) : Measurable (Function.uncurry u) :=
  by
  obtain ⟨t_sf, ht_sf⟩ :
    ∃ t : ℕ → simple_func ι ι, ∀ j x, tendsto (fun n => u (t n j) x) at_top (𝓝 <| u j x) :=
    by
    have h_str_meas : strongly_measurable (id : ι → ι) := stronglyMeasurable_id
    refine' ⟨h_str_meas.approx, fun j x => _⟩
    exact ((hu_cont x).Tendsto j).comp (h_str_meas.tendsto_approx j)
  let U (n : ℕ) (p : ι × α) := u (t_sf n p.fst) p.snd
  have h_tendsto : tendsto U at_top (𝓝 fun p => u p.fst p.snd) :=
    by
    rw [tendsto_pi_nhds]
    exact fun p => ht_sf p.fst p.snd
  refine' measurable_of_tendsto_metrizable (fun n => _) h_tendsto
  have h_meas : Measurable fun p : (t_sf n).range × α => u (↑p.fst) p.snd :=
    by
    have :
      (fun p : ↥(t_sf n).range × α => u (↑p.fst) p.snd) =
        (fun p : α × (t_sf n).range => u (↑p.snd) p.fst) ∘ Prod.swap :=
      rfl
    rw [this, @measurable_swap_iff α (↥(t_sf n).range) β m]
    exact measurable_from_prod_countable fun j => h j
  have :
    (fun p : ι × α => u (t_sf n p.fst) p.snd) =
      (fun p : ↥(t_sf n).range × α => u p.fst p.snd) ∘ fun p : ι × α =>
        (⟨t_sf n p.fst, simple_func.mem_range_self _ _⟩, p.snd) :=
    rfl
  simp_rw [U, this]
  refine' h_meas.comp (Measurable.prod_mk _ measurable_snd)
  exact ((t_sf n).Measurable.comp measurable_fst).subtype_mk
#align measure_theory.measurable_uncurry_of_continuous_of_measurable MeasureTheory.measurable_uncurry_of_continuous_of_measurable

/- warning: measure_theory.strongly_measurable_uncurry_of_continuous_of_strongly_measurable -> MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} [_inst_2 : TopologicalSpace.{u3} ι] [_inst_3 : TopologicalSpace.MetrizableSpace.{u3} ι _inst_2] [_inst_4 : MeasurableSpace.{u3} ι] [_inst_5 : TopologicalSpace.SecondCountableTopology.{u3} ι _inst_2] [_inst_6 : OpensMeasurableSpace.{u3} ι _inst_2 _inst_4] [_inst_7 : TopologicalSpace.{u2} β] [_inst_8 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_7] [_inst_9 : MeasurableSpace.{u1} α] {u : ι -> α -> β}, (forall (x : α), Continuous.{u3, u2} ι β _inst_2 _inst_7 (fun (i : ι) => u i x)) -> (forall (i : ι), MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_7 _inst_9 (u i)) -> (MeasureTheory.StronglyMeasurable.{max u3 u1, u2} (Prod.{u3, u1} ι α) β _inst_7 (Prod.instMeasurableSpace.{u3, u1} ι α _inst_4 _inst_9) (Function.uncurry.{u3, u1, u2} ι α β u))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} ι] [_inst_3 : TopologicalSpace.MetrizableSpace.{u1} ι _inst_2] [_inst_4 : MeasurableSpace.{u1} ι] [_inst_5 : TopologicalSpace.SecondCountableTopology.{u1} ι _inst_2] [_inst_6 : OpensMeasurableSpace.{u1} ι _inst_2 _inst_4] [_inst_7 : TopologicalSpace.{u2} β] [_inst_8 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_7] [_inst_9 : MeasurableSpace.{u3} α] {u : ι -> α -> β}, (forall (x : α), Continuous.{u1, u2} ι β _inst_2 _inst_7 (fun (i : ι) => u i x)) -> (forall (i : ι), MeasureTheory.StronglyMeasurable.{u3, u2} α β _inst_7 _inst_9 (u i)) -> (MeasureTheory.StronglyMeasurable.{max u3 u1, u2} (Prod.{u1, u3} ι α) β _inst_7 (Prod.instMeasurableSpace.{u1, u3} ι α _inst_4 _inst_9) (Function.uncurry.{u1, u3, u2} ι α β u))
Case conversion may be inaccurate. Consider using '#align measure_theory.strongly_measurable_uncurry_of_continuous_of_strongly_measurable MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurableₓ'. -/
theorem stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable {α β ι : Type _}
    [TopologicalSpace ι] [MetrizableSpace ι] [MeasurableSpace ι] [SecondCountableTopology ι]
    [OpensMeasurableSpace ι] [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace α]
    {u : ι → α → β} (hu_cont : ∀ x, Continuous fun i => u i x) (h : ∀ i, StronglyMeasurable (u i)) :
    StronglyMeasurable (Function.uncurry u) :=
  by
  borelize β
  obtain ⟨t_sf, ht_sf⟩ :
    ∃ t : ℕ → simple_func ι ι, ∀ j x, tendsto (fun n => u (t n j) x) at_top (𝓝 <| u j x) :=
    by
    have h_str_meas : strongly_measurable (id : ι → ι) := stronglyMeasurable_id
    refine' ⟨h_str_meas.approx, fun j x => _⟩
    exact ((hu_cont x).Tendsto j).comp (h_str_meas.tendsto_approx j)
  let U (n : ℕ) (p : ι × α) := u (t_sf n p.fst) p.snd
  have h_tendsto : tendsto U at_top (𝓝 fun p => u p.fst p.snd) :=
    by
    rw [tendsto_pi_nhds]
    exact fun p => ht_sf p.fst p.snd
  refine' stronglyMeasurable_of_tendsto _ (fun n => _) h_tendsto
  have h_str_meas : strongly_measurable fun p : (t_sf n).range × α => u (↑p.fst) p.snd :=
    by
    refine' stronglyMeasurable_iff_measurable_separable.2 ⟨_, _⟩
    · have :
        (fun p : ↥(t_sf n).range × α => u (↑p.fst) p.snd) =
          (fun p : α × (t_sf n).range => u (↑p.snd) p.fst) ∘ Prod.swap :=
        rfl
      rw [this, measurable_swap_iff]
      exact measurable_from_prod_countable fun j => (h j).Measurable
    · have : IsSeparable (⋃ i : (t_sf n).range, range (u i)) :=
        is_separable_Union fun i => (h i).isSeparable_range
      apply this.mono
      rintro _ ⟨⟨i, x⟩, rfl⟩
      simp only [mem_Union, mem_range]
      exact ⟨i, x, rfl⟩
  have :
    (fun p : ι × α => u (t_sf n p.fst) p.snd) =
      (fun p : ↥(t_sf n).range × α => u p.fst p.snd) ∘ fun p : ι × α =>
        (⟨t_sf n p.fst, simple_func.mem_range_self _ _⟩, p.snd) :=
    rfl
  simp_rw [U, this]
  refine' h_str_meas.comp_measurable (Measurable.prod_mk _ measurable_snd)
  exact ((t_sf n).Measurable.comp measurable_fst).subtype_mk
#align measure_theory.strongly_measurable_uncurry_of_continuous_of_strongly_measurable MeasureTheory.stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable

end MeasureTheory

-- Guard against import creep
assert_not_exists InnerProductSpace

