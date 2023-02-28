/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module probability.kernel.basic
! leanprover-community/mathlib commit 57ac39bd365c2f80589a700f9fbb664d3a1a30c2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Constructions.Prod

/-!
# Markov Kernels

A kernel from a measurable space `α` to another measurable space `β` is a measurable map
`α → measure β`, where the measurable space instance on `measure β` is the one defined in
`measure_theory.measure.measurable_space`. That is, a kernel `κ` verifies that for all measurable
sets `s` of `β`, `a ↦ κ a s` is measurable.

## Main definitions

Classes of kernels:
* `kernel α β`: kernels from `α` to `β`, defined as the `add_submonoid` of the measurable
  functions in `α → measure β`.
* `is_markov_kernel κ`: a kernel from `α` to `β` is said to be a Markov kernel if for all `a : α`,
  `k a` is a probability measure.
* `is_finite_kernel κ`: a kernel from `α` to `β` is said to be finite if there exists `C : ℝ≥0∞`
  such that `C < ∞` and for all `a : α`, `κ a univ ≤ C`. This implies in particular that all
  measures in the image of `κ` are finite, but is stronger since it requires an uniform bound. This
  stronger condition is necessary to ensure that the composition of two finite kernels is finite.
* `is_s_finite_kernel κ`: a kernel is called s-finite if it is a countable sum of finite kernels.

Particular kernels:
* `deterministic {f : α → β} (hf : measurable f)`: kernel `a ↦ measure.dirac (f a)`.
* `const α (μβ : measure β)`: constant kernel `a ↦ μβ`.
* `kernel.restrict κ (hs : measurable_set s)`: kernel for which the image of `a : α` is
  `(κ a).restrict s`.
  Integral: `∫⁻ b, f b ∂(kernel.restrict κ hs a) = ∫⁻ b in s, f b ∂(κ a)`
* `kernel.with_density κ (f : α → β → ℝ≥0∞)`: kernel `a ↦ (κ a).with_density (f a)`.
  It is defined if `κ` is s-finite. If `f` is finite everywhere, then this is also an s-finite
  kernel. The class of s-finite kernels is the smallest class of kernels that contains finite
  kernels and which is stable by `with_density`.
  Integral: `∫⁻ b, g b ∂(with_density κ f a) = ∫⁻ b, f a b * g b ∂(κ a)`

## Main statements

* `ext_fun`: if `∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)` for all measurable functions `f` and all `a`,
  then the two kernels `κ` and `η` are equal.

* `measurable_lintegral`: the function `a ↦ ∫⁻ b, f a b ∂(κ a)` is measurable, for an s-finite
  kernel `κ : kernel α β` and a function `f : α → β → ℝ≥0∞` such that `function.uncurry f`
  is measurable.

-/


open MeasureTheory

open MeasureTheory ENNReal NNReal BigOperators

namespace ProbabilityTheory

/-- A kernel from a measurable space `α` to another measurable space `β` is a measurable function
`κ : α → measure β`. The measurable space structure on `measure β` is given by
`measure_theory.measure.measurable_space`. A map `κ : α → measure β` is measurable iff
`∀ s : set β, measurable_set s → measurable (λ a, κ a s)`. -/
def kernel (α β : Type _) [MeasurableSpace α] [MeasurableSpace β] : AddSubmonoid (α → Measure β)
    where
  carrier := Measurable
  zero_mem' := measurable_zero
  add_mem' f g hf hg := Measurable.add hf hg
#align probability_theory.kernel ProbabilityTheory.kernel

instance {α β : Type _} [MeasurableSpace α] [MeasurableSpace β] :
    CoeFun (kernel α β) fun _ => α → Measure β :=
  ⟨fun κ => κ.val⟩

variable {α β ι : Type _} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

include mα mβ

namespace Kernel

@[simp]
theorem coeFn_zero : ⇑(0 : kernel α β) = 0 :=
  rfl
#align probability_theory.kernel.coe_fn_zero ProbabilityTheory.kernel.coeFn_zero

@[simp]
theorem coeFn_add (κ η : kernel α β) : ⇑(κ + η) = κ + η :=
  rfl
#align probability_theory.kernel.coe_fn_add ProbabilityTheory.kernel.coeFn_add

omit mα mβ

/-- Coercion to a function as an additive monoid homomorphism. -/
def coeAddHom (α β : Type _) [MeasurableSpace α] [MeasurableSpace β] :
    kernel α β →+ α → Measure β :=
  ⟨coeFn, coeFn_zero, coeFn_add⟩
#align probability_theory.kernel.coe_add_hom ProbabilityTheory.kernel.coeAddHom

include mα mβ

@[simp]
theorem zero_apply (a : α) : (0 : kernel α β) a = 0 :=
  rfl
#align probability_theory.kernel.zero_apply ProbabilityTheory.kernel.zero_apply

@[simp]
theorem coe_finset_sum (I : Finset ι) (κ : ι → kernel α β) : ⇑(∑ i in I, κ i) = ∑ i in I, κ i :=
  (coeAddHom α β).map_sum _ _
#align probability_theory.kernel.coe_finset_sum ProbabilityTheory.kernel.coe_finset_sum

theorem finset_sum_apply (I : Finset ι) (κ : ι → kernel α β) (a : α) :
    (∑ i in I, κ i) a = ∑ i in I, κ i a := by rw [coe_finset_sum, Finset.sum_apply]
#align probability_theory.kernel.finset_sum_apply ProbabilityTheory.kernel.finset_sum_apply

theorem finset_sum_apply' (I : Finset ι) (κ : ι → kernel α β) (a : α) (s : Set β) :
    (∑ i in I, κ i) a s = ∑ i in I, κ i a s := by rw [finset_sum_apply, measure.finset_sum_apply]
#align probability_theory.kernel.finset_sum_apply' ProbabilityTheory.kernel.finset_sum_apply'

end Kernel

/-- A kernel is a Markov kernel if every measure in its image is a probability measure. -/
class IsMarkovKernel (κ : kernel α β) : Prop where
  IsProbabilityMeasure : ∀ a, IsProbabilityMeasure (κ a)
#align probability_theory.is_markov_kernel ProbabilityTheory.IsMarkovKernel

/-- A kernel is finite if every measure in its image is finite, with a uniform bound. -/
class IsFiniteKernel (κ : kernel α β) : Prop where
  exists_univ_le : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a Set.univ ≤ C
#align probability_theory.is_finite_kernel ProbabilityTheory.IsFiniteKernel

/-- A constant `C : ℝ≥0∞` such that `C < ∞` (`is_finite_kernel.bound_lt_top κ`) and for all
`a : α` and `s : set β`, `κ a s ≤ C` (`measure_le_bound κ a s`). -/
noncomputable def IsFiniteKernel.bound (κ : kernel α β) [h : IsFiniteKernel κ] : ℝ≥0∞ :=
  h.exists_univ_le.some
#align probability_theory.is_finite_kernel.bound ProbabilityTheory.IsFiniteKernel.bound

theorem IsFiniteKernel.bound_lt_top (κ : kernel α β) [h : IsFiniteKernel κ] :
    IsFiniteKernel.bound κ < ∞ :=
  h.exists_univ_le.choose_spec.1
#align probability_theory.is_finite_kernel.bound_lt_top ProbabilityTheory.IsFiniteKernel.bound_lt_top

theorem IsFiniteKernel.bound_ne_top (κ : kernel α β) [h : IsFiniteKernel κ] :
    IsFiniteKernel.bound κ ≠ ∞ :=
  (IsFiniteKernel.bound_lt_top κ).Ne
#align probability_theory.is_finite_kernel.bound_ne_top ProbabilityTheory.IsFiniteKernel.bound_ne_top

theorem kernel.measure_le_bound (κ : kernel α β) [h : IsFiniteKernel κ] (a : α) (s : Set β) :
    κ a s ≤ IsFiniteKernel.bound κ :=
  (measure_mono (Set.subset_univ s)).trans (h.exists_univ_le.choose_spec.2 a)
#align probability_theory.kernel.measure_le_bound ProbabilityTheory.kernel.measure_le_bound

instance isFiniteKernelZero (α β : Type _) {mα : MeasurableSpace α} {mβ : MeasurableSpace β} :
    IsFiniteKernel (0 : kernel α β) :=
  ⟨⟨0, ENNReal.coe_lt_top, fun a => by
      simp only [kernel.zero_apply, measure.coe_zero, Pi.zero_apply, le_zero_iff]⟩⟩
#align probability_theory.is_finite_kernel_zero ProbabilityTheory.isFiniteKernelZero

instance IsFiniteKernel.add (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (κ + η) :=
  by
  refine'
    ⟨⟨is_finite_kernel.bound κ + is_finite_kernel.bound η,
        ennreal.add_lt_top.mpr ⟨is_finite_kernel.bound_lt_top κ, is_finite_kernel.bound_lt_top η⟩,
        fun a => _⟩⟩
  simp_rw [kernel.coe_fn_add, Pi.add_apply, measure.coe_add, Pi.add_apply]
  exact add_le_add (kernel.measure_le_bound _ _ _) (kernel.measure_le_bound _ _ _)
#align probability_theory.is_finite_kernel.add ProbabilityTheory.IsFiniteKernel.add

variable {κ : kernel α β}

instance IsMarkovKernel.isProbabilityMeasure' [h : IsMarkovKernel κ] (a : α) :
    IsProbabilityMeasure (κ a) :=
  IsMarkovKernel.isProbabilityMeasure a
#align probability_theory.is_markov_kernel.is_probability_measure' ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure'

instance IsFiniteKernel.isFiniteMeasure [h : IsFiniteKernel κ] (a : α) : IsFiniteMeasure (κ a) :=
  ⟨(kernel.measure_le_bound κ a Set.univ).trans_lt (IsFiniteKernel.bound_lt_top κ)⟩
#align probability_theory.is_finite_kernel.is_finite_measure ProbabilityTheory.IsFiniteKernel.isFiniteMeasure

instance (priority := 100) IsMarkovKernel.isFiniteKernel [h : IsMarkovKernel κ] :
    IsFiniteKernel κ :=
  ⟨⟨1, ENNReal.one_lt_top, fun a => prob_le_one⟩⟩
#align probability_theory.is_markov_kernel.is_finite_kernel ProbabilityTheory.IsMarkovKernel.isFiniteKernel

namespace Kernel

@[ext]
theorem ext {κ : kernel α β} {η : kernel α β} (h : ∀ a, κ a = η a) : κ = η :=
  by
  ext1
  ext1 a
  exact h a
#align probability_theory.kernel.ext ProbabilityTheory.kernel.ext

theorem ext_fun {κ η : kernel α β} (h : ∀ a f, Measurable f → (∫⁻ b, f b ∂κ a) = ∫⁻ b, f b ∂η a) :
    κ = η := by
  ext (a s hs)
  specialize h a (s.indicator fun _ => 1) (Measurable.indicator measurable_const hs)
  simp_rw [lintegral_indicator_const hs, one_mul] at h
  rw [h]
#align probability_theory.kernel.ext_fun ProbabilityTheory.kernel.ext_fun

protected theorem measurable (κ : kernel α β) : Measurable κ :=
  κ.Prop
#align probability_theory.kernel.measurable ProbabilityTheory.kernel.measurable

protected theorem measurable_coe (κ : kernel α β) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => κ a s :=
  (Measure.measurable_coe hs).comp (kernel.measurable κ)
#align probability_theory.kernel.measurable_coe ProbabilityTheory.kernel.measurable_coe

section Sum

/-- Sum of an indexed family of kernels. -/
protected noncomputable def sum [Countable ι] (κ : ι → kernel α β) : kernel α β
    where
  val a := Measure.sum fun n => κ n a
  property := by
    refine' measure.measurable_of_measurable_coe _ fun s hs => _
    simp_rw [measure.sum_apply _ hs]
    exact Measurable.eNNReal_tsum fun n => kernel.measurable_coe (κ n) hs
#align probability_theory.kernel.sum ProbabilityTheory.kernel.sum

theorem sum_apply [Countable ι] (κ : ι → kernel α β) (a : α) :
    kernel.sum κ a = Measure.sum fun n => κ n a :=
  rfl
#align probability_theory.kernel.sum_apply ProbabilityTheory.kernel.sum_apply

theorem sum_apply' [Countable ι] (κ : ι → kernel α β) (a : α) {s : Set β} (hs : MeasurableSet s) :
    kernel.sum κ a s = ∑' n, κ n a s := by rw [sum_apply κ a, measure.sum_apply _ hs]
#align probability_theory.kernel.sum_apply' ProbabilityTheory.kernel.sum_apply'

@[simp]
theorem sum_zero [Countable ι] : (kernel.sum fun i : ι => (0 : kernel α β)) = 0 :=
  by
  ext (a s hs) : 2
  rw [sum_apply' _ a hs]
  simp only [zero_apply, measure.coe_zero, Pi.zero_apply, tsum_zero]
#align probability_theory.kernel.sum_zero ProbabilityTheory.kernel.sum_zero

theorem sum_comm [Countable ι] (κ : ι → ι → kernel α β) :
    (kernel.sum fun n => kernel.sum (κ n)) = kernel.sum fun m => kernel.sum fun n => κ n m :=
  by
  ext (a s hs)
  simp_rw [sum_apply]
  rw [measure.sum_comm]
#align probability_theory.kernel.sum_comm ProbabilityTheory.kernel.sum_comm

@[simp]
theorem sum_fintype [Fintype ι] (κ : ι → kernel α β) : kernel.sum κ = ∑ i, κ i :=
  by
  ext (a s hs)
  simp only [sum_apply' κ a hs, finset_sum_apply' _ κ a s, tsum_fintype]
#align probability_theory.kernel.sum_fintype ProbabilityTheory.kernel.sum_fintype

theorem sum_add [Countable ι] (κ η : ι → kernel α β) :
    (kernel.sum fun n => κ n + η n) = kernel.sum κ + kernel.sum η :=
  by
  ext (a s hs)
  simp only [coe_fn_add, Pi.add_apply, sum_apply, measure.sum_apply _ hs, Pi.add_apply,
    measure.coe_add, tsum_add ENNReal.summable ENNReal.summable]
#align probability_theory.kernel.sum_add ProbabilityTheory.kernel.sum_add

end Sum

section SFinite

/-- A kernel is s-finite if it can be written as the sum of countably many finite kernels. -/
class IsSFiniteKernel (κ : kernel α β) : Prop where
  tsum_finite : ∃ κs : ℕ → kernel α β, (∀ n, IsFiniteKernel (κs n)) ∧ κ = kernel.sum κs
#align probability_theory.kernel.is_s_finite_kernel ProbabilityTheory.kernel.IsSFiniteKernel

instance (priority := 100) IsFiniteKernel.isSFiniteKernel [h : IsFiniteKernel κ] :
    IsSFiniteKernel κ :=
  ⟨⟨fun n => if n = 0 then κ else 0, fun n => by
      split_ifs
      exact h
      infer_instance, by
      ext (a s hs)
      rw [kernel.sum_apply' _ _ hs]
      have : (fun i => ((ite (i = 0) κ 0) a) s) = fun i => ite (i = 0) (κ a s) 0 :=
        by
        ext1 i
        split_ifs <;> rfl
      rw [this, tsum_ite_eq]⟩⟩
#align probability_theory.kernel.is_finite_kernel.is_s_finite_kernel ProbabilityTheory.kernel.IsFiniteKernel.isSFiniteKernel

/-- A sequence of finite kernels such that `κ = kernel.sum (seq κ)`. See `is_finite_kernel_seq`
and `kernel_sum_seq`. -/
noncomputable def seq (κ : kernel α β) [h : IsSFiniteKernel κ] : ℕ → kernel α β :=
  h.tsum_finite.some
#align probability_theory.kernel.seq ProbabilityTheory.kernel.seq

theorem kernel_sum_seq (κ : kernel α β) [h : IsSFiniteKernel κ] : kernel.sum (seq κ) = κ :=
  h.tsum_finite.choose_spec.2.symm
#align probability_theory.kernel.kernel_sum_seq ProbabilityTheory.kernel.kernel_sum_seq

theorem measure_sum_seq (κ : kernel α β) [h : IsSFiniteKernel κ] (a : α) :
    (Measure.sum fun n => seq κ n a) = κ a := by rw [← kernel.sum_apply, kernel_sum_seq κ]
#align probability_theory.kernel.measure_sum_seq ProbabilityTheory.kernel.measure_sum_seq

instance isFiniteKernelSeq (κ : kernel α β) [h : IsSFiniteKernel κ] (n : ℕ) :
    IsFiniteKernel (kernel.seq κ n) :=
  h.tsum_finite.choose_spec.1 n
#align probability_theory.kernel.is_finite_kernel_seq ProbabilityTheory.kernel.isFiniteKernelSeq

instance IsSFiniteKernel.add (κ η : kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    IsSFiniteKernel (κ + η) :=
  by
  refine' ⟨⟨fun n => seq κ n + seq η n, fun n => inferInstance, _⟩⟩
  rw [sum_add, kernel_sum_seq κ, kernel_sum_seq η]
#align probability_theory.kernel.is_s_finite_kernel.add ProbabilityTheory.kernel.IsSFiniteKernel.add

theorem IsSFiniteKernel.finsetSum {κs : ι → kernel α β} (I : Finset ι)
    (h : ∀ i ∈ I, IsSFiniteKernel (κs i)) : IsSFiniteKernel (∑ i in I, κs i) := by
  classical
    induction' I using Finset.induction with i I hi_nmem_I h_ind h
    · rw [Finset.sum_empty]
      infer_instance
    · rw [Finset.sum_insert hi_nmem_I]
      haveI : is_s_finite_kernel (κs i) := h i (Finset.mem_insert_self _ _)
      have : is_s_finite_kernel (∑ x : ι in I, κs x) :=
        h_ind fun i hiI => h i (Finset.mem_insert_of_mem hiI)
      exact is_s_finite_kernel.add _ _
#align probability_theory.kernel.is_s_finite_kernel.finset_sum ProbabilityTheory.kernel.IsSFiniteKernel.finsetSum

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i m) -/
theorem isSFiniteKernelSumOfDenumerable [Denumerable ι] {κs : ι → kernel α β}
    (hκs : ∀ n, IsSFiniteKernel (κs n)) : IsSFiniteKernel (kernel.sum κs) :=
  by
  let e : ℕ ≃ ι × ℕ := Denumerable.equiv₂ ℕ (ι × ℕ)
  refine' ⟨⟨fun n => seq (κs (e n).1) (e n).2, inferInstance, _⟩⟩
  have hκ_eq : kernel.sum κs = kernel.sum fun n => kernel.sum (seq (κs n)) := by
    simp_rw [kernel_sum_seq]
  ext (a s hs) : 2
  rw [hκ_eq]
  simp_rw [kernel.sum_apply' _ _ hs]
  change (∑' (i) (m), seq (κs i) m a s) = ∑' n, (fun im : ι × ℕ => seq (κs im.fst) im.snd a s) (e n)
  rw [e.tsum_eq]
  · rw [tsum_prod' ENNReal.summable fun _ => ENNReal.summable]
  · infer_instance
#align probability_theory.kernel.is_s_finite_kernel_sum_of_denumerable ProbabilityTheory.kernel.isSFiniteKernelSumOfDenumerable

theorem isSFiniteKernelSum [Countable ι] {κs : ι → kernel α β} (hκs : ∀ n, IsSFiniteKernel (κs n)) :
    IsSFiniteKernel (kernel.sum κs) :=
  by
  cases fintypeOrInfinite ι
  · rw [sum_fintype]
    exact is_s_finite_kernel.finset_sum Finset.univ fun i _ => hκs i
  haveI : Encodable ι := Encodable.ofCountable ι
  haveI : Denumerable ι := Denumerable.ofEncodableOfInfinite ι
  exact is_s_finite_kernel_sum_of_denumerable hκs
#align probability_theory.kernel.is_s_finite_kernel_sum ProbabilityTheory.kernel.isSFiniteKernelSum

end SFinite

section Deterministic

/-- Kernel which to `a` associates the dirac measure at `f a`. This is a Markov kernel. -/
noncomputable def deterministic {f : α → β} (hf : Measurable f) : kernel α β
    where
  val a := Measure.dirac (f a)
  property := by
    refine' measure.measurable_of_measurable_coe _ fun s hs => _
    simp_rw [measure.dirac_apply' _ hs]
    exact measurable_one.indicator (hf hs)
#align probability_theory.kernel.deterministic ProbabilityTheory.kernel.deterministic

theorem deterministic_apply {f : α → β} (hf : Measurable f) (a : α) :
    deterministic hf a = Measure.dirac (f a) :=
  rfl
#align probability_theory.kernel.deterministic_apply ProbabilityTheory.kernel.deterministic_apply

theorem deterministic_apply' {f : α → β} (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) : deterministic hf a s = s.indicator (fun _ => 1) (f a) :=
  by
  rw [deterministic]
  change measure.dirac (f a) s = s.indicator 1 (f a)
  simp_rw [measure.dirac_apply' _ hs]
#align probability_theory.kernel.deterministic_apply' ProbabilityTheory.kernel.deterministic_apply'

instance isMarkovKernelDeterministic {f : α → β} (hf : Measurable f) :
    IsMarkovKernel (deterministic hf) :=
  ⟨fun a => by
    rw [deterministic_apply hf]
    infer_instance⟩
#align probability_theory.kernel.is_markov_kernel_deterministic ProbabilityTheory.kernel.isMarkovKernelDeterministic

end Deterministic

section Const

omit mα mβ

/-- Constant kernel, which always returns the same measure. -/
def const (α : Type _) {β : Type _} [MeasurableSpace α] {mβ : MeasurableSpace β} (μβ : Measure β) :
    kernel α β where
  val _ := μβ
  property := Measure.measurable_of_measurable_coe _ fun s hs => measurable_const
#align probability_theory.kernel.const ProbabilityTheory.kernel.const

include mα mβ

instance isFiniteKernelConst {μβ : Measure β} [hμβ : IsFiniteMeasure μβ] :
    IsFiniteKernel (const α μβ) :=
  ⟨⟨μβ Set.univ, measure_lt_top _ _, fun a => le_rfl⟩⟩
#align probability_theory.kernel.is_finite_kernel_const ProbabilityTheory.kernel.isFiniteKernelConst

instance isMarkovKernelConst {μβ : Measure β} [hμβ : IsProbabilityMeasure μβ] :
    IsMarkovKernel (const α μβ) :=
  ⟨fun a => hμβ⟩
#align probability_theory.kernel.is_markov_kernel_const ProbabilityTheory.kernel.isMarkovKernelConst

end Const

omit mα

/-- In a countable space with measurable singletons, every function `α → measure β` defines a
kernel. -/
def ofFunOfCountable [MeasurableSpace α] {mβ : MeasurableSpace β} [Countable α]
    [MeasurableSingletonClass α] (f : α → Measure β) : kernel α β
    where
  val := f
  property := measurable_of_countable f
#align probability_theory.kernel.of_fun_of_countable ProbabilityTheory.kernel.ofFunOfCountable

include mα

section Restrict

variable {s t : Set β}

/-- Kernel given by the restriction of the measures in the image of a kernel to a set. -/
protected noncomputable def restrict (κ : kernel α β) (hs : MeasurableSet s) : kernel α β
    where
  val a := (κ a).restrict s
  property := by
    refine' measure.measurable_of_measurable_coe _ fun t ht => _
    simp_rw [measure.restrict_apply ht]
    exact kernel.measurable_coe κ (ht.inter hs)
#align probability_theory.kernel.restrict ProbabilityTheory.kernel.restrict

theorem restrict_apply (κ : kernel α β) (hs : MeasurableSet s) (a : α) :
    kernel.restrict κ hs a = (κ a).restrict s :=
  rfl
#align probability_theory.kernel.restrict_apply ProbabilityTheory.kernel.restrict_apply

theorem restrict_apply' (κ : kernel α β) (hs : MeasurableSet s) (a : α) (ht : MeasurableSet t) :
    kernel.restrict κ hs a t = (κ a) (t ∩ s) := by
  rw [restrict_apply κ hs a, measure.restrict_apply ht]
#align probability_theory.kernel.restrict_apply' ProbabilityTheory.kernel.restrict_apply'

theorem lintegral_restrict (κ : kernel α β) (hs : MeasurableSet s) (a : α) (f : β → ℝ≥0∞) :
    (∫⁻ b, f b ∂kernel.restrict κ hs a) = ∫⁻ b in s, f b ∂κ a := by rw [restrict_apply]
#align probability_theory.kernel.lintegral_restrict ProbabilityTheory.kernel.lintegral_restrict

instance IsFiniteKernel.restrict (κ : kernel α β) [IsFiniteKernel κ] (hs : MeasurableSet s) :
    IsFiniteKernel (kernel.restrict κ hs) :=
  by
  refine' ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, fun a => _⟩⟩
  rw [restrict_apply' κ hs a MeasurableSet.univ]
  exact measure_le_bound κ a _
#align probability_theory.kernel.is_finite_kernel.restrict ProbabilityTheory.kernel.IsFiniteKernel.restrict

instance IsSFiniteKernel.restrict (κ : kernel α β) [IsSFiniteKernel κ] (hs : MeasurableSet s) :
    IsSFiniteKernel (kernel.restrict κ hs) :=
  by
  refine' ⟨⟨fun n => kernel.restrict (seq κ n) hs, inferInstance, _⟩⟩
  ext1 a
  simp_rw [sum_apply, restrict_apply, ← measure.restrict_sum _ hs, ← sum_apply, kernel_sum_seq]
#align probability_theory.kernel.is_s_finite_kernel.restrict ProbabilityTheory.kernel.IsSFiniteKernel.restrict

end Restrict

section MeasurableLintegral

/-- This is an auxiliary lemma for `measurable_prod_mk_mem`. -/
theorem measurable_prod_mk_mem_of_finite (κ : kernel α β) {t : Set (α × β)} (ht : MeasurableSet t)
    (hκs : ∀ a, IsFiniteMeasure (κ a)) : Measurable fun a => κ a { b | (a, b) ∈ t } :=
  by
  -- `t` is a measurable set in the product `α × β`: we use that the product σ-algebra is generated
  -- by boxes to prove the result by induction.
  refine' MeasurableSpace.induction_on_inter generate_from_prod.symm isPiSystem_prod _ _ _ _ ht
  ·-- case `t = ∅`
    simp only [Set.mem_empty_iff_false, Set.setOf_false, measure_empty, measurable_const]
  · -- case of a box: `t = t₁ ×ˢ t₂` for measurable sets `t₁` and `t₂`
    intro t' ht'
    simp only [Set.mem_image2, Set.mem_setOf_eq, exists_and_left] at ht'
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht'
    simp only [Set.prod_mk_mem_set_prod_eq]
    classical
      have h_eq_ite :
        (fun a => κ a { b : β | a ∈ t₁ ∧ b ∈ t₂ }) = fun a => ite (a ∈ t₁) (κ a t₂) 0 :=
        by
        ext1 a
        split_ifs
        · simp only [h, true_and_iff]
          rfl
        · simp only [h, false_and_iff, Set.setOf_false, Set.inter_empty, measure_empty]
      rw [h_eq_ite]
      exact Measurable.ite ht₁ (kernel.measurable_coe κ ht₂) measurable_const
  · -- we assume that the result is true for `t` and we prove it for `tᶜ`
    intro t' ht' h_meas
    have h_eq_sdiff : ∀ a, { b : β | (a, b) ∈ t'ᶜ } = Set.univ \ { b : β | (a, b) ∈ t' } :=
      by
      intro a
      ext1 b
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_diff, Set.mem_univ, true_and_iff]
    simp_rw [h_eq_sdiff]
    have :
      (fun a => κ a (Set.univ \ { b : β | (a, b) ∈ t' })) = fun a =>
        κ a Set.univ - κ a { b : β | (a, b) ∈ t' } :=
      by
      ext1 a
      rw [← Set.diff_inter_self_eq_diff, Set.inter_univ, measure_diff]
      · exact Set.subset_univ _
      · exact (@measurable_prod_mk_left α β _ _ a) t' ht'
      · exact measure_ne_top _ _
    rw [this]
    exact Measurable.sub (kernel.measurable_coe κ MeasurableSet.univ) h_meas
  · -- we assume that the result is true for a family of disjoint sets and prove it for their union
    intro f h_disj hf_meas hf
    have h_Union :
      (fun a => κ a { b : β | (a, b) ∈ ⋃ i, f i }) = fun a => κ a (⋃ i, { b : β | (a, b) ∈ f i }) :=
      by
      ext1 a
      congr with b
      simp only [Set.mem_unionᵢ, Set.supᵢ_eq_unionᵢ, Set.mem_setOf_eq]
      rfl
    rw [h_Union]
    have h_tsum :
      (fun a => κ a (⋃ i, { b : β | (a, b) ∈ f i })) = fun a =>
        ∑' i, κ a { b : β | (a, b) ∈ f i } :=
      by
      ext1 a
      rw [measure_Union]
      · intro i j hij s hsi hsj b hbs
        have habi : {(a, b)} ⊆ f i := by
          rw [Set.singleton_subset_iff]
          exact hsi hbs
        have habj : {(a, b)} ⊆ f j := by
          rw [Set.singleton_subset_iff]
          exact hsj hbs
        simpa only [Set.bot_eq_empty, Set.le_eq_subset, Set.singleton_subset_iff,
          Set.mem_empty_iff_false] using h_disj hij habi habj
      · exact fun i => (@measurable_prod_mk_left α β _ _ a) _ (hf_meas i)
    rw [h_tsum]
    exact Measurable.eNNReal_tsum hf
#align probability_theory.kernel.measurable_prod_mk_mem_of_finite ProbabilityTheory.kernel.measurable_prod_mk_mem_of_finite

theorem measurable_prod_mk_mem (κ : kernel α β) [IsSFiniteKernel κ] {t : Set (α × β)}
    (ht : MeasurableSet t) : Measurable fun a => κ a { b | (a, b) ∈ t } :=
  by
  rw [← kernel_sum_seq κ]
  have :
    ∀ a, kernel.sum (seq κ) a { b : β | (a, b) ∈ t } = ∑' n, seq κ n a { b : β | (a, b) ∈ t } :=
    fun a => kernel.sum_apply' _ _ (measurable_prod_mk_left ht)
  simp_rw [this]
  refine' Measurable.eNNReal_tsum fun n => _
  exact measurable_prod_mk_mem_of_finite (seq κ n) ht inferInstance
#align probability_theory.kernel.measurable_prod_mk_mem ProbabilityTheory.kernel.measurable_prod_mk_mem

theorem measurable_lintegral_indicator_const (κ : kernel α β) [IsSFiniteKernel κ] {t : Set (α × β)}
    (ht : MeasurableSet t) (c : ℝ≥0∞) :
    Measurable fun a => ∫⁻ b, t.indicator (Function.const (α × β) c) (a, b) ∂κ a :=
  by
  simp_rw [lintegral_indicator_const_comp measurable_prod_mk_left ht _]
  exact Measurable.const_mul (measurable_prod_mk_mem _ ht) c
#align probability_theory.kernel.measurable_lintegral_indicator_const ProbabilityTheory.kernel.measurable_lintegral_indicator_const

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is measurable when seen as a
map from `α × β` (hypothesis `measurable (function.uncurry f)`), the integral
`a ↦ ∫⁻ b, f a b ∂(κ a)` is measurable. -/
theorem measurable_lintegral (κ : kernel α β) [IsSFiniteKernel κ] {f : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) : Measurable fun a => ∫⁻ b, f a b ∂κ a :=
  by
  let F : ℕ → simple_func (α × β) ℝ≥0∞ := simple_func.eapprox (Function.uncurry f)
  have h : ∀ a, (⨆ n, F n a) = Function.uncurry f a :=
    simple_func.supr_eapprox_apply (Function.uncurry f) hf
  simp only [Prod.forall, Function.uncurry_apply_pair] at h
  simp_rw [← h]
  have : ∀ a, (∫⁻ b, ⨆ n, F n (a, b) ∂κ a) = ⨆ n, ∫⁻ b, F n (a, b) ∂κ a :=
    by
    intro a
    rw [lintegral_supr]
    · exact fun n => (F n).Measurable.comp measurable_prod_mk_left
    · exact fun i j hij b => simple_func.monotone_eapprox (Function.uncurry f) hij _
  simp_rw [this]
  refine' measurable_supᵢ fun n => simple_func.induction _ _ (F n)
  · intro c t ht
    simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_const,
      simple_func.coe_zero, Set.piecewise_eq_indicator]
    exact measurable_lintegral_indicator_const κ ht c
  · intro g₁ g₂ h_disj hm₁ hm₂
    simp only [simple_func.coe_add, Pi.add_apply]
    have h_add :
      (fun a => ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂κ a) =
        (fun a => ∫⁻ b, g₁ (a, b) ∂κ a) + fun a => ∫⁻ b, g₂ (a, b) ∂κ a :=
      by
      ext1 a
      rw [Pi.add_apply, lintegral_add_left (g₁.measurable.comp measurable_prod_mk_left)]
    rw [h_add]
    exact Measurable.add hm₁ hm₂
#align probability_theory.kernel.measurable_lintegral ProbabilityTheory.kernel.measurable_lintegral

theorem measurable_lintegral' (κ : kernel α β) [IsSFiniteKernel κ] {f : β → ℝ≥0∞}
    (hf : Measurable f) : Measurable fun a => ∫⁻ b, f b ∂κ a :=
  measurable_lintegral κ (hf.comp measurable_snd)
#align probability_theory.kernel.measurable_lintegral' ProbabilityTheory.kernel.measurable_lintegral'

theorem measurableSet_lintegral (κ : kernel α β) [IsSFiniteKernel κ] {f : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => ∫⁻ b in s, f a b ∂κ a :=
  by
  simp_rw [← lintegral_restrict κ hs]
  exact measurable_lintegral _ hf
#align probability_theory.kernel.measurable_set_lintegral ProbabilityTheory.kernel.measurableSet_lintegral

theorem measurableSet_lintegral' (κ : kernel α β) [IsSFiniteKernel κ] {f : β → ℝ≥0∞}
    (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => ∫⁻ b in s, f b ∂κ a :=
  measurableSet_lintegral κ (hf.comp measurable_snd) hs
#align probability_theory.kernel.measurable_set_lintegral' ProbabilityTheory.kernel.measurableSet_lintegral'

end MeasurableLintegral

section WithDensity

variable {f : α → β → ℝ≥0∞}

/-- Kernel with image `(κ a).with_density (f a)` if `function.uncurry f` is measurable, and
with image 0 otherwise. If `function.uncurry f` is measurable, it satisfies
`∫⁻ b, g b ∂(with_density κ f hf a) = ∫⁻ b, f a b * g b ∂(κ a)`. -/
noncomputable def withDensity (κ : kernel α β) [IsSFiniteKernel κ] (f : α → β → ℝ≥0∞) :
    kernel α β :=
  @dite _ (Measurable (Function.uncurry f)) (Classical.dec _)
    (fun hf =>
      ({  val := fun a => (κ a).withDensity (f a)
          property := by
            refine' measure.measurable_of_measurable_coe _ fun s hs => _
            simp_rw [with_density_apply _ hs]
            exact measurable_set_lintegral κ hf hs } :
        kernel α β))
    fun hf => 0
#align probability_theory.kernel.with_density ProbabilityTheory.kernel.withDensity

theorem withDensity_of_not_measurable (κ : kernel α β) [IsSFiniteKernel κ]
    (hf : ¬Measurable (Function.uncurry f)) : withDensity κ f = 0 := by classical exact dif_neg hf
#align probability_theory.kernel.with_density_of_not_measurable ProbabilityTheory.kernel.withDensity_of_not_measurable

protected theorem withDensity_apply (κ : kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) : withDensity κ f a = (κ a).withDensity (f a) :=
  by
  classical
    rw [with_density, dif_pos hf]
    rfl
#align probability_theory.kernel.with_density_apply ProbabilityTheory.kernel.withDensity_apply

theorem withDensity_apply' (κ : kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) {s : Set β} (hs : MeasurableSet s) :
    withDensity κ f a s = ∫⁻ b in s, f a b ∂κ a := by
  rw [kernel.with_density_apply κ hf, with_density_apply _ hs]
#align probability_theory.kernel.with_density_apply' ProbabilityTheory.kernel.withDensity_apply'

theorem lintegral_withDensity (κ : kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) (a : α) {g : β → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ b, g b ∂withDensity κ f a) = ∫⁻ b, f a b * g b ∂κ a :=
  by
  rw [kernel.with_density_apply _ hf,
    lintegral_with_density_eq_lintegral_mul _ (Measurable.of_uncurry_left hf) hg]
  simp_rw [Pi.mul_apply]
#align probability_theory.kernel.lintegral_with_density ProbabilityTheory.kernel.lintegral_withDensity

theorem withDensity_add_left (κ η : kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (f : α → β → ℝ≥0∞) : withDensity (κ + η) f = withDensity κ f + withDensity η f :=
  by
  by_cases hf : Measurable (Function.uncurry f)
  · ext (a s hs) : 2
    simp only [kernel.with_density_apply _ hf, coe_fn_add, Pi.add_apply, with_density_add_measure,
      measure.add_apply]
  · simp_rw [with_density_of_not_measurable _ hf]
    rw [zero_add]
#align probability_theory.kernel.with_density_add_left ProbabilityTheory.kernel.withDensity_add_left

theorem withDensity_kernel_sum [Countable ι] (κ : ι → kernel α β) (hκ : ∀ i, IsSFiniteKernel (κ i))
    (f : α → β → ℝ≥0∞) :
    @withDensity _ _ _ _ (kernel.sum κ) (isSFiniteKernelSum hκ) f =
      kernel.sum fun i => withDensity (κ i) f :=
  by
  by_cases hf : Measurable (Function.uncurry f)
  · ext1 a
    simp_rw [sum_apply, kernel.with_density_apply _ hf, sum_apply,
      with_density_sum (fun n => κ n a) (f a)]
  · simp_rw [with_density_of_not_measurable _ hf]
    exact sum_zero.symm
#align probability_theory.kernel.with_density_kernel_sum ProbabilityTheory.kernel.withDensity_kernel_sum

theorem withDensity_tsum [Countable ι] (κ : kernel α β) [IsSFiniteKernel κ] {f : ι → α → β → ℝ≥0∞}
    (hf : ∀ i, Measurable (Function.uncurry (f i))) :
    withDensity κ (∑' n, f n) = kernel.sum fun n => withDensity κ (f n) :=
  by
  have h_sum_a : ∀ a, Summable fun n => f n a := fun a => pi.summable.mpr fun b => ENNReal.summable
  have h_sum : Summable fun n => f n := pi.summable.mpr h_sum_a
  ext (a s hs) : 2
  rw [sum_apply' _ a hs, with_density_apply' κ _ a hs]
  swap
  · have : Function.uncurry (∑' n, f n) = ∑' n, Function.uncurry (f n) :=
      by
      ext1 p
      simp only [Function.uncurry_def]
      rw [tsum_apply h_sum, tsum_apply (h_sum_a _), tsum_apply]
      exact pi.summable.mpr fun p => ENNReal.summable
    rw [this]
    exact Measurable.eNNReal_tsum' hf
  have : (∫⁻ b in s, (∑' n, f n) a b ∂κ a) = ∫⁻ b in s, ∑' n, (fun b => f n a b) b ∂κ a :=
    by
    congr with b
    rw [tsum_apply h_sum, tsum_apply (h_sum_a a)]
  rw [this, lintegral_tsum fun n => (Measurable.of_uncurry_left (hf n)).AeMeasurable]
  congr with n
  rw [with_density_apply' _ (hf n) a hs]
#align probability_theory.kernel.with_density_tsum ProbabilityTheory.kernel.withDensity_tsum

/-- If a kernel `κ` is finite and a function `f : α → β → ℝ≥0∞` is bounded, then `with_density κ f`
is finite. -/
theorem isFiniteKernelWithDensityOfBounded (κ : kernel α β) [IsFiniteKernel κ] {B : ℝ≥0∞}
    (hB_top : B ≠ ∞) (hf_B : ∀ a b, f a b ≤ B) : IsFiniteKernel (withDensity κ f) :=
  by
  by_cases hf : Measurable (Function.uncurry f)
  ·
    exact
      ⟨⟨B * is_finite_kernel.bound κ, ENNReal.mul_lt_top hB_top (is_finite_kernel.bound_ne_top κ),
          fun a => by
          rw [with_density_apply' κ hf a MeasurableSet.univ]
          calc
            (∫⁻ b in Set.univ, f a b ∂κ a) ≤ ∫⁻ b in Set.univ, B ∂κ a := lintegral_mono (hf_B a)
            _ = B * κ a Set.univ := by simp only [measure.restrict_univ, lintegral_const]
            _ ≤ B * is_finite_kernel.bound κ := mul_le_mul_left' (measure_le_bound κ a Set.univ) _
            ⟩⟩
  · rw [with_density_of_not_measurable _ hf]
    infer_instance
#align probability_theory.kernel.is_finite_kernel_with_density_of_bounded ProbabilityTheory.kernel.isFiniteKernelWithDensityOfBounded

/-- Auxiliary lemma for `is_s_finite_kernel_with_density`.
If a kernel `κ` is finite, then `with_density κ f` is s-finite. -/
theorem isSFiniteKernelWithDensityOfIsFiniteKernel (κ : kernel α β) [IsFiniteKernel κ]
    (hf_ne_top : ∀ a b, f a b ≠ ∞) : IsSFiniteKernel (withDensity κ f) :=
  by
  -- We already have that for `f` bounded from above and a `κ` a finite kernel,
  -- `with_density κ f` is finite. We write any function as a countable sum of bounded
  -- functions, and decompose an s-finite kernel as a sum of finite kernels. We then use that
  -- `with_density` commutes with sums for both arguments and get a sum of finite kernels.
  by_cases hf : Measurable (Function.uncurry f)
  swap
  · rw [with_density_of_not_measurable _ hf]
    infer_instance
  let fs : ℕ → α → β → ℝ≥0∞ := fun n a b => min (f a b) (n + 1) - min (f a b) n
  have h_le : ∀ a b n, ⌈(f a b).toReal⌉₊ ≤ n → f a b ≤ n :=
    by
    intro a b n hn
    have : (f a b).toReal ≤ n := Nat.le_of_ceil_le hn
    rw [← ENNReal.le_ofReal_iff_toReal_le (hf_ne_top a b) _] at this
    · refine' this.trans (le_of_eq _)
      rw [ENNReal.ofReal_coe_nat]
    · norm_cast
      exact zero_le _
  have h_zero : ∀ a b n, ⌈(f a b).toReal⌉₊ ≤ n → fs n a b = 0 :=
    by
    intro a b n hn
    suffices min (f a b) (n + 1) = f a b ∧ min (f a b) n = f a b by
      simp_rw [fs, this.1, this.2, tsub_self (f a b)]
    exact
      ⟨min_eq_left ((h_le a b n hn).trans (le_add_of_nonneg_right zero_le_one)),
        min_eq_left (h_le a b n hn)⟩
  have hf_eq_tsum : f = ∑' n, fs n :=
    by
    have h_sum_a : ∀ a, Summable fun n => fs n a :=
      by
      refine' fun a => pi.summable.mpr fun b => _
      suffices : ∀ n, n ∉ Finset.range ⌈(f a b).toReal⌉₊ → fs n a b = 0
      exact summable_of_ne_finset_zero this
      intro n hn_not_mem
      rw [Finset.mem_range, not_lt] at hn_not_mem
      exact h_zero a b n hn_not_mem
    ext (a b) : 2
    rw [tsum_apply (pi.summable.mpr h_sum_a), tsum_apply (h_sum_a a),
      ENNReal.tsum_eq_liminf_sum_nat]
    have h_finset_sum : ∀ n, (∑ i in Finset.range n, fs i a b) = min (f a b) n :=
      by
      intro n
      induction' n with n hn
      · simp only [Finset.range_zero, Finset.sum_empty, algebraMap.coe_zero, min_zero]
      rw [Finset.sum_range_succ, hn]
      simp_rw [fs]
      norm_cast
      rw [add_tsub_cancel_iff_le]
      refine' min_le_min le_rfl _
      norm_cast
      exact Nat.le_succ n
    simp_rw [h_finset_sum]
    refine' (Filter.Tendsto.liminf_eq _).symm
    refine' Filter.Tendsto.congr' _ tendsto_const_nhds
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    exact ⟨⌈(f a b).toReal⌉₊, fun n hn => (min_eq_left (h_le a b n hn)).symm⟩
  rw [hf_eq_tsum, with_density_tsum _ fun n : ℕ => _]
  swap
  · exact (hf.min measurable_const).sub (hf.min measurable_const)
  refine' is_s_finite_kernel_sum fun n => _
  suffices is_finite_kernel (with_density κ (fs n))
    by
    haveI := this
    infer_instance
  refine' is_finite_kernel_with_density_of_bounded _ (ENNReal.coe_ne_top : ↑n + 1 ≠ ∞) fun a b => _
  norm_cast
  calc
    fs n a b ≤ min (f a b) (n + 1) := tsub_le_self
    _ ≤ n + 1 := min_le_right _ _
    _ = ↑(n + 1) := by norm_cast
    
#align probability_theory.kernel.is_s_finite_kernel_with_density_of_is_finite_kernel ProbabilityTheory.kernel.isSFiniteKernelWithDensityOfIsFiniteKernel

/-- For a s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is everywhere finite,
`with_density κ f` is s-finite. -/
theorem IsSFiniteKernel.withDensity (κ : kernel α β) [IsSFiniteKernel κ]
    (hf_ne_top : ∀ a b, f a b ≠ ∞) : IsSFiniteKernel (withDensity κ f) :=
  by
  have h_eq_sum : with_density κ f = kernel.sum fun i => with_density (seq κ i) f :=
    by
    rw [← with_density_kernel_sum _ _]
    congr
    exact (kernel_sum_seq κ).symm
  rw [h_eq_sum]
  exact
    is_s_finite_kernel_sum fun n =>
      is_s_finite_kernel_with_density_of_is_finite_kernel (seq κ n) hf_ne_top
#align probability_theory.kernel.is_s_finite_kernel.with_density ProbabilityTheory.kernel.IsSFiniteKernel.withDensity

/-- For a s-finite kernel `κ` and a function `f : α → β → ℝ≥0`, `with_density κ f` is s-finite. -/
instance (κ : kernel α β) [IsSFiniteKernel κ] (f : α → β → ℝ≥0) :
    IsSFiniteKernel (withDensity κ fun a b => f a b) :=
  IsSFiniteKernel.withDensity κ fun _ _ => ENNReal.coe_ne_top

end WithDensity

end Kernel

end ProbabilityTheory

