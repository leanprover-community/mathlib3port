/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.group.arithmetic
! leanprover-community/mathlib commit ba2245edf0c8bb155f1569fd9b9492a9b384cde6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.AeMeasurable

/-!
# Typeclasses for measurability of operations

In this file we define classes `has_measurable_mul` etc and prove dot-style lemmas
(`measurable.mul`, `ae_measurable.mul` etc). For binary operations we define two typeclasses:

- `has_measurable_mul` says that both left and right multiplication are measurable;
- `has_measurable_mul₂` says that `λ p : α × α, p.1 * p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `has_measurable_mul₂`
etc require `α` to have a second countable topology.

We define separate classes for `has_measurable_div`/`has_measurable_sub`
because on some types (e.g., `ℕ`, `ℝ≥0∞`) division and/or subtraction are not defined as `a * b⁻¹` /
`a + (-b)`.

For instances relating, e.g., `has_continuous_mul` to `has_measurable_mul` see file
`measure_theory.borel_space`.

## Implementation notes

For the heuristics of `@[to_additive]` it is important that the type with a multiplication
(or another multiplicative operations) is the first (implicit) argument of all declarations.

## Tags

measurable function, arithmetic operator

## Todo

* Uniformize the treatment of `pow` and `smul`.
* Use `@[to_additive]` to send `has_measurable_pow` to `has_measurable_smul₂`.
* This might require changing the definition (swapping the arguments in the function that is
  in the conclusion of `measurable_smul`.)
-/


universe u v

open BigOperators Pointwise MeasureTheory

open MeasureTheory

/-!
### Binary operations: `(+)`, `(*)`, `(-)`, `(/)`
-/


/-- We say that a type `has_measurable_add` if `((+) c)` and `(+ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (+)` see `has_measurable_add₂`. -/
class HasMeasurableAdd (M : Type _) [MeasurableSpace M] [Add M] : Prop where
  measurableConstAdd : ∀ c : M, Measurable ((· + ·) c)
  measurableAddConst : ∀ c : M, Measurable (· + c)
#align has_measurable_add HasMeasurableAdd

export HasMeasurableAdd (measurableConstAdd measurableAddConst)

/-- We say that a type `has_measurable_add` if `uncurry (+)` is a measurable functions.
For a typeclass assuming measurability of `((+) c)` and `(+ c)` see `has_measurable_add`. -/
class HasMeasurableAdd₂ (M : Type _) [MeasurableSpace M] [Add M] : Prop where
  measurableAdd : Measurable fun p : M × M => p.1 + p.2
#align has_measurable_add₂ HasMeasurableAdd₂

export HasMeasurableAdd₂ (measurableAdd)

export HasMeasurableAdd (measurableConstAdd measurableAddConst)

/-- We say that a type `has_measurable_mul` if `((*) c)` and `(* c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (*)` see `has_measurable_mul₂`. -/
@[to_additive]
class HasMeasurableMul (M : Type _) [MeasurableSpace M] [Mul M] : Prop where
  measurableConstMul : ∀ c : M, Measurable ((· * ·) c)
  measurableMulConst : ∀ c : M, Measurable (· * c)
#align has_measurable_mul HasMeasurableMul

export HasMeasurableMul (measurableConstMul measurableMulConst)

/-- We say that a type `has_measurable_mul` if `uncurry (*)` is a measurable functions.
For a typeclass assuming measurability of `((*) c)` and `(* c)` see `has_measurable_mul`. -/
@[to_additive HasMeasurableAdd₂]
class HasMeasurableMul₂ (M : Type _) [MeasurableSpace M] [Mul M] : Prop where
  measurableMul : Measurable fun p : M × M => p.1 * p.2
#align has_measurable_mul₂ HasMeasurableMul₂

export HasMeasurableMul₂ (measurableMul)

section Mul

variable {M α : Type _} [MeasurableSpace M] [Mul M] {m : MeasurableSpace α} {f g : α → M}
  {μ : Measure α}

include m

@[measurability, to_additive]
theorem Measurable.constMul [HasMeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => c * f x :=
  (measurableConstMul c).comp hf
#align measurable.const_mul Measurable.constMul

@[measurability, to_additive]
theorem AeMeasurable.constMul [HasMeasurableMul M] (hf : AeMeasurable f μ) (c : M) :
    AeMeasurable (fun x => c * f x) μ :=
  (HasMeasurableMul.measurableConstMul c).compAeMeasurable hf
#align ae_measurable.const_mul AeMeasurable.constMul

@[measurability, to_additive]
theorem Measurable.mulConst [HasMeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => f x * c :=
  (measurableMulConst c).comp hf
#align measurable.mul_const Measurable.mulConst

@[measurability, to_additive]
theorem AeMeasurable.mulConst [HasMeasurableMul M] (hf : AeMeasurable f μ) (c : M) :
    AeMeasurable (fun x => f x * c) μ :=
  (measurableMulConst c).compAeMeasurable hf
#align ae_measurable.mul_const AeMeasurable.mulConst

@[measurability, to_additive]
theorem Measurable.mul' [HasMeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f * g) :=
  measurableMul.comp (hf.prod_mk hg)
#align measurable.mul' Measurable.mul'

@[measurability, to_additive]
theorem Measurable.mul [HasMeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a * g a :=
  measurableMul.comp (hf.prod_mk hg)
#align measurable.mul Measurable.mul

@[measurability, to_additive]
theorem AeMeasurable.mul' [HasMeasurableMul₂ M] (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (f * g) μ :=
  measurableMul.compAeMeasurable (hf.prod_mk hg)
#align ae_measurable.mul' AeMeasurable.mul'

@[measurability, to_additive]
theorem AeMeasurable.mul [HasMeasurableMul₂ M] (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (fun a => f a * g a) μ :=
  measurableMul.compAeMeasurable (hf.prod_mk hg)
#align ae_measurable.mul AeMeasurable.mul

omit m

@[to_additive]
instance (priority := 100) HasMeasurableMul₂.toHasMeasurableMul [HasMeasurableMul₂ M] :
    HasMeasurableMul M :=
  ⟨fun c => measurableConst.mul measurableId, fun c => measurableId.mul measurableConst⟩
#align has_measurable_mul₂.to_has_measurable_mul HasMeasurableMul₂.toHasMeasurableMul

@[to_additive]
instance Pi.hasMeasurableMul {ι : Type _} {α : ι → Type _} [∀ i, Mul (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, HasMeasurableMul (α i)] : HasMeasurableMul (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurablePiApply i).const_mul _, fun g =>
    measurable_pi_iff.mpr fun i => (measurablePiApply i).mul_const _⟩
#align pi.has_measurable_mul Pi.hasMeasurableMul

@[to_additive Pi.hasMeasurableAdd₂]
instance Pi.hasMeasurableMul₂ {ι : Type _} {α : ι → Type _} [∀ i, Mul (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, HasMeasurableMul₂ (α i)] : HasMeasurableMul₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => measurableFst.eval.mul measurableSnd.eval⟩
#align pi.has_measurable_mul₂ Pi.hasMeasurableMul₂

attribute [measurability]
  Measurable.add' Measurable.add AeMeasurable.add AeMeasurable.add' Measurable.constAdd AeMeasurable.constAdd Measurable.addConst AeMeasurable.addConst

end Mul

/-- A version of `measurable_div_const` that assumes `has_measurable_mul` instead of
  `has_measurable_div`. This can be nice to avoid unnecessary type-class assumptions. -/
@[to_additive
      " A version of `measurable_sub_const` that assumes `has_measurable_add` instead of\n  `has_measurable_sub`. This can be nice to avoid unnecessary type-class assumptions. "]
theorem measurableDivConst' {G : Type _} [DivInvMonoid G] [MeasurableSpace G] [HasMeasurableMul G]
    (g : G) : Measurable fun h => h / g := by simp_rw [div_eq_mul_inv, measurable_mul_const]
#align measurable_div_const' measurableDivConst'

/-- This class assumes that the map `β × γ → β` given by `(x, y) ↦ x ^ y` is measurable. -/
class HasMeasurablePow (β γ : Type _) [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] where
  measurablePow : Measurable fun p : β × γ => p.1 ^ p.2
#align has_measurable_pow HasMeasurablePow

export HasMeasurablePow (measurablePow)

/-- `monoid.has_pow` is measurable. -/
instance Monoid.hasMeasurablePow (M : Type _) [Monoid M] [MeasurableSpace M] [HasMeasurableMul₂ M] :
    HasMeasurablePow M ℕ :=
  ⟨measurableFromProdCountable fun n => by
      induction' n with n ih
      · simp only [pow_zero, ← Pi.one_def, measurableOne]
      · simp only [pow_succ]
        exact measurable_id.mul ih⟩
#align monoid.has_measurable_pow Monoid.hasMeasurablePow

section Pow

variable {β γ α : Type _} [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] [HasMeasurablePow β γ]
  {m : MeasurableSpace α} {μ : Measure α} {f : α → β} {g : α → γ}

include m

@[measurability]
theorem Measurable.pow (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x ^ g x :=
  measurablePow.comp (hf.prod_mk hg)
#align measurable.pow Measurable.pow

@[measurability]
theorem AeMeasurable.pow (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (fun x => f x ^ g x) μ :=
  measurablePow.compAeMeasurable (hf.prod_mk hg)
#align ae_measurable.pow AeMeasurable.pow

@[measurability]
theorem Measurable.powConst (hf : Measurable f) (c : γ) : Measurable fun x => f x ^ c :=
  hf.pow measurableConst
#align measurable.pow_const Measurable.powConst

@[measurability]
theorem AeMeasurable.powConst (hf : AeMeasurable f μ) (c : γ) : AeMeasurable (fun x => f x ^ c) μ :=
  hf.pow aeMeasurableConst
#align ae_measurable.pow_const AeMeasurable.powConst

@[measurability]
theorem Measurable.constPow (hg : Measurable g) (c : β) : Measurable fun x => c ^ g x :=
  measurableConst.pow hg
#align measurable.const_pow Measurable.constPow

@[measurability]
theorem AeMeasurable.constPow (hg : AeMeasurable g μ) (c : β) : AeMeasurable (fun x => c ^ g x) μ :=
  aeMeasurableConst.pow hg
#align ae_measurable.const_pow AeMeasurable.constPow

omit m

end Pow

/-- We say that a type `has_measurable_sub` if `(λ x, c - x)` and `(λ x, x - c)` are measurable
functions. For a typeclass assuming measurability of `uncurry (-)` see `has_measurable_sub₂`. -/
class HasMeasurableSub (G : Type _) [MeasurableSpace G] [Sub G] : Prop where
  measurableConstSub : ∀ c : G, Measurable fun x => c - x
  measurableSubConst : ∀ c : G, Measurable fun x => x - c
#align has_measurable_sub HasMeasurableSub

export HasMeasurableSub (measurableConstSub measurableSubConst)

/-- We say that a type `has_measurable_sub` if `uncurry (-)` is a measurable functions.
For a typeclass assuming measurability of `((-) c)` and `(- c)` see `has_measurable_sub`. -/
class HasMeasurableSub₂ (G : Type _) [MeasurableSpace G] [Sub G] : Prop where
  measurableSub : Measurable fun p : G × G => p.1 - p.2
#align has_measurable_sub₂ HasMeasurableSub₂

export HasMeasurableSub₂ (measurableSub)

/-- We say that a type `has_measurable_div` if `((/) c)` and `(/ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (/)` see `has_measurable_div₂`. -/
@[to_additive]
class HasMeasurableDiv (G₀ : Type _) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurableConstDiv : ∀ c : G₀, Measurable ((· / ·) c)
  measurableDivConst : ∀ c : G₀, Measurable (· / c)
#align has_measurable_div HasMeasurableDiv

export HasMeasurableDiv (measurableConstDiv measurableDivConst)

/-- We say that a type `has_measurable_div` if `uncurry (/)` is a measurable functions.
For a typeclass assuming measurability of `((/) c)` and `(/ c)` see `has_measurable_div`. -/
@[to_additive HasMeasurableSub₂]
class HasMeasurableDiv₂ (G₀ : Type _) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurableDiv : Measurable fun p : G₀ × G₀ => p.1 / p.2
#align has_measurable_div₂ HasMeasurableDiv₂

export HasMeasurableDiv₂ (measurableDiv)

section Div

variable {G α : Type _} [MeasurableSpace G] [Div G] {m : MeasurableSpace α} {f g : α → G}
  {μ : Measure α}

include m

@[measurability, to_additive]
theorem Measurable.constDiv [HasMeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => c / f x :=
  (HasMeasurableDiv.measurableConstDiv c).comp hf
#align measurable.const_div Measurable.constDiv

@[measurability, to_additive]
theorem AeMeasurable.constDiv [HasMeasurableDiv G] (hf : AeMeasurable f μ) (c : G) :
    AeMeasurable (fun x => c / f x) μ :=
  (HasMeasurableDiv.measurableConstDiv c).compAeMeasurable hf
#align ae_measurable.const_div AeMeasurable.constDiv

@[measurability, to_additive]
theorem Measurable.divConst [HasMeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => f x / c :=
  (HasMeasurableDiv.measurableDivConst c).comp hf
#align measurable.div_const Measurable.divConst

@[measurability, to_additive]
theorem AeMeasurable.divConst [HasMeasurableDiv G] (hf : AeMeasurable f μ) (c : G) :
    AeMeasurable (fun x => f x / c) μ :=
  (HasMeasurableDiv.measurableDivConst c).compAeMeasurable hf
#align ae_measurable.div_const AeMeasurable.divConst

@[measurability, to_additive]
theorem Measurable.div' [HasMeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f / g) :=
  measurableDiv.comp (hf.prod_mk hg)
#align measurable.div' Measurable.div'

@[measurability, to_additive]
theorem Measurable.div [HasMeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a / g a :=
  measurableDiv.comp (hf.prod_mk hg)
#align measurable.div Measurable.div

@[measurability, to_additive]
theorem AeMeasurable.div' [HasMeasurableDiv₂ G] (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (f / g) μ :=
  measurableDiv.compAeMeasurable (hf.prod_mk hg)
#align ae_measurable.div' AeMeasurable.div'

@[measurability, to_additive]
theorem AeMeasurable.div [HasMeasurableDiv₂ G] (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (fun a => f a / g a) μ :=
  measurableDiv.compAeMeasurable (hf.prod_mk hg)
#align ae_measurable.div AeMeasurable.div

attribute [measurability]
  Measurable.sub Measurable.sub' AeMeasurable.sub AeMeasurable.sub' Measurable.constSub AeMeasurable.constSub Measurable.subConst AeMeasurable.subConst

omit m

@[to_additive]
instance (priority := 100) HasMeasurableDiv₂.toHasMeasurableDiv [HasMeasurableDiv₂ G] :
    HasMeasurableDiv G :=
  ⟨fun c => measurableConst.div measurableId, fun c => measurableId.div measurableConst⟩
#align has_measurable_div₂.to_has_measurable_div HasMeasurableDiv₂.toHasMeasurableDiv

@[to_additive]
instance Pi.hasMeasurableDiv {ι : Type _} {α : ι → Type _} [∀ i, Div (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, HasMeasurableDiv (α i)] : HasMeasurableDiv (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurablePiApply i).const_div _, fun g =>
    measurable_pi_iff.mpr fun i => (measurablePiApply i).div_const _⟩
#align pi.has_measurable_div Pi.hasMeasurableDiv

@[to_additive Pi.hasMeasurableSub₂]
instance Pi.hasMeasurableDiv₂ {ι : Type _} {α : ι → Type _} [∀ i, Div (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, HasMeasurableDiv₂ (α i)] : HasMeasurableDiv₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => measurableFst.eval.div measurableSnd.eval⟩
#align pi.has_measurable_div₂ Pi.hasMeasurableDiv₂

@[measurability]
theorem measurableSetEqFun {m : MeasurableSpace α} {E} [MeasurableSpace E] [AddGroup E]
    [MeasurableSingletonClass E] [HasMeasurableSub₂ E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet { x | f x = g x } := by
  suffices h_set_eq : { x : α | f x = g x } = { x | (f - g) x = (0 : E) }
  · rw [h_set_eq]
    exact (hf.sub hg) measurableSetEq
  ext
  simp_rw [Set.mem_setOf_eq, Pi.sub_apply, sub_eq_zero]
#align measurable_set_eq_fun measurableSetEqFun

theorem measurableSetEqFunOfCountable {m : MeasurableSpace α} {E} [MeasurableSpace E]
    [MeasurableSingletonClass E] [Countable E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet { x | f x = g x } := by
  have : { x | f x = g x } = ⋃ j, { x | f x = j } ∩ { x | g x = j } := by
    ext1 x
    simp only [Set.mem_setOf_eq, Set.mem_Union, Set.mem_inter_iff, exists_eq_right']
  rw [this]
  refine' MeasurableSet.union fun j => MeasurableSet.inter _ _
  · exact hf (measurable_set_singleton j)
  · exact hg (measurable_set_singleton j)
#align measurable_set_eq_fun_of_countable measurableSetEqFunOfCountable

theorem ae_eq_trim_of_measurable {α E} {m m0 : MeasurableSpace α} {μ : Measure α}
    [MeasurableSpace E] [AddGroup E] [MeasurableSingletonClass E] [HasMeasurableSub₂ E]
    (hm : m ≤ m0) {f g : α → E} (hf : measurable[m] f) (hg : measurable[m] g) (hfg : f =ᵐ[μ] g) :
    f =ᶠ[@Measure.ae α m (μ.trim hm)] g := by
  rwa [Filter.EventuallyEq, ae_iff, trim_measurable_set_eq hm _]
  exact @MeasurableSet.compl α _ m (@measurableSetEqFun α m E _ _ _ _ _ _ hf hg)
#align ae_eq_trim_of_measurable ae_eq_trim_of_measurable

end Div

/-- We say that a type `has_measurable_neg` if `x ↦ -x` is a measurable function. -/
class HasMeasurableNeg (G : Type _) [Neg G] [MeasurableSpace G] : Prop where
  measurableNeg : Measurable (Neg.neg : G → G)
#align has_measurable_neg HasMeasurableNeg

/-- We say that a type `has_measurable_inv` if `x ↦ x⁻¹` is a measurable function. -/
@[to_additive]
class HasMeasurableInv (G : Type _) [Inv G] [MeasurableSpace G] : Prop where
  measurableInv : Measurable (Inv.inv : G → G)
#align has_measurable_inv HasMeasurableInv

export HasMeasurableInv (measurableInv)

export HasMeasurableNeg (measurableNeg)

@[to_additive]
instance (priority := 100) hasMeasurableDivOfMulInv (G : Type _) [MeasurableSpace G]
    [DivInvMonoid G] [HasMeasurableMul G] [HasMeasurableInv G] :
    HasMeasurableDiv
      G where 
  measurableConstDiv c := by 
    convert measurable_inv.const_mul c
    ext1
    apply div_eq_mul_inv
  measurableDivConst c := by 
    convert measurable_id.mul_const c⁻¹
    ext1
    apply div_eq_mul_inv
#align has_measurable_div_of_mul_inv hasMeasurableDivOfMulInv

section Inv

variable {G α : Type _} [Inv G] [MeasurableSpace G] [HasMeasurableInv G] {m : MeasurableSpace α}
  {f : α → G} {μ : Measure α}

include m

@[measurability, to_additive]
theorem Measurable.inv (hf : Measurable f) : Measurable fun x => (f x)⁻¹ :=
  measurableInv.comp hf
#align measurable.inv Measurable.inv

@[measurability, to_additive]
theorem AeMeasurable.inv (hf : AeMeasurable f μ) : AeMeasurable (fun x => (f x)⁻¹) μ :=
  measurableInv.compAeMeasurable hf
#align ae_measurable.inv AeMeasurable.inv

attribute [measurability] Measurable.neg AeMeasurable.neg

@[simp, to_additive]
theorem measurable_inv_iff {G : Type _} [Group G] [MeasurableSpace G] [HasMeasurableInv G]
    {f : α → G} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align measurable_inv_iff measurable_inv_iff

@[simp, to_additive]
theorem ae_measurable_inv_iff {G : Type _} [Group G] [MeasurableSpace G] [HasMeasurableInv G]
    {f : α → G} : AeMeasurable (fun x => (f x)⁻¹) μ ↔ AeMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align ae_measurable_inv_iff ae_measurable_inv_iff

@[simp]
theorem measurable_inv_iff₀ {G₀ : Type _} [GroupWithZero G₀] [MeasurableSpace G₀]
    [HasMeasurableInv G₀] {f : α → G₀} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align measurable_inv_iff₀ measurable_inv_iff₀

@[simp]
theorem ae_measurable_inv_iff₀ {G₀ : Type _} [GroupWithZero G₀] [MeasurableSpace G₀]
    [HasMeasurableInv G₀] {f : α → G₀} : AeMeasurable (fun x => (f x)⁻¹) μ ↔ AeMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align ae_measurable_inv_iff₀ ae_measurable_inv_iff₀

omit m

@[to_additive]
instance Pi.hasMeasurableInv {ι : Type _} {α : ι → Type _} [∀ i, Inv (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, HasMeasurableInv (α i)] : HasMeasurableInv (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => (measurablePiApply i).inv⟩
#align pi.has_measurable_inv Pi.hasMeasurableInv

@[to_additive]
theorem MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) : MeasurableSet s⁻¹ :=
  measurableInv hs
#align measurable_set.inv MeasurableSet.inv

end Inv

/-- `div_inv_monoid.has_pow` is measurable. -/
instance DivInvMonoid.hasMeasurableZpow (G : Type u) [DivInvMonoid G] [MeasurableSpace G]
    [HasMeasurableMul₂ G] [HasMeasurableInv G] : HasMeasurablePow G ℤ :=
  ⟨measurableFromProdCountable fun n => by 
      cases' n with n n
      · simp_rw [zpow_ofNat]
        exact measurable_id.pow_const _
      · simp_rw [zpow_negSucc]
        exact (measurable_id.pow_const (n + 1)).inv⟩
#align div_inv_monoid.has_measurable_zpow DivInvMonoid.hasMeasurableZpow

@[to_additive]
instance (priority := 100) hasMeasurableDiv₂OfMulInv (G : Type _) [MeasurableSpace G]
    [DivInvMonoid G] [HasMeasurableMul₂ G] [HasMeasurableInv G] : HasMeasurableDiv₂ G :=
  ⟨by 
    simp only [div_eq_mul_inv]
    exact measurable_fst.mul measurable_snd.inv⟩
#align has_measurable_div₂_of_mul_inv hasMeasurableDiv₂OfMulInv

/-- We say that the action of `M` on `α` `has_measurable_vadd` if for each `c` the map `x ↦ c +ᵥ x`
is a measurable function and for each `x` the map `c ↦ c +ᵥ x` is a measurable function. -/
class HasMeasurableVadd (M α : Type _) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α] :
  Prop where
  measurableConstVadd : ∀ c : M, Measurable ((· +ᵥ ·) c : α → α)
  measurableVaddConst : ∀ x : α, Measurable fun c : M => c +ᵥ x
#align has_measurable_vadd HasMeasurableVadd

/-- We say that the action of `M` on `α` `has_measurable_smul` if for each `c` the map `x ↦ c • x`
is a measurable function and for each `x` the map `c ↦ c • x` is a measurable function. -/
@[to_additive]
class HasMeasurableSmul (M α : Type _) [HasSmul M α] [MeasurableSpace M] [MeasurableSpace α] :
  Prop where
  measurableConstSmul : ∀ c : M, Measurable ((· • ·) c : α → α)
  measurableSmulConst : ∀ x : α, Measurable fun c : M => c • x
#align has_measurable_smul HasMeasurableSmul

/-- We say that the action of `M` on `α` `has_measurable_vadd₂` if the map
`(c, x) ↦ c +ᵥ x` is a measurable function. -/
class HasMeasurableVadd₂ (M α : Type _) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α] :
  Prop where
  measurableVadd : Measurable (Function.uncurry (· +ᵥ ·) : M × α → α)
#align has_measurable_vadd₂ HasMeasurableVadd₂

/-- We say that the action of `M` on `α` `has_measurable_smul₂` if the map
`(c, x) ↦ c • x` is a measurable function. -/
@[to_additive HasMeasurableVadd₂]
class HasMeasurableSmul₂ (M α : Type _) [HasSmul M α] [MeasurableSpace M] [MeasurableSpace α] :
  Prop where
  measurableSmul : Measurable (Function.uncurry (· • ·) : M × α → α)
#align has_measurable_smul₂ HasMeasurableSmul₂

export HasMeasurableSmul (measurableConstSmul measurableSmulConst)

export HasMeasurableSmul₂ (measurableSmul)

export HasMeasurableVadd (measurableConstVadd measurableVaddConst)

export HasMeasurableVadd₂ (measurableVadd)

@[to_additive]
instance hasMeasurableSmulOfMul (M : Type _) [Mul M] [MeasurableSpace M] [HasMeasurableMul M] :
    HasMeasurableSmul M M :=
  ⟨measurableId.const_mul, measurableId.mul_const⟩
#align has_measurable_smul_of_mul hasMeasurableSmulOfMul

@[to_additive]
instance hasMeasurableSmul₂OfMul (M : Type _) [Mul M] [MeasurableSpace M] [HasMeasurableMul₂ M] :
    HasMeasurableSmul₂ M M :=
  ⟨measurableMul⟩
#align has_measurable_smul₂_of_mul hasMeasurableSmul₂OfMul

@[to_additive]
instance Submonoid.hasMeasurableSmul {M α} [MeasurableSpace M] [MeasurableSpace α] [Monoid M]
    [MulAction M α] [HasMeasurableSmul M α] (s : Submonoid M) : HasMeasurableSmul s α :=
  ⟨fun c => by simpa only using measurable_const_smul (c : M), fun x =>
    (measurableSmulConst x : Measurable fun c : M => c • x).comp measurableSubtypeCoe⟩
#align submonoid.has_measurable_smul Submonoid.hasMeasurableSmul

@[to_additive]
instance Subgroup.hasMeasurableSmul {G α} [MeasurableSpace G] [MeasurableSpace α] [Group G]
    [MulAction G α] [HasMeasurableSmul G α] (s : Subgroup G) : HasMeasurableSmul s α :=
  s.toSubmonoid.HasMeasurableSmul
#align subgroup.has_measurable_smul Subgroup.hasMeasurableSmul

section Smul

variable {M β α : Type _} [MeasurableSpace M] [MeasurableSpace β] [HasSmul M β]
  {m : MeasurableSpace α} {f : α → M} {g : α → β}

include m

@[measurability, to_additive]
theorem Measurable.smul [HasMeasurableSmul₂ M β] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x • g x :=
  measurableSmul.comp (hf.prod_mk hg)
#align measurable.smul Measurable.smul

@[measurability, to_additive]
theorem AeMeasurable.smul [HasMeasurableSmul₂ M β] {μ : Measure α} (hf : AeMeasurable f μ)
    (hg : AeMeasurable g μ) : AeMeasurable (fun x => f x • g x) μ :=
  HasMeasurableSmul₂.measurableSmul.compAeMeasurable (hf.prod_mk hg)
#align ae_measurable.smul AeMeasurable.smul

omit m

@[to_additive]
instance (priority := 100) HasMeasurableSmul₂.toHasMeasurableSmul [HasMeasurableSmul₂ M β] :
    HasMeasurableSmul M β :=
  ⟨fun c => measurableConst.smul measurableId, fun y => measurableId.smul measurableConst⟩
#align has_measurable_smul₂.to_has_measurable_smul HasMeasurableSmul₂.toHasMeasurableSmul

include m

variable [HasMeasurableSmul M β] {μ : Measure α}

@[measurability, to_additive]
theorem Measurable.smulConst (hf : Measurable f) (y : β) : Measurable fun x => f x • y :=
  (HasMeasurableSmul.measurableSmulConst y).comp hf
#align measurable.smul_const Measurable.smulConst

@[measurability, to_additive]
theorem AeMeasurable.smulConst (hf : AeMeasurable f μ) (y : β) :
    AeMeasurable (fun x => f x • y) μ :=
  (HasMeasurableSmul.measurableSmulConst y).compAeMeasurable hf
#align ae_measurable.smul_const AeMeasurable.smulConst

@[measurability, to_additive]
theorem Measurable.constSmul' (hg : Measurable g) (c : M) : Measurable fun x => c • g x :=
  (HasMeasurableSmul.measurableConstSmul c).comp hg
#align measurable.const_smul' Measurable.constSmul'

@[measurability, to_additive]
theorem Measurable.constSmul (hg : Measurable g) (c : M) : Measurable (c • g) :=
  hg.constSmul' c
#align measurable.const_smul Measurable.constSmul

@[measurability, to_additive]
theorem AeMeasurable.constSmul' (hg : AeMeasurable g μ) (c : M) :
    AeMeasurable (fun x => c • g x) μ :=
  (HasMeasurableSmul.measurableConstSmul c).compAeMeasurable hg
#align ae_measurable.const_smul' AeMeasurable.constSmul'

@[measurability, to_additive]
theorem AeMeasurable.constSmul (hf : AeMeasurable g μ) (c : M) : AeMeasurable (c • g) μ :=
  hf.constSmul' c
#align ae_measurable.const_smul AeMeasurable.constSmul

omit m

@[to_additive]
instance Pi.hasMeasurableSmul {ι : Type _} {α : ι → Type _} [∀ i, HasSmul M (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, HasMeasurableSmul M (α i)] :
    HasMeasurableSmul M (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurablePiApply i).const_smul _, fun g =>
    measurable_pi_iff.mpr fun i => measurableSmulConst _⟩
#align pi.has_measurable_smul Pi.hasMeasurableSmul

/-- `add_monoid.has_smul_nat` is measurable. -/
instance AddMonoid.hasMeasurableSmulNat₂ (M : Type _) [AddMonoid M] [MeasurableSpace M]
    [HasMeasurableAdd₂ M] : HasMeasurableSmul₂ ℕ M :=
  ⟨by 
    suffices Measurable fun p : M × ℕ => p.2 • p.1 by apply this.comp measurableSwap
    refine' measurableFromProdCountable fun n => _
    induction' n with n ih
    · simp only [zero_smul, ← Pi.zero_def, measurableZero]
    · simp only [succ_nsmul]
      exact measurable_id.add ih⟩
#align add_monoid.has_measurable_smul_nat₂ AddMonoid.hasMeasurableSmulNat₂

/-- `sub_neg_monoid.has_smul_int` is measurable. -/
instance SubNegMonoid.hasMeasurableSmulInt₂ (M : Type _) [SubNegMonoid M] [MeasurableSpace M]
    [HasMeasurableAdd₂ M] [HasMeasurableNeg M] : HasMeasurableSmul₂ ℤ M :=
  ⟨by 
    suffices Measurable fun p : M × ℤ => p.2 • p.1 by apply this.comp measurableSwap
    refine' measurableFromProdCountable fun n => _
    induction' n with n n ih
    · simp only [of_nat_zsmul]
      exact measurable_const_smul _
    · simp only [negSucc_zsmul]
      exact (measurable_const_smul _).neg⟩
#align sub_neg_monoid.has_measurable_smul_int₂ SubNegMonoid.hasMeasurableSmulInt₂

end Smul

section MulAction

variable {M β α : Type _} [MeasurableSpace M] [MeasurableSpace β] [Monoid M] [MulAction M β]
  [HasMeasurableSmul M β] [MeasurableSpace α] {f : α → β} {μ : Measure α}

variable {G : Type _} [Group G] [MeasurableSpace G] [MulAction G β] [HasMeasurableSmul G β]

@[to_additive]
theorem measurable_const_smul_iff (c : G) : (Measurable fun x => c • f x) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align measurable_const_smul_iff measurable_const_smul_iff

@[to_additive]
theorem ae_measurable_const_smul_iff (c : G) :
    AeMeasurable (fun x => c • f x) μ ↔ AeMeasurable f μ :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align ae_measurable_const_smul_iff ae_measurable_const_smul_iff

@[to_additive]
instance : MeasurableSpace Mˣ :=
  MeasurableSpace.comap (coe : Mˣ → M) ‹_›

@[to_additive]
instance Units.hasMeasurableSmul :
    HasMeasurableSmul Mˣ
      β where 
  measurableConstSmul c := (measurableConstSmul (c : M) : _)
  measurableSmulConst x :=
    (measurableSmulConst x : Measurable fun c : M => c • x).comp MeasurableSpace.le_map_comap
#align units.has_measurable_smul Units.hasMeasurableSmul

@[to_additive]
theorem IsUnit.measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ measurable_const_smul_iff u
#align is_unit.measurable_const_smul_iff IsUnit.measurable_const_smul_iff

@[to_additive]
theorem IsUnit.ae_measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AeMeasurable (fun x => c • f x) μ ↔ AeMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ ae_measurable_const_smul_iff u
#align is_unit.ae_measurable_const_smul_iff IsUnit.ae_measurable_const_smul_iff

variable {G₀ : Type _} [GroupWithZero G₀] [MeasurableSpace G₀] [MulAction G₀ β]
  [HasMeasurableSmul G₀ β]

theorem measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  (IsUnit.mk0 c hc).measurable_const_smul_iff
#align measurable_const_smul_iff₀ measurable_const_smul_iff₀

theorem ae_measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    AeMeasurable (fun x => c • f x) μ ↔ AeMeasurable f μ :=
  (IsUnit.mk0 c hc).ae_measurable_const_smul_iff
#align ae_measurable_const_smul_iff₀ ae_measurable_const_smul_iff₀

end MulAction

/-!
### Opposite monoid
-/


section Opposite

open MulOpposite

@[to_additive]
instance {α : Type _} [h : MeasurableSpace α] : MeasurableSpace αᵐᵒᵖ :=
  MeasurableSpace.map op h

@[to_additive]
theorem measurableMulOp {α : Type _} [MeasurableSpace α] : Measurable (op : α → αᵐᵒᵖ) := fun s => id
#align measurable_mul_op measurableMulOp

@[to_additive]
theorem measurableMulUnop {α : Type _} [MeasurableSpace α] : Measurable (unop : αᵐᵒᵖ → α) :=
  fun s => id
#align measurable_mul_unop measurableMulUnop

@[to_additive]
instance {M : Type _} [Mul M] [MeasurableSpace M] [HasMeasurableMul M] : HasMeasurableMul Mᵐᵒᵖ :=
  ⟨fun c => measurableMulOp.comp (measurableMulUnop.mul_const _), fun c =>
    measurableMulOp.comp (measurableMulUnop.const_mul _)⟩

@[to_additive]
instance {M : Type _} [Mul M] [MeasurableSpace M] [HasMeasurableMul₂ M] : HasMeasurableMul₂ Mᵐᵒᵖ :=
  ⟨measurableMulOp.comp
      ((measurableMulUnop.comp measurableSnd).mul (measurableMulUnop.comp measurableFst))⟩

/-- If a scalar is central, then its right action is measurable when its left action is. -/
instance HasMeasurableSmul.op {M α} [MeasurableSpace M] [MeasurableSpace α] [HasSmul M α]
    [HasSmul Mᵐᵒᵖ α] [IsCentralScalar M α] [HasMeasurableSmul M α] : HasMeasurableSmul Mᵐᵒᵖ α :=
  ⟨MulOpposite.rec' fun c =>
      show Measurable fun x => op c • x by
        simpa only [op_smul_eq_smul] using measurable_const_smul c,
    fun x =>
    show Measurable fun c => op (unop c) • x by
      simpa only [op_smul_eq_smul] using (measurable_smul_const x).comp measurableMulUnop⟩
#align has_measurable_smul.op HasMeasurableSmul.op

/-- If a scalar is central, then its right action is measurable when its left action is. -/
instance HasMeasurableSmul₂.op {M α} [MeasurableSpace M] [MeasurableSpace α] [HasSmul M α]
    [HasSmul Mᵐᵒᵖ α] [IsCentralScalar M α] [HasMeasurableSmul₂ M α] : HasMeasurableSmul₂ Mᵐᵒᵖ α :=
  ⟨show Measurable fun x : Mᵐᵒᵖ × α => op (unop x.1) • x.2 by
      simp_rw [op_smul_eq_smul]
      refine' (measurable_mul_unop.comp measurableFst).smul measurableSnd⟩
#align has_measurable_smul₂.op HasMeasurableSmul₂.op

@[to_additive]
instance hasMeasurableSmulOppositeOfMul {M : Type _} [Mul M] [MeasurableSpace M]
    [HasMeasurableMul M] : HasMeasurableSmul Mᵐᵒᵖ M :=
  ⟨fun c => measurableMulConst (unop c), fun x => measurableMulUnop.const_mul x⟩
#align has_measurable_smul_opposite_of_mul hasMeasurableSmulOppositeOfMul

@[to_additive]
instance hasMeasurableSmul₂OppositeOfMul {M : Type _} [Mul M] [MeasurableSpace M]
    [HasMeasurableMul₂ M] : HasMeasurableSmul₂ Mᵐᵒᵖ M :=
  ⟨measurableSnd.mul (measurableMulUnop.comp measurableFst)⟩
#align has_measurable_smul₂_opposite_of_mul hasMeasurableSmul₂OppositeOfMul

end Opposite

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M α : Type _} [Monoid M] [MeasurableSpace M] [HasMeasurableMul₂ M] {m : MeasurableSpace α}
  {μ : Measure α}

include m

@[measurability, to_additive]
theorem List.measurableProd' (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) : Measurable l.Prod :=
  by 
  induction' l with f l ihl; · exact measurableOne
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.measurable_prod' List.measurableProd'

@[measurability, to_additive]
theorem List.aeMeasurableProd' (l : List (α → M)) (hl : ∀ f ∈ l, AeMeasurable f μ) :
    AeMeasurable l.Prod μ := by 
  induction' l with f l ihl; · exact aeMeasurableOne
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.ae_measurable_prod' List.aeMeasurableProd'

@[measurability, to_additive]
theorem List.measurableProd (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable fun x => (l.map fun f : α → M => f x).Prod := by
  simpa only [← Pi.list_prod_apply] using l.measurable_prod' hl
#align list.measurable_prod List.measurableProd

@[measurability, to_additive]
theorem List.aeMeasurableProd (l : List (α → M)) (hl : ∀ f ∈ l, AeMeasurable f μ) :
    AeMeasurable (fun x => (l.map fun f : α → M => f x).Prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.ae_measurable_prod' hl
#align list.ae_measurable_prod List.aeMeasurableProd

omit m

end Monoid

section CommMonoid

variable {M ι α : Type _} [CommMonoid M] [MeasurableSpace M] [HasMeasurableMul₂ M]
  {m : MeasurableSpace α} {μ : Measure α} {f : ι → α → M}

include m

@[measurability, to_additive]
theorem Multiset.measurableProd' (l : Multiset (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable l.Prod := by 
  rcases l with ⟨l⟩
  simpa using l.measurable_prod' (by simpa using hl)
#align multiset.measurable_prod' Multiset.measurableProd'

@[measurability, to_additive]
theorem Multiset.aeMeasurableProd' (l : Multiset (α → M)) (hl : ∀ f ∈ l, AeMeasurable f μ) :
    AeMeasurable l.Prod μ := by 
  rcases l with ⟨l⟩
  simpa using l.ae_measurable_prod' (by simpa using hl)
#align multiset.ae_measurable_prod' Multiset.aeMeasurableProd'

@[measurability, to_additive]
theorem Multiset.measurableProd (s : Multiset (α → M)) (hs : ∀ f ∈ s, Measurable f) :
    Measurable fun x => (s.map fun f : α → M => f x).Prod := by
  simpa only [← Pi.multiset_prod_apply] using s.measurable_prod' hs
#align multiset.measurable_prod Multiset.measurableProd

@[measurability, to_additive]
theorem Multiset.aeMeasurableProd (s : Multiset (α → M)) (hs : ∀ f ∈ s, AeMeasurable f μ) :
    AeMeasurable (fun x => (s.map fun f : α → M => f x).Prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.ae_measurable_prod' hs
#align multiset.ae_measurable_prod Multiset.aeMeasurableProd

@[measurability, to_additive]
theorem Finset.measurableProd' (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (∏ i in s, f i) :=
  Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurableOne M _ _ _ _) hf
#align finset.measurable_prod' Finset.measurableProd'

@[measurability, to_additive]
theorem Finset.measurableProd (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun a => ∏ i in s, f i a := by
  simpa only [← Finset.prod_apply] using s.measurable_prod' hf
#align finset.measurable_prod Finset.measurableProd

@[measurability, to_additive]
theorem Finset.aeMeasurableProd' (s : Finset ι) (hf : ∀ i ∈ s, AeMeasurable (f i) μ) :
    AeMeasurable (∏ i in s, f i) μ :=
  (Multiset.aeMeasurableProd' _) fun g hg =>
    let ⟨i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi
#align finset.ae_measurable_prod' Finset.aeMeasurableProd'

@[measurability, to_additive]
theorem Finset.aeMeasurableProd (s : Finset ι) (hf : ∀ i ∈ s, AeMeasurable (f i) μ) :
    AeMeasurable (fun a => ∏ i in s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.ae_measurable_prod' hf
#align finset.ae_measurable_prod Finset.aeMeasurableProd

omit m

end CommMonoid

