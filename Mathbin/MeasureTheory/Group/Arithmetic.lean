/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import MeasureTheory.Measure.AeMeasurable

#align_import measure_theory.group.arithmetic from "leanprover-community/mathlib"@"781cb2eed038c4caf53bdbd8d20a95e5822d77df"

/-!
# Typeclasses for measurability of operations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

open scoped BigOperators Pointwise MeasureTheory

open MeasureTheory

/-!
### Binary operations: `(+)`, `(*)`, `(-)`, `(/)`
-/


#print MeasurableAdd /-
/-- We say that a type `has_measurable_add` if `((+) c)` and `(+ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (+)` see `has_measurable_add₂`. -/
class MeasurableAdd (M : Type _) [MeasurableSpace M] [Add M] : Prop where
  measurable_const_add : ∀ c : M, Measurable ((· + ·) c)
  measurable_add_const : ∀ c : M, Measurable (· + c)
#align has_measurable_add MeasurableAdd
-/

export MeasurableAdd (measurable_const_add measurable_add_const)

#print MeasurableAdd₂ /-
/-- We say that a type `has_measurable_add` if `uncurry (+)` is a measurable functions.
For a typeclass assuming measurability of `((+) c)` and `(+ c)` see `has_measurable_add`. -/
class MeasurableAdd₂ (M : Type _) [MeasurableSpace M] [Add M] : Prop where
  measurable_add : Measurable fun p : M × M => p.1 + p.2
#align has_measurable_add₂ MeasurableAdd₂
-/

export MeasurableAdd₂ (measurable_add)

export MeasurableAdd (measurable_const_add measurable_add_const)

#print MeasurableMul /-
/-- We say that a type `has_measurable_mul` if `((*) c)` and `(* c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (*)` see `has_measurable_mul₂`. -/
@[to_additive]
class MeasurableMul (M : Type _) [MeasurableSpace M] [Mul M] : Prop where
  measurable_const_mul : ∀ c : M, Measurable ((· * ·) c)
  measurable_mul_const : ∀ c : M, Measurable (· * c)
#align has_measurable_mul MeasurableMul
#align has_measurable_add MeasurableAdd
-/

export MeasurableMul (measurable_const_mul measurable_mul_const)

#print MeasurableMul₂ /-
/-- We say that a type `has_measurable_mul` if `uncurry (*)` is a measurable functions.
For a typeclass assuming measurability of `((*) c)` and `(* c)` see `has_measurable_mul`. -/
@[to_additive MeasurableAdd₂]
class MeasurableMul₂ (M : Type _) [MeasurableSpace M] [Mul M] : Prop where
  measurable_mul : Measurable fun p : M × M => p.1 * p.2
#align has_measurable_mul₂ MeasurableMul₂
#align has_measurable_add₂ MeasurableAdd₂
-/

export MeasurableMul₂ (measurable_mul)

section Mul

variable {M α : Type _} [MeasurableSpace M] [Mul M] {m : MeasurableSpace α} {f g : α → M}
  {μ : Measure α}

#print Measurable.const_mul /-
@[measurability, to_additive]
theorem Measurable.const_mul [MeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => c * f x :=
  (measurable_const_mul c).comp hf
#align measurable.const_mul Measurable.const_mul
#align measurable.const_add Measurable.const_add
-/

#print AEMeasurable.const_mul /-
@[measurability, to_additive]
theorem AEMeasurable.const_mul [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c * f x) μ :=
  (MeasurableMul.measurable_const_mul c).comp_aemeasurable hf
#align ae_measurable.const_mul AEMeasurable.const_mul
#align ae_measurable.const_add AEMeasurable.const_add
-/

#print Measurable.mul_const /-
@[measurability, to_additive]
theorem Measurable.mul_const [MeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => f x * c :=
  (measurable_mul_const c).comp hf
#align measurable.mul_const Measurable.mul_const
#align measurable.add_const Measurable.add_const
-/

#print AEMeasurable.mul_const /-
@[measurability, to_additive]
theorem AEMeasurable.mul_const [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x * c) μ :=
  (measurable_mul_const c).comp_aemeasurable hf
#align ae_measurable.mul_const AEMeasurable.mul_const
#align ae_measurable.add_const AEMeasurable.add_const
-/

#print Measurable.mul' /-
@[measurability, to_additive]
theorem Measurable.mul' [MeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f * g) :=
  measurable_mul.comp (hf.prod_mk hg)
#align measurable.mul' Measurable.mul'
#align measurable.add' Measurable.add'
-/

#print Measurable.mul /-
@[measurability, to_additive]
theorem Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a * g a :=
  measurable_mul.comp (hf.prod_mk hg)
#align measurable.mul Measurable.mul
#align measurable.add Measurable.add
-/

#print AEMeasurable.mul' /-
@[measurability, to_additive]
theorem AEMeasurable.mul' [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f * g) μ :=
  measurable_mul.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.mul' AEMeasurable.mul'
#align ae_measurable.add' AEMeasurable.add'
-/

#print AEMeasurable.mul /-
@[measurability, to_additive]
theorem AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a * g a) μ :=
  measurable_mul.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.mul AEMeasurable.mul
#align ae_measurable.add AEMeasurable.add
-/

#print MeasurableMul₂.toMeasurableMul /-
@[to_additive]
instance (priority := 100) MeasurableMul₂.toMeasurableMul [MeasurableMul₂ M] : MeasurableMul M :=
  ⟨fun c => measurable_const.mul measurable_id, fun c => measurable_id.mul measurable_const⟩
#align has_measurable_mul₂.to_has_measurable_mul MeasurableMul₂.toMeasurableMul
#align has_measurable_add₂.to_has_measurable_add MeasurableAdd₂.toMeasurableAdd
-/

#print Pi.measurableMul /-
@[to_additive]
instance Pi.measurableMul {ι : Type _} {α : ι → Type _} [∀ i, Mul (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableMul (α i)] : MeasurableMul (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_mul _, fun g =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).mul_const _⟩
#align pi.has_measurable_mul Pi.measurableMul
#align pi.has_measurable_add Pi.measurableAdd
-/

#print Pi.measurableMul₂ /-
@[to_additive Pi.measurableAdd₂]
instance Pi.measurableMul₂ {ι : Type _} {α : ι → Type _} [∀ i, Mul (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableMul₂ (α i)] : MeasurableMul₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => measurable_fst.eval.mul measurable_snd.eval⟩
#align pi.has_measurable_mul₂ Pi.measurableMul₂
#align pi.has_measurable_add₂ Pi.measurableAdd₂
-/

attribute [measurability] Measurable.add' Measurable.add AEMeasurable.add AEMeasurable.add'
  Measurable.const_add AEMeasurable.const_add Measurable.add_const AEMeasurable.add_const

end Mul

#print measurable_div_const' /-
/-- A version of `measurable_div_const` that assumes `has_measurable_mul` instead of
  `has_measurable_div`. This can be nice to avoid unnecessary type-class assumptions. -/
@[to_additive
      " A version of `measurable_sub_const` that assumes `has_measurable_add` instead of\n  `has_measurable_sub`. This can be nice to avoid unnecessary type-class assumptions. "]
theorem measurable_div_const' {G : Type _} [DivInvMonoid G] [MeasurableSpace G] [MeasurableMul G]
    (g : G) : Measurable fun h => h / g := by simp_rw [div_eq_mul_inv, measurable_mul_const]
#align measurable_div_const' measurable_div_const'
#align measurable_sub_const' measurable_sub_const'
-/

#print MeasurablePow /-
/-- This class assumes that the map `β × γ → β` given by `(x, y) ↦ x ^ y` is measurable. -/
class MeasurablePow (β γ : Type _) [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] where
  measurable_pow : Measurable fun p : β × γ => p.1 ^ p.2
#align has_measurable_pow MeasurablePow
-/

export MeasurablePow (measurable_pow)

#print Monoid.measurablePow /-
/-- `monoid.has_pow` is measurable. -/
instance Monoid.measurablePow (M : Type _) [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] :
    MeasurablePow M ℕ :=
  ⟨measurable_from_prod_countable fun n =>
      by
      induction' n with n ih
      · simp only [pow_zero, ← Pi.one_def, measurable_one]
      · simp only [pow_succ]; exact measurable_id.mul ih⟩
#align monoid.has_measurable_pow Monoid.measurablePow
-/

section Pow

variable {β γ α : Type _} [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] [MeasurablePow β γ]
  {m : MeasurableSpace α} {μ : Measure α} {f : α → β} {g : α → γ}

#print Measurable.pow /-
@[measurability]
theorem Measurable.pow (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x ^ g x :=
  measurable_pow.comp (hf.prod_mk hg)
#align measurable.pow Measurable.pow
-/

#print AEMeasurable.pow /-
@[measurability]
theorem AEMeasurable.pow (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => f x ^ g x) μ :=
  measurable_pow.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.pow AEMeasurable.pow
-/

#print Measurable.pow_const /-
@[measurability]
theorem Measurable.pow_const (hf : Measurable f) (c : γ) : Measurable fun x => f x ^ c :=
  hf.pow measurable_const
#align measurable.pow_const Measurable.pow_const
-/

#print AEMeasurable.pow_const /-
@[measurability]
theorem AEMeasurable.pow_const (hf : AEMeasurable f μ) (c : γ) :
    AEMeasurable (fun x => f x ^ c) μ :=
  hf.pow aemeasurable_const
#align ae_measurable.pow_const AEMeasurable.pow_const
-/

#print Measurable.const_pow /-
@[measurability]
theorem Measurable.const_pow (hg : Measurable g) (c : β) : Measurable fun x => c ^ g x :=
  measurable_const.pow hg
#align measurable.const_pow Measurable.const_pow
-/

#print AEMeasurable.const_pow /-
@[measurability]
theorem AEMeasurable.const_pow (hg : AEMeasurable g μ) (c : β) :
    AEMeasurable (fun x => c ^ g x) μ :=
  aemeasurable_const.pow hg
#align ae_measurable.const_pow AEMeasurable.const_pow
-/

end Pow

#print MeasurableSub /-
/-- We say that a type `has_measurable_sub` if `(λ x, c - x)` and `(λ x, x - c)` are measurable
functions. For a typeclass assuming measurability of `uncurry (-)` see `has_measurable_sub₂`. -/
class MeasurableSub (G : Type _) [MeasurableSpace G] [Sub G] : Prop where
  measurable_const_sub : ∀ c : G, Measurable fun x => c - x
  measurable_sub_const : ∀ c : G, Measurable fun x => x - c
#align has_measurable_sub MeasurableSub
-/

export MeasurableSub (measurable_const_sub measurable_sub_const)

#print MeasurableSub₂ /-
/-- We say that a type `has_measurable_sub` if `uncurry (-)` is a measurable functions.
For a typeclass assuming measurability of `((-) c)` and `(- c)` see `has_measurable_sub`. -/
class MeasurableSub₂ (G : Type _) [MeasurableSpace G] [Sub G] : Prop where
  measurable_sub : Measurable fun p : G × G => p.1 - p.2
#align has_measurable_sub₂ MeasurableSub₂
-/

export MeasurableSub₂ (measurable_sub)

#print MeasurableDiv /-
/-- We say that a type `has_measurable_div` if `((/) c)` and `(/ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (/)` see `has_measurable_div₂`. -/
@[to_additive]
class MeasurableDiv (G₀ : Type _) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_div_const : ∀ c : G₀, Measurable ((· / ·) c)
  measurable_div_const : ∀ c : G₀, Measurable (· / c)
#align has_measurable_div MeasurableDiv
#align has_measurable_sub MeasurableSub
-/

export MeasurableDiv (measurable_div_const measurable_div_const)

#print MeasurableDiv₂ /-
/-- We say that a type `has_measurable_div` if `uncurry (/)` is a measurable functions.
For a typeclass assuming measurability of `((/) c)` and `(/ c)` see `has_measurable_div`. -/
@[to_additive MeasurableSub₂]
class MeasurableDiv₂ (G₀ : Type _) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_div : Measurable fun p : G₀ × G₀ => p.1 / p.2
#align has_measurable_div₂ MeasurableDiv₂
#align has_measurable_sub₂ MeasurableSub₂
-/

export MeasurableDiv₂ (measurable_div)

section Div

variable {G α : Type _} [MeasurableSpace G] [Div G] {m : MeasurableSpace α} {f g : α → G}
  {μ : Measure α}

#print Measurable.const_div /-
@[measurability, to_additive]
theorem Measurable.const_div [MeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => c / f x :=
  (MeasurableDiv.measurable_div_const c).comp hf
#align measurable.const_div Measurable.const_div
#align measurable.const_sub Measurable.const_sub
-/

#print AEMeasurable.const_div /-
@[measurability, to_additive]
theorem AEMeasurable.const_div [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => c / f x) μ :=
  (MeasurableDiv.measurable_div_const c).comp_aemeasurable hf
#align ae_measurable.const_div AEMeasurable.const_div
#align ae_measurable.const_sub AEMeasurable.const_sub
-/

#print Measurable.div_const /-
@[measurability, to_additive]
theorem Measurable.div_const [MeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => f x / c :=
  (MeasurableDiv.measurable_div_const c).comp hf
#align measurable.div_const Measurable.div_const
#align measurable.sub_const Measurable.sub_const
-/

#print AEMeasurable.div_const /-
@[measurability, to_additive]
theorem AEMeasurable.div_const [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => f x / c) μ :=
  (MeasurableDiv.measurable_div_const c).comp_aemeasurable hf
#align ae_measurable.div_const AEMeasurable.div_const
#align ae_measurable.sub_const AEMeasurable.sub_const
-/

#print Measurable.div' /-
@[measurability, to_additive]
theorem Measurable.div' [MeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f / g) :=
  measurable_div.comp (hf.prod_mk hg)
#align measurable.div' Measurable.div'
#align measurable.sub' Measurable.sub'
-/

#print Measurable.div /-
@[measurability, to_additive]
theorem Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a / g a :=
  measurable_div.comp (hf.prod_mk hg)
#align measurable.div Measurable.div
#align measurable.sub Measurable.sub
-/

#print AEMeasurable.div' /-
@[measurability, to_additive]
theorem AEMeasurable.div' [MeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f / g) μ :=
  measurable_div.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.div' AEMeasurable.div'
#align ae_measurable.sub' AEMeasurable.sub'
-/

#print AEMeasurable.div /-
@[measurability, to_additive]
theorem AEMeasurable.div [MeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a / g a) μ :=
  measurable_div.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.div AEMeasurable.div
#align ae_measurable.sub AEMeasurable.sub
-/

attribute [measurability] Measurable.sub Measurable.sub' AEMeasurable.sub AEMeasurable.sub'
  Measurable.const_sub AEMeasurable.const_sub Measurable.sub_const AEMeasurable.sub_const

#print MeasurableDiv₂.toMeasurableDiv /-
@[to_additive]
instance (priority := 100) MeasurableDiv₂.toMeasurableDiv [MeasurableDiv₂ G] : MeasurableDiv G :=
  ⟨fun c => measurable_const.div measurable_id, fun c => measurable_id.div measurable_const⟩
#align has_measurable_div₂.to_has_measurable_div MeasurableDiv₂.toMeasurableDiv
#align has_measurable_sub₂.to_has_measurable_sub MeasurableSub₂.toMeasurableSub
-/

#print Pi.measurableDiv /-
@[to_additive]
instance Pi.measurableDiv {ι : Type _} {α : ι → Type _} [∀ i, Div (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableDiv (α i)] : MeasurableDiv (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_div _, fun g =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).div_const _⟩
#align pi.has_measurable_div Pi.measurableDiv
#align pi.has_measurable_sub Pi.measurableSub
-/

#print Pi.measurableDiv₂ /-
@[to_additive Pi.measurableSub₂]
instance Pi.measurableDiv₂ {ι : Type _} {α : ι → Type _} [∀ i, Div (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableDiv₂ (α i)] : MeasurableDiv₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => measurable_fst.eval.div measurable_snd.eval⟩
#align pi.has_measurable_div₂ Pi.measurableDiv₂
#align pi.has_measurable_sub₂ Pi.measurableSub₂
-/

#print measurableSet_eq_fun /-
@[measurability]
theorem measurableSet_eq_fun {m : MeasurableSpace α} {E} [MeasurableSpace E] [AddGroup E]
    [MeasurableSingletonClass E] [MeasurableSub₂ E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet {x | f x = g x} :=
  by
  suffices h_set_eq : {x : α | f x = g x} = {x | (f - g) x = (0 : E)}
  · rw [h_set_eq]
    exact (hf.sub hg) measurableSet_eq
  ext
  simp_rw [Set.mem_setOf_eq, Pi.sub_apply, sub_eq_zero]
#align measurable_set_eq_fun measurableSet_eq_fun
-/

#print nullMeasurableSet_eq_fun /-
theorem nullMeasurableSet_eq_fun {E} [MeasurableSpace E] [AddGroup E] [MeasurableSingletonClass E]
    [MeasurableSub₂ E] {f g : α → E} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    NullMeasurableSet {x | f x = g x} μ :=
  by
  apply (measurableSet_eq_fun hf.measurable_mk hg.measurable_mk).NullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x = hg.mk g x) = (f x = g x)
  simp only [hfx, hgx]
#align null_measurable_set_eq_fun nullMeasurableSet_eq_fun
-/

#print measurableSet_eq_fun_of_countable /-
theorem measurableSet_eq_fun_of_countable {m : MeasurableSpace α} {E} [MeasurableSpace E]
    [MeasurableSingletonClass E] [Countable E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet {x | f x = g x} :=
  by
  have : {x | f x = g x} = ⋃ j, {x | f x = j} ∩ {x | g x = j} := by ext1 x;
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_eq_right']
  rw [this]
  refine' MeasurableSet.iUnion fun j => MeasurableSet.inter _ _
  · exact hf (measurable_set_singleton j)
  · exact hg (measurable_set_singleton j)
#align measurable_set_eq_fun_of_countable measurableSet_eq_fun_of_countable
-/

#print ae_eq_trim_of_measurable /-
theorem ae_eq_trim_of_measurable {α E} {m m0 : MeasurableSpace α} {μ : Measure α}
    [MeasurableSpace E] [AddGroup E] [MeasurableSingletonClass E] [MeasurableSub₂ E] (hm : m ≤ m0)
    {f g : α → E} (hf : measurable[m] f) (hg : measurable[m] g) (hfg : f =ᵐ[μ] g) :
    f =ᶠ[@Measure.ae α m (μ.trim hm)] g :=
  by
  rwa [Filter.EventuallyEq, ae_iff, trim_measurable_set_eq hm _]
  exact @MeasurableSet.compl α _ m (@measurableSet_eq_fun α m E _ _ _ _ _ _ hf hg)
#align ae_eq_trim_of_measurable ae_eq_trim_of_measurable
-/

end Div

#print MeasurableNeg /-
/-- We say that a type `has_measurable_neg` if `x ↦ -x` is a measurable function. -/
class MeasurableNeg (G : Type _) [Neg G] [MeasurableSpace G] : Prop where
  measurable_neg : Measurable (Neg.neg : G → G)
#align has_measurable_neg MeasurableNeg
-/

#print MeasurableInv /-
/-- We say that a type `has_measurable_inv` if `x ↦ x⁻¹` is a measurable function. -/
@[to_additive]
class MeasurableInv (G : Type _) [Inv G] [MeasurableSpace G] : Prop where
  measurable_inv : Measurable (Inv.inv : G → G)
#align has_measurable_inv MeasurableInv
#align has_measurable_neg MeasurableNeg
-/

export MeasurableInv (measurable_inv)

export MeasurableNeg (measurable_neg)

#print measurableDiv_of_mul_inv /-
@[to_additive]
instance (priority := 100) measurableDiv_of_mul_inv (G : Type _) [MeasurableSpace G]
    [DivInvMonoid G] [MeasurableMul G] [MeasurableInv G] : MeasurableDiv G
    where
  measurable_div_const c := by convert measurable_inv.const_mul c; ext1; apply div_eq_mul_inv
  measurable_div_const c := by convert measurable_id.mul_const c⁻¹; ext1; apply div_eq_mul_inv
#align has_measurable_div_of_mul_inv measurableDiv_of_mul_inv
#align has_measurable_sub_of_add_neg measurableSub_of_add_neg
-/

section Inv

variable {G α : Type _} [Inv G] [MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}
  {f : α → G} {μ : Measure α}

#print Measurable.inv /-
@[measurability, to_additive]
theorem Measurable.inv (hf : Measurable f) : Measurable fun x => (f x)⁻¹ :=
  measurable_inv.comp hf
#align measurable.inv Measurable.inv
#align measurable.neg Measurable.neg
-/

#print AEMeasurable.inv /-
@[measurability, to_additive]
theorem AEMeasurable.inv (hf : AEMeasurable f μ) : AEMeasurable (fun x => (f x)⁻¹) μ :=
  measurable_inv.comp_aemeasurable hf
#align ae_measurable.inv AEMeasurable.inv
#align ae_measurable.neg AEMeasurable.neg
-/

attribute [measurability] Measurable.neg AEMeasurable.neg

#print measurable_inv_iff /-
@[simp, to_additive]
theorem measurable_inv_iff {G : Type _} [Group G] [MeasurableSpace G] [MeasurableInv G]
    {f : α → G} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align measurable_inv_iff measurable_inv_iff
#align measurable_neg_iff measurable_neg_iff
-/

#print aemeasurable_inv_iff /-
@[simp, to_additive]
theorem aemeasurable_inv_iff {G : Type _} [Group G] [MeasurableSpace G] [MeasurableInv G]
    {f : α → G} : AEMeasurable (fun x => (f x)⁻¹) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align ae_measurable_inv_iff aemeasurable_inv_iff
#align ae_measurable_neg_iff aemeasurable_neg_iff
-/

#print measurable_inv_iff₀ /-
@[simp]
theorem measurable_inv_iff₀ {G₀ : Type _} [GroupWithZero G₀] [MeasurableSpace G₀] [MeasurableInv G₀]
    {f : α → G₀} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align measurable_inv_iff₀ measurable_inv_iff₀
-/

#print aemeasurable_inv_iff₀ /-
@[simp]
theorem aemeasurable_inv_iff₀ {G₀ : Type _} [GroupWithZero G₀] [MeasurableSpace G₀]
    [MeasurableInv G₀] {f : α → G₀} : AEMeasurable (fun x => (f x)⁻¹) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align ae_measurable_inv_iff₀ aemeasurable_inv_iff₀
-/

#print Pi.measurableInv /-
@[to_additive]
instance Pi.measurableInv {ι : Type _} {α : ι → Type _} [∀ i, Inv (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableInv (α i)] : MeasurableInv (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => (measurable_pi_apply i).inv⟩
#align pi.has_measurable_inv Pi.measurableInv
#align pi.has_measurable_neg Pi.measurableNeg
-/

#print MeasurableSet.inv /-
@[to_additive]
theorem MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) : MeasurableSet s⁻¹ :=
  measurable_inv hs
#align measurable_set.inv MeasurableSet.inv
#align measurable_set.neg MeasurableSet.neg
-/

end Inv

#print DivInvMonoid.measurableZPow /-
/-- `div_inv_monoid.has_pow` is measurable. -/
instance DivInvMonoid.measurableZPow (G : Type u) [DivInvMonoid G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] : MeasurablePow G ℤ :=
  ⟨measurable_from_prod_countable fun n => by
      cases' n with n n
      · simp_rw [zpow_coe_nat]; exact measurable_id.pow_const _
      · simp_rw [zpow_negSucc]; exact (measurable_id.pow_const (n + 1)).inv⟩
#align div_inv_monoid.has_measurable_zpow DivInvMonoid.measurableZPow
-/

#print measurableDiv₂_of_mul_inv /-
@[to_additive]
instance (priority := 100) measurableDiv₂_of_mul_inv (G : Type _) [MeasurableSpace G]
    [DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G] : MeasurableDiv₂ G :=
  ⟨by simp only [div_eq_mul_inv]; exact measurable_fst.mul measurable_snd.inv⟩
#align has_measurable_div₂_of_mul_inv measurableDiv₂_of_mul_inv
#align has_measurable_div₂_of_add_neg measurableDiv₂_of_add_neg
-/

#print MeasurableVAdd /-
/-- We say that the action of `M` on `α` `has_measurable_vadd` if for each `c` the map `x ↦ c +ᵥ x`
is a measurable function and for each `x` the map `c ↦ c +ᵥ x` is a measurable function. -/
class MeasurableVAdd (M α : Type _) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α] : Prop where
  measurable_const_vadd : ∀ c : M, Measurable ((· +ᵥ ·) c : α → α)
  measurable_vadd_const : ∀ x : α, Measurable fun c : M => c +ᵥ x
#align has_measurable_vadd MeasurableVAdd
-/

#print MeasurableSMul /-
/-- We say that the action of `M` on `α` `has_measurable_smul` if for each `c` the map `x ↦ c • x`
is a measurable function and for each `x` the map `c ↦ c • x` is a measurable function. -/
@[to_additive]
class MeasurableSMul (M α : Type _) [SMul M α] [MeasurableSpace M] [MeasurableSpace α] : Prop where
  measurable_const_smul : ∀ c : M, Measurable ((· • ·) c : α → α)
  measurable_smul_const : ∀ x : α, Measurable fun c : M => c • x
#align has_measurable_smul MeasurableSMul
#align has_measurable_vadd MeasurableVAdd
-/

#print MeasurableVAdd₂ /-
/-- We say that the action of `M` on `α` `has_measurable_vadd₂` if the map
`(c, x) ↦ c +ᵥ x` is a measurable function. -/
class MeasurableVAdd₂ (M α : Type _) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α] : Prop where
  measurable_vadd : Measurable (Function.uncurry (· +ᵥ ·) : M × α → α)
#align has_measurable_vadd₂ MeasurableVAdd₂
-/

#print MeasurableSMul₂ /-
/-- We say that the action of `M` on `α` `has_measurable_smul₂` if the map
`(c, x) ↦ c • x` is a measurable function. -/
@[to_additive MeasurableVAdd₂]
class MeasurableSMul₂ (M α : Type _) [SMul M α] [MeasurableSpace M] [MeasurableSpace α] : Prop where
  measurable_smul : Measurable (Function.uncurry (· • ·) : M × α → α)
#align has_measurable_smul₂ MeasurableSMul₂
#align has_measurable_vadd₂ MeasurableVAdd₂
-/

export MeasurableSMul (measurable_const_smul measurable_smul_const)

export MeasurableSMul₂ (measurable_smul)

export MeasurableVAdd (measurable_const_vadd measurable_vadd_const)

export MeasurableVAdd₂ (measurable_vadd)

#print measurableSMul_of_mul /-
@[to_additive]
instance measurableSMul_of_mul (M : Type _) [Mul M] [MeasurableSpace M] [MeasurableMul M] :
    MeasurableSMul M M :=
  ⟨measurable_id.const_mul, measurable_id.mul_const⟩
#align has_measurable_smul_of_mul measurableSMul_of_mul
#align has_measurable_vadd_of_add measurableVAdd_of_add
-/

#print measurableSMul₂_of_mul /-
@[to_additive]
instance measurableSMul₂_of_mul (M : Type _) [Mul M] [MeasurableSpace M] [MeasurableMul₂ M] :
    MeasurableSMul₂ M M :=
  ⟨measurable_mul⟩
#align has_measurable_smul₂_of_mul measurableSMul₂_of_mul
#align has_measurable_smul₂_of_add measurableSMul₂_of_add
-/

#print Submonoid.measurableSMul /-
@[to_additive]
instance Submonoid.measurableSMul {M α} [MeasurableSpace M] [MeasurableSpace α] [Monoid M]
    [MulAction M α] [MeasurableSMul M α] (s : Submonoid M) : MeasurableSMul s α :=
  ⟨fun c => by simpa only using measurable_const_smul (c : M), fun x =>
    (measurable_smul_const x : Measurable fun c : M => c • x).comp measurable_subtype_coe⟩
#align submonoid.has_measurable_smul Submonoid.measurableSMul
#align add_submonoid.has_measurable_vadd AddSubmonoid.measurableVAdd
-/

#print Subgroup.measurableSMul /-
@[to_additive]
instance Subgroup.measurableSMul {G α} [MeasurableSpace G] [MeasurableSpace α] [Group G]
    [MulAction G α] [MeasurableSMul G α] (s : Subgroup G) : MeasurableSMul s α :=
  s.toSubmonoid.MeasurableSMul
#align subgroup.has_measurable_smul Subgroup.measurableSMul
#align add_subgroup.has_measurable_vadd AddSubgroup.measurableVAdd
-/

section Smul

variable {M β α : Type _} [MeasurableSpace M] [MeasurableSpace β] [SMul M β] {m : MeasurableSpace α}
  {f : α → M} {g : α → β}

#print Measurable.smul /-
@[measurability, to_additive]
theorem Measurable.smul [MeasurableSMul₂ M β] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x • g x :=
  measurable_smul.comp (hf.prod_mk hg)
#align measurable.smul Measurable.smul
#align measurable.vadd Measurable.vadd
-/

#print AEMeasurable.smul /-
@[measurability, to_additive]
theorem AEMeasurable.smul [MeasurableSMul₂ M β] {μ : Measure α} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun x => f x • g x) μ :=
  MeasurableSMul₂.measurable_smul.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.smul AEMeasurable.smul
#align ae_measurable.vadd AEMeasurable.vadd
-/

#print MeasurableSMul₂.toMeasurableSMul /-
@[to_additive]
instance (priority := 100) MeasurableSMul₂.toMeasurableSMul [MeasurableSMul₂ M β] :
    MeasurableSMul M β :=
  ⟨fun c => measurable_const.smul measurable_id, fun y => measurable_id.smul measurable_const⟩
#align has_measurable_smul₂.to_has_measurable_smul MeasurableSMul₂.toMeasurableSMul
#align has_measurable_vadd₂.to_has_measurable_vadd MeasurableVAdd₂.toMeasurableVAdd
-/

variable [MeasurableSMul M β] {μ : Measure α}

#print Measurable.smul_const /-
@[measurability, to_additive]
theorem Measurable.smul_const (hf : Measurable f) (y : β) : Measurable fun x => f x • y :=
  (MeasurableSMul.measurable_smul_const y).comp hf
#align measurable.smul_const Measurable.smul_const
#align measurable.vadd_const Measurable.vadd_const
-/

#print AEMeasurable.smul_const /-
@[measurability, to_additive]
theorem AEMeasurable.smul_const (hf : AEMeasurable f μ) (y : β) :
    AEMeasurable (fun x => f x • y) μ :=
  (MeasurableSMul.measurable_smul_const y).comp_aemeasurable hf
#align ae_measurable.smul_const AEMeasurable.smul_const
#align ae_measurable.vadd_const AEMeasurable.vadd_const
-/

#print Measurable.const_smul' /-
@[measurability, to_additive]
theorem Measurable.const_smul' (hg : Measurable g) (c : M) : Measurable fun x => c • g x :=
  (MeasurableSMul.measurable_const_smul c).comp hg
#align measurable.const_smul' Measurable.const_smul'
#align measurable.const_vadd' Measurable.const_vadd'
-/

#print Measurable.const_smul /-
@[measurability, to_additive]
theorem Measurable.const_smul (hg : Measurable g) (c : M) : Measurable (c • g) :=
  hg.const_smul' c
#align measurable.const_smul Measurable.const_smul
#align measurable.const_vadd Measurable.const_vadd
-/

#print AEMeasurable.const_smul' /-
@[measurability, to_additive]
theorem AEMeasurable.const_smul' (hg : AEMeasurable g μ) (c : M) :
    AEMeasurable (fun x => c • g x) μ :=
  (MeasurableSMul.measurable_const_smul c).comp_aemeasurable hg
#align ae_measurable.const_smul' AEMeasurable.const_smul'
#align ae_measurable.const_vadd' AEMeasurable.const_vadd'
-/

#print AEMeasurable.const_smul /-
@[measurability, to_additive]
theorem AEMeasurable.const_smul (hf : AEMeasurable g μ) (c : M) : AEMeasurable (c • g) μ :=
  hf.const_smul' c
#align ae_measurable.const_smul AEMeasurable.const_smul
#align ae_measurable.const_vadd AEMeasurable.const_vadd
-/

#print Pi.measurableSMul /-
@[to_additive]
instance Pi.measurableSMul {ι : Type _} {α : ι → Type _} [∀ i, SMul M (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSMul M (α i)] : MeasurableSMul M (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_smul _, fun g =>
    measurable_pi_iff.mpr fun i => measurable_smul_const _⟩
#align pi.has_measurable_smul Pi.measurableSMul
#align pi.has_measurable_vadd Pi.measurableVAdd
-/

#print AddMonoid.measurableSMul_nat₂ /-
/-- `add_monoid.has_smul_nat` is measurable. -/
instance AddMonoid.measurableSMul_nat₂ (M : Type _) [AddMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] : MeasurableSMul₂ ℕ M :=
  ⟨by
    suffices Measurable fun p : M × ℕ => p.2 • p.1 by apply this.comp measurable_swap
    refine' measurable_from_prod_countable fun n => _
    induction' n with n ih
    · simp only [zero_smul, ← Pi.zero_def, measurable_zero]
    · simp only [succ_nsmul]; exact measurable_id.add ih⟩
#align add_monoid.has_measurable_smul_nat₂ AddMonoid.measurableSMul_nat₂
-/

#print SubNegMonoid.measurableSMul_int₂ /-
/-- `sub_neg_monoid.has_smul_int` is measurable. -/
instance SubNegMonoid.measurableSMul_int₂ (M : Type _) [SubNegMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] [MeasurableNeg M] : MeasurableSMul₂ ℤ M :=
  ⟨by
    suffices Measurable fun p : M × ℤ => p.2 • p.1 by apply this.comp measurable_swap
    refine' measurable_from_prod_countable fun n => _
    induction' n with n n ih
    · simp only [coe_nat_zsmul]; exact measurable_const_smul _
    · simp only [negSucc_zsmul]; exact (measurable_const_smul _).neg⟩
#align sub_neg_monoid.has_measurable_smul_int₂ SubNegMonoid.measurableSMul_int₂
-/

end Smul

section MulAction

variable {M β α : Type _} [MeasurableSpace M] [MeasurableSpace β] [Monoid M] [MulAction M β]
  [MeasurableSMul M β] [MeasurableSpace α] {f : α → β} {μ : Measure α}

variable {G : Type _} [Group G] [MeasurableSpace G] [MulAction G β] [MeasurableSMul G β]

#print measurable_const_smul_iff /-
@[to_additive]
theorem measurable_const_smul_iff (c : G) : (Measurable fun x => c • f x) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align measurable_const_smul_iff measurable_const_smul_iff
#align measurable_const_vadd_iff measurable_const_vadd_iff
-/

#print aemeasurable_const_smul_iff /-
@[to_additive]
theorem aemeasurable_const_smul_iff (c : G) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align ae_measurable_const_smul_iff aemeasurable_const_smul_iff
#align ae_measurable_const_vadd_iff aemeasurable_const_vadd_iff
-/

@[to_additive]
instance : MeasurableSpace Mˣ :=
  MeasurableSpace.comap (coe : Mˣ → M) ‹_›

#print Units.measurableSMul /-
@[to_additive]
instance Units.measurableSMul : MeasurableSMul Mˣ β
    where
  measurable_const_smul c := (measurable_const_smul (c : M) : _)
  measurable_smul_const x :=
    (measurable_smul_const x : Measurable fun c : M => c • x).comp MeasurableSpace.le_map_comap
#align units.has_measurable_smul Units.measurableSMul
#align add_units.has_measurable_vadd AddUnits.measurableVAdd
-/

#print IsUnit.measurable_const_smul_iff /-
@[to_additive]
theorem IsUnit.measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ measurable_const_smul_iff u
#align is_unit.measurable_const_smul_iff IsUnit.measurable_const_smul_iff
#align is_add_unit.measurable_const_vadd_iff IsAddUnit.measurable_const_vadd_iff
-/

#print IsUnit.aemeasurable_const_smul_iff /-
@[to_additive]
theorem IsUnit.aemeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aemeasurable_const_smul_iff u
#align is_unit.ae_measurable_const_smul_iff IsUnit.aemeasurable_const_smul_iff
#align is_add_unit.ae_measurable_const_vadd_iff IsAddUnit.aemeasurable_const_vadd_iff
-/

variable {G₀ : Type _} [GroupWithZero G₀] [MeasurableSpace G₀] [MulAction G₀ β]
  [MeasurableSMul G₀ β]

#print measurable_const_smul_iff₀ /-
theorem measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  (IsUnit.mk0 c hc).measurable_const_smul_iff
#align measurable_const_smul_iff₀ measurable_const_smul_iff₀
-/

#print aemeasurable_const_smul_iff₀ /-
theorem aemeasurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  (IsUnit.mk0 c hc).aemeasurable_const_smul_iff
#align ae_measurable_const_smul_iff₀ aemeasurable_const_smul_iff₀
-/

end MulAction

/-!
### Opposite monoid
-/


section Opposite

open MulOpposite

@[to_additive]
instance {α : Type _} [h : MeasurableSpace α] : MeasurableSpace αᵐᵒᵖ :=
  MeasurableSpace.map op h

#print measurable_mul_op /-
@[to_additive]
theorem measurable_mul_op {α : Type _} [MeasurableSpace α] : Measurable (op : α → αᵐᵒᵖ) := fun s =>
  id
#align measurable_mul_op measurable_mul_op
#align measurable_add_op measurable_add_op
-/

#print measurable_mul_unop /-
@[to_additive]
theorem measurable_mul_unop {α : Type _} [MeasurableSpace α] : Measurable (unop : αᵐᵒᵖ → α) :=
  fun s => id
#align measurable_mul_unop measurable_mul_unop
#align measurable_add_unop measurable_add_unop
-/

@[to_additive]
instance {M : Type _} [Mul M] [MeasurableSpace M] [MeasurableMul M] : MeasurableMul Mᵐᵒᵖ :=
  ⟨fun c => measurable_mul_op.comp (measurable_mul_unop.mul_const _), fun c =>
    measurable_mul_op.comp (measurable_mul_unop.const_mul _)⟩

@[to_additive]
instance {M : Type _} [Mul M] [MeasurableSpace M] [MeasurableMul₂ M] : MeasurableMul₂ Mᵐᵒᵖ :=
  ⟨measurable_mul_op.comp
      ((measurable_mul_unop.comp measurable_snd).mul (measurable_mul_unop.comp measurable_fst))⟩

#print MeasurableSMul.op /-
/-- If a scalar is central, then its right action is measurable when its left action is. -/
instance MeasurableSMul.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α] [SMul Mᵐᵒᵖ α]
    [IsCentralScalar M α] [MeasurableSMul M α] : MeasurableSMul Mᵐᵒᵖ α :=
  ⟨MulOpposite.rec' fun c =>
      show Measurable fun x => op c • x by
        simpa only [op_smul_eq_smul] using measurable_const_smul c,
    fun x =>
    show Measurable fun c => op (unop c) • x by
      simpa only [op_smul_eq_smul] using (measurable_smul_const x).comp measurable_mul_unop⟩
#align has_measurable_smul.op MeasurableSMul.op
-/

#print MeasurableSMul₂.op /-
/-- If a scalar is central, then its right action is measurable when its left action is. -/
instance MeasurableSMul₂.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α] [SMul Mᵐᵒᵖ α]
    [IsCentralScalar M α] [MeasurableSMul₂ M α] : MeasurableSMul₂ Mᵐᵒᵖ α :=
  ⟨show Measurable fun x : Mᵐᵒᵖ × α => op (unop x.1) • x.2
      by
      simp_rw [op_smul_eq_smul]
      refine' (measurable_mul_unop.comp measurable_fst).smul measurable_snd⟩
#align has_measurable_smul₂.op MeasurableSMul₂.op
-/

#print measurableSMul_opposite_of_mul /-
@[to_additive]
instance measurableSMul_opposite_of_mul {M : Type _} [Mul M] [MeasurableSpace M] [MeasurableMul M] :
    MeasurableSMul Mᵐᵒᵖ M :=
  ⟨fun c => measurable_mul_const (unop c), fun x => measurable_mul_unop.const_mul x⟩
#align has_measurable_smul_opposite_of_mul measurableSMul_opposite_of_mul
#align has_measurable_vadd_opposite_of_add measurableVAdd_opposite_of_add
-/

#print measurableSMul₂_opposite_of_mul /-
@[to_additive]
instance measurableSMul₂_opposite_of_mul {M : Type _} [Mul M] [MeasurableSpace M]
    [MeasurableMul₂ M] : MeasurableSMul₂ Mᵐᵒᵖ M :=
  ⟨measurable_snd.mul (measurable_mul_unop.comp measurable_fst)⟩
#align has_measurable_smul₂_opposite_of_mul measurableSMul₂_opposite_of_mul
#align has_measurable_smul₂_opposite_of_add measurableSMul₂_opposite_of_add
-/

end Opposite

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M α : Type _} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] {m : MeasurableSpace α}
  {μ : Measure α}

#print List.measurable_prod' /-
@[measurability, to_additive]
theorem List.measurable_prod' (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) : Measurable l.Prod :=
  by
  induction' l with f l ihl; · exact measurable_one
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.measurable_prod' List.measurable_prod'
#align list.measurable_sum' List.measurable_sum'
-/

#print List.aemeasurable_prod' /-
@[measurability, to_additive]
theorem List.aemeasurable_prod' (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.Prod μ := by
  induction' l with f l ihl; · exact aemeasurable_one
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.ae_measurable_prod' List.aemeasurable_prod'
#align list.ae_measurable_sum' List.aemeasurable_sum'
-/

#print List.measurable_prod /-
@[measurability, to_additive]
theorem List.measurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable fun x => (l.map fun f : α → M => f x).Prod := by
  simpa only [← Pi.list_prod_apply] using l.measurable_prod' hl
#align list.measurable_prod List.measurable_prod
#align list.measurable_sum List.measurable_sum
-/

#print List.aemeasurable_prod /-
@[measurability, to_additive]
theorem List.aemeasurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable (fun x => (l.map fun f : α → M => f x).Prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.ae_measurable_prod' hl
#align list.ae_measurable_prod List.aemeasurable_prod
#align list.ae_measurable_sum List.aemeasurable_sum
-/

end Monoid

section CommMonoid

variable {M ι α : Type _} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M]
  {m : MeasurableSpace α} {μ : Measure α} {f : ι → α → M}

#print Multiset.measurable_prod' /-
@[measurability, to_additive]
theorem Multiset.measurable_prod' (l : Multiset (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable l.Prod := by rcases l with ⟨l⟩; simpa using l.measurable_prod' (by simpa using hl)
#align multiset.measurable_prod' Multiset.measurable_prod'
#align multiset.measurable_sum' Multiset.measurable_sum'
-/

#print Multiset.aemeasurable_prod' /-
@[measurability, to_additive]
theorem Multiset.aemeasurable_prod' (l : Multiset (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.Prod μ := by rcases l with ⟨l⟩;
  simpa using l.ae_measurable_prod' (by simpa using hl)
#align multiset.ae_measurable_prod' Multiset.aemeasurable_prod'
#align multiset.ae_measurable_sum' Multiset.aemeasurable_sum'
-/

#print Multiset.measurable_prod /-
@[measurability, to_additive]
theorem Multiset.measurable_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, Measurable f) :
    Measurable fun x => (s.map fun f : α → M => f x).Prod := by
  simpa only [← Pi.multiset_prod_apply] using s.measurable_prod' hs
#align multiset.measurable_prod Multiset.measurable_prod
#align multiset.measurable_sum Multiset.measurable_sum
-/

#print Multiset.aemeasurable_prod /-
@[measurability, to_additive]
theorem Multiset.aemeasurable_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, AEMeasurable f μ) :
    AEMeasurable (fun x => (s.map fun f : α → M => f x).Prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.ae_measurable_prod' hs
#align multiset.ae_measurable_prod Multiset.aemeasurable_prod
#align multiset.ae_measurable_sum Multiset.aemeasurable_sum
-/

#print Finset.measurable_prod' /-
@[measurability, to_additive]
theorem Finset.measurable_prod' (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (∏ i in s, f i) :=
  Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf
#align finset.measurable_prod' Finset.measurable_prod'
#align finset.measurable_sum' Finset.measurable_sum'
-/

#print Finset.measurable_prod /-
@[measurability, to_additive]
theorem Finset.measurable_prod (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun a => ∏ i in s, f i a := by
  simpa only [← Finset.prod_apply] using s.measurable_prod' hf
#align finset.measurable_prod Finset.measurable_prod
#align finset.measurable_sum Finset.measurable_sum
-/

#print Finset.aemeasurable_prod' /-
@[measurability, to_additive]
theorem Finset.aemeasurable_prod' (s : Finset ι) (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (∏ i in s, f i) μ :=
  Multiset.aemeasurable_prod' _ fun g hg =>
    let ⟨i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi
#align finset.ae_measurable_prod' Finset.aemeasurable_prod'
#align finset.ae_measurable_sum' Finset.aemeasurable_sum'
-/

#print Finset.aemeasurable_prod /-
@[measurability, to_additive]
theorem Finset.aemeasurable_prod (s : Finset ι) (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (fun a => ∏ i in s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.ae_measurable_prod' hf
#align finset.ae_measurable_prod Finset.aemeasurable_prod
#align finset.ae_measurable_sum Finset.aemeasurable_sum
-/

end CommMonoid

