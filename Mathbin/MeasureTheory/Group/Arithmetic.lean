/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.group.arithmetic
! leanprover-community/mathlib commit 781cb2eed038c4caf53bdbd8d20a95e5822d77df
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.AeMeasurable

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

open BigOperators Pointwise MeasureTheory

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

include m

/- warning: measurable.const_mul -> Measurable.const_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : Mul.{u1} M] {m : MeasurableSpace.{u2} α} {f : α -> M} [_inst_3 : MeasurableMul.{u1} M _inst_1 _inst_2], (Measurable.{u2, u1} α M m _inst_1 f) -> (forall (c : M), Measurable.{u2, u1} α M m _inst_1 (fun (x : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_2) c (f x)))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} M] [_inst_2 : Mul.{u2} M] {m : MeasurableSpace.{u1} α} {f : α -> M} [_inst_3 : MeasurableMul.{u2} M _inst_1 _inst_2], (Measurable.{u1, u2} α M m _inst_1 f) -> (forall (c : M), Measurable.{u1, u2} α M m _inst_1 (fun (x : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_2) c (f x)))
Case conversion may be inaccurate. Consider using '#align measurable.const_mul Measurable.const_mulₓ'. -/
@[measurability, to_additive]
theorem Measurable.const_mul [MeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => c * f x :=
  (measurable_const_mul c).comp hf
#align measurable.const_mul Measurable.const_mul
#align measurable.const_add Measurable.const_add

/- warning: ae_measurable.const_mul -> AEMeasurable.const_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : Mul.{u1} M] {m : MeasurableSpace.{u2} α} {f : α -> M} {μ : MeasureTheory.Measure.{u2} α m} [_inst_3 : MeasurableMul.{u1} M _inst_1 _inst_2], (AEMeasurable.{u2, u1} α M _inst_1 m f μ) -> (forall (c : M), AEMeasurable.{u2, u1} α M _inst_1 m (fun (x : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_2) c (f x)) μ)
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} M] [_inst_2 : Mul.{u2} M] {m : MeasurableSpace.{u1} α} {f : α -> M} {μ : MeasureTheory.Measure.{u1} α m} [_inst_3 : MeasurableMul.{u2} M _inst_1 _inst_2], (AEMeasurable.{u1, u2} α M _inst_1 m f μ) -> (forall (c : M), AEMeasurable.{u1, u2} α M _inst_1 m (fun (x : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_2) c (f x)) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.const_mul AEMeasurable.const_mulₓ'. -/
@[measurability, to_additive]
theorem AEMeasurable.const_mul [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c * f x) μ :=
  (MeasurableMul.measurable_const_mul c).comp_aemeasurable hf
#align ae_measurable.const_mul AEMeasurable.const_mul
#align ae_measurable.const_add AEMeasurable.const_add

/- warning: measurable.mul_const -> Measurable.mul_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : Mul.{u1} M] {m : MeasurableSpace.{u2} α} {f : α -> M} [_inst_3 : MeasurableMul.{u1} M _inst_1 _inst_2], (Measurable.{u2, u1} α M m _inst_1 f) -> (forall (c : M), Measurable.{u2, u1} α M m _inst_1 (fun (x : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_2) (f x) c))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} M] [_inst_2 : Mul.{u2} M] {m : MeasurableSpace.{u1} α} {f : α -> M} [_inst_3 : MeasurableMul.{u2} M _inst_1 _inst_2], (Measurable.{u1, u2} α M m _inst_1 f) -> (forall (c : M), Measurable.{u1, u2} α M m _inst_1 (fun (x : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_2) (f x) c))
Case conversion may be inaccurate. Consider using '#align measurable.mul_const Measurable.mul_constₓ'. -/
@[measurability, to_additive]
theorem Measurable.mul_const [MeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => f x * c :=
  (measurable_mul_const c).comp hf
#align measurable.mul_const Measurable.mul_const
#align measurable.add_const Measurable.add_const

/- warning: ae_measurable.mul_const -> AEMeasurable.mul_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : Mul.{u1} M] {m : MeasurableSpace.{u2} α} {f : α -> M} {μ : MeasureTheory.Measure.{u2} α m} [_inst_3 : MeasurableMul.{u1} M _inst_1 _inst_2], (AEMeasurable.{u2, u1} α M _inst_1 m f μ) -> (forall (c : M), AEMeasurable.{u2, u1} α M _inst_1 m (fun (x : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_2) (f x) c) μ)
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} M] [_inst_2 : Mul.{u2} M] {m : MeasurableSpace.{u1} α} {f : α -> M} {μ : MeasureTheory.Measure.{u1} α m} [_inst_3 : MeasurableMul.{u2} M _inst_1 _inst_2], (AEMeasurable.{u1, u2} α M _inst_1 m f μ) -> (forall (c : M), AEMeasurable.{u1, u2} α M _inst_1 m (fun (x : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_2) (f x) c) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.mul_const AEMeasurable.mul_constₓ'. -/
@[measurability, to_additive]
theorem AEMeasurable.mul_const [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x * c) μ :=
  (measurable_mul_const c).comp_aemeasurable hf
#align ae_measurable.mul_const AEMeasurable.mul_const
#align ae_measurable.add_const AEMeasurable.add_const

/- warning: measurable.mul' -> Measurable.mul' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : Mul.{u1} M] {m : MeasurableSpace.{u2} α} {f : α -> M} {g : α -> M} [_inst_3 : MeasurableMul₂.{u1} M _inst_1 _inst_2], (Measurable.{u2, u1} α M m _inst_1 f) -> (Measurable.{u2, u1} α M m _inst_1 g) -> (Measurable.{u2, u1} α M m _inst_1 (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2))) f g))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} M] [_inst_2 : Mul.{u2} M] {m : MeasurableSpace.{u1} α} {f : α -> M} {g : α -> M} [_inst_3 : MeasurableMul₂.{u2} M _inst_1 _inst_2], (Measurable.{u1, u2} α M m _inst_1 f) -> (Measurable.{u1, u2} α M m _inst_1 g) -> (Measurable.{u1, u2} α M m _inst_1 (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2))) f g))
Case conversion may be inaccurate. Consider using '#align measurable.mul' Measurable.mul'ₓ'. -/
@[measurability, to_additive]
theorem Measurable.mul' [MeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f * g) :=
  measurable_mul.comp (hf.prod_mk hg)
#align measurable.mul' Measurable.mul'
#align measurable.add' Measurable.add'

/- warning: measurable.mul -> Measurable.mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : Mul.{u1} M] {m : MeasurableSpace.{u2} α} {f : α -> M} {g : α -> M} [_inst_3 : MeasurableMul₂.{u1} M _inst_1 _inst_2], (Measurable.{u2, u1} α M m _inst_1 f) -> (Measurable.{u2, u1} α M m _inst_1 g) -> (Measurable.{u2, u1} α M m _inst_1 (fun (a : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_2) (f a) (g a)))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} M] [_inst_2 : Mul.{u2} M] {m : MeasurableSpace.{u1} α} {f : α -> M} {g : α -> M} [_inst_3 : MeasurableMul₂.{u2} M _inst_1 _inst_2], (Measurable.{u1, u2} α M m _inst_1 f) -> (Measurable.{u1, u2} α M m _inst_1 g) -> (Measurable.{u1, u2} α M m _inst_1 (fun (a : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_2) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align measurable.mul Measurable.mulₓ'. -/
@[measurability, to_additive]
theorem Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a * g a :=
  measurable_mul.comp (hf.prod_mk hg)
#align measurable.mul Measurable.mul
#align measurable.add Measurable.add

/- warning: ae_measurable.mul' -> AEMeasurable.mul' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : Mul.{u1} M] {m : MeasurableSpace.{u2} α} {f : α -> M} {g : α -> M} {μ : MeasureTheory.Measure.{u2} α m} [_inst_3 : MeasurableMul₂.{u1} M _inst_1 _inst_2], (AEMeasurable.{u2, u1} α M _inst_1 m f μ) -> (AEMeasurable.{u2, u1} α M _inst_1 m g μ) -> (AEMeasurable.{u2, u1} α M _inst_1 m (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2))) f g) μ)
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} M] [_inst_2 : Mul.{u2} M] {m : MeasurableSpace.{u1} α} {f : α -> M} {g : α -> M} {μ : MeasureTheory.Measure.{u1} α m} [_inst_3 : MeasurableMul₂.{u2} M _inst_1 _inst_2], (AEMeasurable.{u1, u2} α M _inst_1 m f μ) -> (AEMeasurable.{u1, u2} α M _inst_1 m g μ) -> (AEMeasurable.{u1, u2} α M _inst_1 m (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> M) (α -> M) (α -> M) (instHMul.{max u2 u1} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_2))) f g) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.mul' AEMeasurable.mul'ₓ'. -/
@[measurability, to_additive]
theorem AEMeasurable.mul' [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f * g) μ :=
  measurable_mul.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.mul' AEMeasurable.mul'
#align ae_measurable.add' AEMeasurable.add'

/- warning: ae_measurable.mul -> AEMeasurable.mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : Mul.{u1} M] {m : MeasurableSpace.{u2} α} {f : α -> M} {g : α -> M} {μ : MeasureTheory.Measure.{u2} α m} [_inst_3 : MeasurableMul₂.{u1} M _inst_1 _inst_2], (AEMeasurable.{u2, u1} α M _inst_1 m f μ) -> (AEMeasurable.{u2, u1} α M _inst_1 m g μ) -> (AEMeasurable.{u2, u1} α M _inst_1 m (fun (a : α) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_2) (f a) (g a)) μ)
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} M] [_inst_2 : Mul.{u2} M] {m : MeasurableSpace.{u1} α} {f : α -> M} {g : α -> M} {μ : MeasureTheory.Measure.{u1} α m} [_inst_3 : MeasurableMul₂.{u2} M _inst_1 _inst_2], (AEMeasurable.{u1, u2} α M _inst_1 m f μ) -> (AEMeasurable.{u1, u2} α M _inst_1 m g μ) -> (AEMeasurable.{u1, u2} α M _inst_1 m (fun (a : α) => HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_2) (f a) (g a)) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.mul AEMeasurable.mulₓ'. -/
@[measurability, to_additive]
theorem AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a * g a) μ :=
  measurable_mul.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.mul AEMeasurable.mul
#align ae_measurable.add AEMeasurable.add

omit m

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

attribute [measurability]
  Measurable.add' Measurable.add AEMeasurable.add AEMeasurable.add' Measurable.const_add AEMeasurable.const_add Measurable.add_const AEMeasurable.add_const

end Mul

/- warning: measurable_div_const' -> measurable_div_const' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] [_inst_2 : MeasurableSpace.{u1} G] [_inst_3 : MeasurableMul.{u1} G _inst_2 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))] (g : G), Measurable.{u1, u1} G G _inst_2 _inst_2 (fun (h : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G _inst_1)) h g)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : DivInvMonoid.{u1} G] [_inst_2 : MeasurableSpace.{u1} G] [_inst_3 : MeasurableMul.{u1} G _inst_2 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))] (g : G), Measurable.{u1, u1} G G _inst_2 _inst_2 (fun (h : G) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toDiv.{u1} G _inst_1)) h g)
Case conversion may be inaccurate. Consider using '#align measurable_div_const' measurable_div_const'ₓ'. -/
/-- A version of `measurable_div_const` that assumes `has_measurable_mul` instead of
  `has_measurable_div`. This can be nice to avoid unnecessary type-class assumptions. -/
@[to_additive
      " A version of `measurable_sub_const` that assumes `has_measurable_add` instead of\n  `has_measurable_sub`. This can be nice to avoid unnecessary type-class assumptions. "]
theorem measurable_div_const' {G : Type _} [DivInvMonoid G] [MeasurableSpace G] [MeasurableMul G]
    (g : G) : Measurable fun h => h / g := by simp_rw [div_eq_mul_inv, measurable_mul_const]
#align measurable_div_const' measurable_div_const'
#align measurable_sub_const' measurable_sub_const'

#print MeasurablePow /-
/-- This class assumes that the map `β × γ → β` given by `(x, y) ↦ x ^ y` is measurable. -/
class MeasurablePow (β γ : Type _) [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] where
  measurable_pow : Measurable fun p : β × γ => p.1 ^ p.2
#align has_measurable_pow MeasurablePow
-/

export MeasurablePow (measurable_pow)

/- warning: monoid.has_measurable_pow -> Monoid.measurablePow is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : Monoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))], MeasurablePow.{u1, 0} M Nat _inst_2 Nat.instMeasurableSpace (Monoid.Pow.{u1} M _inst_1)
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : Monoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))], MeasurablePow.{u1, 0} M Nat _inst_2 Nat.instMeasurableSpace (Monoid.Pow.{u1} M _inst_1)
Case conversion may be inaccurate. Consider using '#align monoid.has_measurable_pow Monoid.measurablePowₓ'. -/
/-- `monoid.has_pow` is measurable. -/
instance Monoid.measurablePow (M : Type _) [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] :
    MeasurablePow M ℕ :=
  ⟨measurable_from_prod_countable fun n =>
      by
      induction' n with n ih
      · simp only [pow_zero, ← Pi.one_def, measurable_one]
      · simp only [pow_succ]; exact measurable_id.mul ih⟩
#align monoid.has_measurable_pow Monoid.measurablePow

section Pow

variable {β γ α : Type _} [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] [MeasurablePow β γ]
  {m : MeasurableSpace α} {μ : Measure α} {f : α → β} {g : α → γ}

include m

/- warning: measurable.pow -> Measurable.pow is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} β] [_inst_2 : MeasurableSpace.{u2} γ] [_inst_3 : Pow.{u1, u2} β γ] [_inst_4 : MeasurablePow.{u1, u2} β γ _inst_1 _inst_2 _inst_3] {m : MeasurableSpace.{u3} α} {f : α -> β} {g : α -> γ}, (Measurable.{u3, u1} α β m _inst_1 f) -> (Measurable.{u3, u2} α γ m _inst_2 g) -> (Measurable.{u3, u1} α β m _inst_1 (fun (x : α) => HPow.hPow.{u1, u2, u1} β γ β (instHPow.{u1, u2} β γ _inst_3) (f x) (g x)))
but is expected to have type
  forall {β : Type.{u2}} {γ : Type.{u1}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u1} γ] [_inst_3 : Pow.{u2, u1} β γ] [_inst_4 : MeasurablePow.{u2, u1} β γ _inst_1 _inst_2 _inst_3] {m : MeasurableSpace.{u3} α} {f : α -> β} {g : α -> γ}, (Measurable.{u3, u2} α β m _inst_1 f) -> (Measurable.{u3, u1} α γ m _inst_2 g) -> (Measurable.{u3, u2} α β m _inst_1 (fun (x : α) => HPow.hPow.{u2, u1, u2} β γ β (instHPow.{u2, u1} β γ _inst_3) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align measurable.pow Measurable.powₓ'. -/
@[measurability]
theorem Measurable.pow (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x ^ g x :=
  measurable_pow.comp (hf.prod_mk hg)
#align measurable.pow Measurable.pow

/- warning: ae_measurable.pow -> AEMeasurable.pow is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} β] [_inst_2 : MeasurableSpace.{u2} γ] [_inst_3 : Pow.{u1, u2} β γ] [_inst_4 : MeasurablePow.{u1, u2} β γ _inst_1 _inst_2 _inst_3] {m : MeasurableSpace.{u3} α} {μ : MeasureTheory.Measure.{u3} α m} {f : α -> β} {g : α -> γ}, (AEMeasurable.{u3, u1} α β _inst_1 m f μ) -> (AEMeasurable.{u3, u2} α γ _inst_2 m g μ) -> (AEMeasurable.{u3, u1} α β _inst_1 m (fun (x : α) => HPow.hPow.{u1, u2, u1} β γ β (instHPow.{u1, u2} β γ _inst_3) (f x) (g x)) μ)
but is expected to have type
  forall {β : Type.{u2}} {γ : Type.{u1}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u1} γ] [_inst_3 : Pow.{u2, u1} β γ] [_inst_4 : MeasurablePow.{u2, u1} β γ _inst_1 _inst_2 _inst_3] {m : MeasurableSpace.{u3} α} {μ : MeasureTheory.Measure.{u3} α m} {f : α -> β} {g : α -> γ}, (AEMeasurable.{u3, u2} α β _inst_1 m f μ) -> (AEMeasurable.{u3, u1} α γ _inst_2 m g μ) -> (AEMeasurable.{u3, u2} α β _inst_1 m (fun (x : α) => HPow.hPow.{u2, u1, u2} β γ β (instHPow.{u2, u1} β γ _inst_3) (f x) (g x)) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.pow AEMeasurable.powₓ'. -/
@[measurability]
theorem AEMeasurable.pow (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => f x ^ g x) μ :=
  measurable_pow.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.pow AEMeasurable.pow

/- warning: measurable.pow_const -> Measurable.pow_const is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} β] [_inst_2 : MeasurableSpace.{u2} γ] [_inst_3 : Pow.{u1, u2} β γ] [_inst_4 : MeasurablePow.{u1, u2} β γ _inst_1 _inst_2 _inst_3] {m : MeasurableSpace.{u3} α} {f : α -> β}, (Measurable.{u3, u1} α β m _inst_1 f) -> (forall (c : γ), Measurable.{u3, u1} α β m _inst_1 (fun (x : α) => HPow.hPow.{u1, u2, u1} β γ β (instHPow.{u1, u2} β γ _inst_3) (f x) c))
but is expected to have type
  forall {β : Type.{u2}} {γ : Type.{u1}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u1} γ] [_inst_3 : Pow.{u2, u1} β γ] [_inst_4 : MeasurablePow.{u2, u1} β γ _inst_1 _inst_2 _inst_3] {m : MeasurableSpace.{u3} α} {f : α -> β}, (Measurable.{u3, u2} α β m _inst_1 f) -> (forall (c : γ), Measurable.{u3, u2} α β m _inst_1 (fun (x : α) => HPow.hPow.{u2, u1, u2} β γ β (instHPow.{u2, u1} β γ _inst_3) (f x) c))
Case conversion may be inaccurate. Consider using '#align measurable.pow_const Measurable.pow_constₓ'. -/
@[measurability]
theorem Measurable.pow_const (hf : Measurable f) (c : γ) : Measurable fun x => f x ^ c :=
  hf.pow measurable_const
#align measurable.pow_const Measurable.pow_const

/- warning: ae_measurable.pow_const -> AEMeasurable.pow_const is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {γ : Type.{u2}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} β] [_inst_2 : MeasurableSpace.{u2} γ] [_inst_3 : Pow.{u1, u2} β γ] [_inst_4 : MeasurablePow.{u1, u2} β γ _inst_1 _inst_2 _inst_3] {m : MeasurableSpace.{u3} α} {μ : MeasureTheory.Measure.{u3} α m} {f : α -> β}, (AEMeasurable.{u3, u1} α β _inst_1 m f μ) -> (forall (c : γ), AEMeasurable.{u3, u1} α β _inst_1 m (fun (x : α) => HPow.hPow.{u1, u2, u1} β γ β (instHPow.{u1, u2} β γ _inst_3) (f x) c) μ)
but is expected to have type
  forall {β : Type.{u2}} {γ : Type.{u1}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u2} β] [_inst_2 : MeasurableSpace.{u1} γ] [_inst_3 : Pow.{u2, u1} β γ] [_inst_4 : MeasurablePow.{u2, u1} β γ _inst_1 _inst_2 _inst_3] {m : MeasurableSpace.{u3} α} {μ : MeasureTheory.Measure.{u3} α m} {f : α -> β}, (AEMeasurable.{u3, u2} α β _inst_1 m f μ) -> (forall (c : γ), AEMeasurable.{u3, u2} α β _inst_1 m (fun (x : α) => HPow.hPow.{u2, u1, u2} β γ β (instHPow.{u2, u1} β γ _inst_3) (f x) c) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.pow_const AEMeasurable.pow_constₓ'. -/
@[measurability]
theorem AEMeasurable.pow_const (hf : AEMeasurable f μ) (c : γ) :
    AEMeasurable (fun x => f x ^ c) μ :=
  hf.pow aemeasurable_const
#align ae_measurable.pow_const AEMeasurable.pow_const

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

omit m

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

include m

/- warning: measurable.const_div -> Measurable.const_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : Div.{u1} G] {m : MeasurableSpace.{u2} α} {f : α -> G} [_inst_3 : MeasurableDiv.{u1} G _inst_1 _inst_2], (Measurable.{u2, u1} α G m _inst_1 f) -> (forall (c : G), Measurable.{u2, u1} α G m _inst_1 (fun (x : α) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G _inst_2) c (f x)))
but is expected to have type
  forall {G : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} G] [_inst_2 : Div.{u2} G] {m : MeasurableSpace.{u1} α} {f : α -> G} [_inst_3 : MeasurableDiv.{u2} G _inst_1 _inst_2], (Measurable.{u1, u2} α G m _inst_1 f) -> (forall (c : G), Measurable.{u1, u2} α G m _inst_1 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G _inst_2) c (f x)))
Case conversion may be inaccurate. Consider using '#align measurable.const_div Measurable.const_divₓ'. -/
@[measurability, to_additive]
theorem Measurable.const_div [MeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => c / f x :=
  (MeasurableDiv.measurable_div_const c).comp hf
#align measurable.const_div Measurable.const_div
#align measurable.const_sub Measurable.const_sub

/- warning: ae_measurable.const_div -> AEMeasurable.const_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : Div.{u1} G] {m : MeasurableSpace.{u2} α} {f : α -> G} {μ : MeasureTheory.Measure.{u2} α m} [_inst_3 : MeasurableDiv.{u1} G _inst_1 _inst_2], (AEMeasurable.{u2, u1} α G _inst_1 m f μ) -> (forall (c : G), AEMeasurable.{u2, u1} α G _inst_1 m (fun (x : α) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G _inst_2) c (f x)) μ)
but is expected to have type
  forall {G : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} G] [_inst_2 : Div.{u2} G] {m : MeasurableSpace.{u1} α} {f : α -> G} {μ : MeasureTheory.Measure.{u1} α m} [_inst_3 : MeasurableDiv.{u2} G _inst_1 _inst_2], (AEMeasurable.{u1, u2} α G _inst_1 m f μ) -> (forall (c : G), AEMeasurable.{u1, u2} α G _inst_1 m (fun (x : α) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G _inst_2) c (f x)) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.const_div AEMeasurable.const_divₓ'. -/
@[measurability, to_additive]
theorem AEMeasurable.const_div [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => c / f x) μ :=
  (MeasurableDiv.measurable_div_const c).comp_aemeasurable hf
#align ae_measurable.const_div AEMeasurable.const_div
#align ae_measurable.const_sub AEMeasurable.const_sub

/- warning: measurable.div_const -> Measurable.div_const is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : Div.{u1} G] {m : MeasurableSpace.{u2} α} {f : α -> G} [_inst_3 : MeasurableDiv.{u1} G _inst_1 _inst_2], (Measurable.{u2, u1} α G m _inst_1 f) -> (forall (c : G), Measurable.{u2, u1} α G m _inst_1 (fun (x : α) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G _inst_2) (f x) c))
but is expected to have type
  forall {G : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} G] [_inst_2 : Div.{u2} G] {m : MeasurableSpace.{u1} α} {f : α -> G} [_inst_3 : MeasurableDiv.{u2} G _inst_1 _inst_2], (Measurable.{u1, u2} α G m _inst_1 f) -> (forall (c : G), Measurable.{u1, u2} α G m _inst_1 (fun (x : α) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G _inst_2) (f x) c))
Case conversion may be inaccurate. Consider using '#align measurable.div_const Measurable.div_constₓ'. -/
@[measurability, to_additive]
theorem Measurable.div_const [MeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => f x / c :=
  (MeasurableDiv.measurable_div_const c).comp hf
#align measurable.div_const Measurable.div_const
#align measurable.sub_const Measurable.sub_const

/- warning: ae_measurable.div_const -> AEMeasurable.div_const is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : Div.{u1} G] {m : MeasurableSpace.{u2} α} {f : α -> G} {μ : MeasureTheory.Measure.{u2} α m} [_inst_3 : MeasurableDiv.{u1} G _inst_1 _inst_2], (AEMeasurable.{u2, u1} α G _inst_1 m f μ) -> (forall (c : G), AEMeasurable.{u2, u1} α G _inst_1 m (fun (x : α) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G _inst_2) (f x) c) μ)
but is expected to have type
  forall {G : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} G] [_inst_2 : Div.{u2} G] {m : MeasurableSpace.{u1} α} {f : α -> G} {μ : MeasureTheory.Measure.{u1} α m} [_inst_3 : MeasurableDiv.{u2} G _inst_1 _inst_2], (AEMeasurable.{u1, u2} α G _inst_1 m f μ) -> (forall (c : G), AEMeasurable.{u1, u2} α G _inst_1 m (fun (x : α) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G _inst_2) (f x) c) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.div_const AEMeasurable.div_constₓ'. -/
@[measurability, to_additive]
theorem AEMeasurable.div_const [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => f x / c) μ :=
  (MeasurableDiv.measurable_div_const c).comp_aemeasurable hf
#align ae_measurable.div_const AEMeasurable.div_const
#align ae_measurable.sub_const AEMeasurable.sub_const

/- warning: measurable.div' -> Measurable.div' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : Div.{u1} G] {m : MeasurableSpace.{u2} α} {f : α -> G} {g : α -> G} [_inst_3 : MeasurableDiv₂.{u1} G _inst_1 _inst_2], (Measurable.{u2, u1} α G m _inst_1 f) -> (Measurable.{u2, u1} α G m _inst_1 g) -> (Measurable.{u2, u1} α G m _inst_1 (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> G) (α -> G) (α -> G) (instHDiv.{max u2 u1} (α -> G) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => G) (fun (i : α) => _inst_2))) f g))
but is expected to have type
  forall {G : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} G] [_inst_2 : Div.{u2} G] {m : MeasurableSpace.{u1} α} {f : α -> G} {g : α -> G} [_inst_3 : MeasurableDiv₂.{u2} G _inst_1 _inst_2], (Measurable.{u1, u2} α G m _inst_1 f) -> (Measurable.{u1, u2} α G m _inst_1 g) -> (Measurable.{u1, u2} α G m _inst_1 (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> G) (α -> G) (α -> G) (instHDiv.{max u2 u1} (α -> G) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => _inst_2))) f g))
Case conversion may be inaccurate. Consider using '#align measurable.div' Measurable.div'ₓ'. -/
@[measurability, to_additive]
theorem Measurable.div' [MeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f / g) :=
  measurable_div.comp (hf.prod_mk hg)
#align measurable.div' Measurable.div'
#align measurable.sub' Measurable.sub'

/- warning: measurable.div -> Measurable.div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : Div.{u1} G] {m : MeasurableSpace.{u2} α} {f : α -> G} {g : α -> G} [_inst_3 : MeasurableDiv₂.{u1} G _inst_1 _inst_2], (Measurable.{u2, u1} α G m _inst_1 f) -> (Measurable.{u2, u1} α G m _inst_1 g) -> (Measurable.{u2, u1} α G m _inst_1 (fun (a : α) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G _inst_2) (f a) (g a)))
but is expected to have type
  forall {G : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} G] [_inst_2 : Div.{u2} G] {m : MeasurableSpace.{u1} α} {f : α -> G} {g : α -> G} [_inst_3 : MeasurableDiv₂.{u2} G _inst_1 _inst_2], (Measurable.{u1, u2} α G m _inst_1 f) -> (Measurable.{u1, u2} α G m _inst_1 g) -> (Measurable.{u1, u2} α G m _inst_1 (fun (a : α) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G _inst_2) (f a) (g a)))
Case conversion may be inaccurate. Consider using '#align measurable.div Measurable.divₓ'. -/
@[measurability, to_additive]
theorem Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a / g a :=
  measurable_div.comp (hf.prod_mk hg)
#align measurable.div Measurable.div
#align measurable.sub Measurable.sub

/- warning: ae_measurable.div' -> AEMeasurable.div' is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : Div.{u1} G] {m : MeasurableSpace.{u2} α} {f : α -> G} {g : α -> G} {μ : MeasureTheory.Measure.{u2} α m} [_inst_3 : MeasurableDiv₂.{u1} G _inst_1 _inst_2], (AEMeasurable.{u2, u1} α G _inst_1 m f μ) -> (AEMeasurable.{u2, u1} α G _inst_1 m g μ) -> (AEMeasurable.{u2, u1} α G _inst_1 m (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> G) (α -> G) (α -> G) (instHDiv.{max u2 u1} (α -> G) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => G) (fun (i : α) => _inst_2))) f g) μ)
but is expected to have type
  forall {G : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} G] [_inst_2 : Div.{u2} G] {m : MeasurableSpace.{u1} α} {f : α -> G} {g : α -> G} {μ : MeasureTheory.Measure.{u1} α m} [_inst_3 : MeasurableDiv₂.{u2} G _inst_1 _inst_2], (AEMeasurable.{u1, u2} α G _inst_1 m f μ) -> (AEMeasurable.{u1, u2} α G _inst_1 m g μ) -> (AEMeasurable.{u1, u2} α G _inst_1 m (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> G) (α -> G) (α -> G) (instHDiv.{max u2 u1} (α -> G) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => G) (fun (i : α) => _inst_2))) f g) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.div' AEMeasurable.div'ₓ'. -/
@[measurability, to_additive]
theorem AEMeasurable.div' [MeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f / g) μ :=
  measurable_div.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.div' AEMeasurable.div'
#align ae_measurable.sub' AEMeasurable.sub'

/- warning: ae_measurable.div -> AEMeasurable.div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : Div.{u1} G] {m : MeasurableSpace.{u2} α} {f : α -> G} {g : α -> G} {μ : MeasureTheory.Measure.{u2} α m} [_inst_3 : MeasurableDiv₂.{u1} G _inst_1 _inst_2], (AEMeasurable.{u2, u1} α G _inst_1 m f μ) -> (AEMeasurable.{u2, u1} α G _inst_1 m g μ) -> (AEMeasurable.{u2, u1} α G _inst_1 m (fun (a : α) => HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G _inst_2) (f a) (g a)) μ)
but is expected to have type
  forall {G : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} G] [_inst_2 : Div.{u2} G] {m : MeasurableSpace.{u1} α} {f : α -> G} {g : α -> G} {μ : MeasureTheory.Measure.{u1} α m} [_inst_3 : MeasurableDiv₂.{u2} G _inst_1 _inst_2], (AEMeasurable.{u1, u2} α G _inst_1 m f μ) -> (AEMeasurable.{u1, u2} α G _inst_1 m g μ) -> (AEMeasurable.{u1, u2} α G _inst_1 m (fun (a : α) => HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G _inst_2) (f a) (g a)) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.div AEMeasurable.divₓ'. -/
@[measurability, to_additive]
theorem AEMeasurable.div [MeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a / g a) μ :=
  measurable_div.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.div AEMeasurable.div
#align ae_measurable.sub AEMeasurable.sub

attribute [measurability]
  Measurable.sub Measurable.sub' AEMeasurable.sub AEMeasurable.sub' Measurable.const_sub AEMeasurable.const_sub Measurable.sub_const AEMeasurable.sub_const

omit m

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

/- warning: measurable_set_eq_fun -> measurableSet_eq_fun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {E : Type.{u2}} [_inst_3 : MeasurableSpace.{u2} E] [_inst_4 : AddGroup.{u2} E] [_inst_5 : MeasurableSingletonClass.{u2} E _inst_3] [_inst_6 : MeasurableSub₂.{u2} E _inst_3 (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_4))] {f : α -> E} {g : α -> E}, (Measurable.{u1, u2} α E m _inst_3 f) -> (Measurable.{u1, u2} α E m _inst_3 g) -> (MeasurableSet.{u1} α m (setOf.{u1} α (fun (x : α) => Eq.{succ u2} E (f x) (g x))))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {E : Type.{u1}} [_inst_3 : MeasurableSpace.{u1} E] [_inst_4 : AddGroup.{u1} E] [_inst_5 : MeasurableSingletonClass.{u1} E _inst_3] [_inst_6 : MeasurableSub₂.{u1} E _inst_3 (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_4))] {f : α -> E} {g : α -> E}, (Measurable.{u2, u1} α E m _inst_3 f) -> (Measurable.{u2, u1} α E m _inst_3 g) -> (MeasurableSet.{u2} α m (setOf.{u2} α (fun (x : α) => Eq.{succ u1} E (f x) (g x))))
Case conversion may be inaccurate. Consider using '#align measurable_set_eq_fun measurableSet_eq_funₓ'. -/
@[measurability]
theorem measurableSet_eq_fun {m : MeasurableSpace α} {E} [MeasurableSpace E] [AddGroup E]
    [MeasurableSingletonClass E] [MeasurableSub₂ E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet { x | f x = g x } :=
  by
  suffices h_set_eq : { x : α | f x = g x } = { x | (f - g) x = (0 : E) }
  · rw [h_set_eq]
    exact (hf.sub hg) measurableSet_eq
  ext
  simp_rw [Set.mem_setOf_eq, Pi.sub_apply, sub_eq_zero]
#align measurable_set_eq_fun measurableSet_eq_fun

/- warning: null_measurable_set_eq_fun -> nullMeasurableSet_eq_fun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {E : Type.{u2}} [_inst_3 : MeasurableSpace.{u2} E] [_inst_4 : AddGroup.{u2} E] [_inst_5 : MeasurableSingletonClass.{u2} E _inst_3] [_inst_6 : MeasurableSub₂.{u2} E _inst_3 (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_4))] {f : α -> E} {g : α -> E}, (AEMeasurable.{u1, u2} α E _inst_3 m f μ) -> (AEMeasurable.{u1, u2} α E _inst_3 m g μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m (setOf.{u1} α (fun (x : α) => Eq.{succ u2} E (f x) (g x))) μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {E : Type.{u2}} [_inst_3 : MeasurableSpace.{u2} E] [_inst_4 : AddGroup.{u2} E] [_inst_5 : MeasurableSingletonClass.{u2} E _inst_3] [_inst_6 : MeasurableSub₂.{u2} E _inst_3 (SubNegMonoid.toSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_4))] {f : α -> E} {g : α -> E}, (AEMeasurable.{u1, u2} α E _inst_3 m f μ) -> (AEMeasurable.{u1, u2} α E _inst_3 m g μ) -> (MeasureTheory.NullMeasurableSet.{u1} α m (setOf.{u1} α (fun (x : α) => Eq.{succ u2} E (f x) (g x))) μ)
Case conversion may be inaccurate. Consider using '#align null_measurable_set_eq_fun nullMeasurableSet_eq_funₓ'. -/
theorem nullMeasurableSet_eq_fun {E} [MeasurableSpace E] [AddGroup E] [MeasurableSingletonClass E]
    [MeasurableSub₂ E] {f g : α → E} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    NullMeasurableSet { x | f x = g x } μ :=
  by
  apply (measurableSet_eq_fun hf.measurable_mk hg.measurable_mk).NullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk]with x hfx hgx
  change (hf.mk f x = hg.mk g x) = (f x = g x)
  simp only [hfx, hgx]
#align null_measurable_set_eq_fun nullMeasurableSet_eq_fun

/- warning: measurable_set_eq_fun_of_countable -> measurableSet_eq_fun_of_countable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {E : Type.{u2}} [_inst_3 : MeasurableSpace.{u2} E] [_inst_4 : MeasurableSingletonClass.{u2} E _inst_3] [_inst_5 : Countable.{succ u2} E] {f : α -> E} {g : α -> E}, (Measurable.{u1, u2} α E m _inst_3 f) -> (Measurable.{u1, u2} α E m _inst_3 g) -> (MeasurableSet.{u1} α m (setOf.{u1} α (fun (x : α) => Eq.{succ u2} E (f x) (g x))))
but is expected to have type
  forall {α : Type.{u2}} {m : MeasurableSpace.{u2} α} {E : Type.{u1}} [_inst_3 : MeasurableSpace.{u1} E] [_inst_4 : MeasurableSingletonClass.{u1} E _inst_3] [_inst_5 : Countable.{succ u1} E] {f : α -> E} {g : α -> E}, (Measurable.{u2, u1} α E m _inst_3 f) -> (Measurable.{u2, u1} α E m _inst_3 g) -> (MeasurableSet.{u2} α m (setOf.{u2} α (fun (x : α) => Eq.{succ u1} E (f x) (g x))))
Case conversion may be inaccurate. Consider using '#align measurable_set_eq_fun_of_countable measurableSet_eq_fun_of_countableₓ'. -/
theorem measurableSet_eq_fun_of_countable {m : MeasurableSpace α} {E} [MeasurableSpace E]
    [MeasurableSingletonClass E] [Countable E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet { x | f x = g x } :=
  by
  have : { x | f x = g x } = ⋃ j, { x | f x = j } ∩ { x | g x = j } := by ext1 x;
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_eq_right']
  rw [this]
  refine' MeasurableSet.iUnion fun j => MeasurableSet.inter _ _
  · exact hf (measurable_set_singleton j)
  · exact hg (measurable_set_singleton j)
#align measurable_set_eq_fun_of_countable measurableSet_eq_fun_of_countable

/- warning: ae_eq_trim_of_measurable -> ae_eq_trim_of_measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} {m : MeasurableSpace.{u1} α} {m0 : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m0} [_inst_3 : MeasurableSpace.{u2} E] [_inst_4 : AddGroup.{u2} E] [_inst_5 : MeasurableSingletonClass.{u2} E _inst_3] [_inst_6 : MeasurableSub₂.{u2} E _inst_3 (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_4))] (hm : LE.le.{u1} (MeasurableSpace.{u1} α) (MeasurableSpace.hasLe.{u1} α) m m0) {f : α -> E} {g : α -> E}, (Measurable.{u1, u2} α E m _inst_3 f) -> (Measurable.{u1, u2} α E m _inst_3 g) -> (Filter.EventuallyEq.{u1, u2} α E (MeasureTheory.Measure.ae.{u1} α m0 μ) f g) -> (Filter.EventuallyEq.{u1, u2} α E (MeasureTheory.Measure.ae.{u1} α m (MeasureTheory.Measure.trim.{u1} α m m0 μ hm)) f g)
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} {m : MeasurableSpace.{u2} α} {m0 : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m0} [_inst_3 : MeasurableSpace.{u1} E] [_inst_4 : AddGroup.{u1} E] [_inst_5 : MeasurableSingletonClass.{u1} E _inst_3] [_inst_6 : MeasurableSub₂.{u1} E _inst_3 (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_4))] (hm : LE.le.{u2} (MeasurableSpace.{u2} α) (MeasurableSpace.instLEMeasurableSpace.{u2} α) m m0) {f : α -> E} {g : α -> E}, (Measurable.{u2, u1} α E m _inst_3 f) -> (Measurable.{u2, u1} α E m _inst_3 g) -> (Filter.EventuallyEq.{u2, u1} α E (MeasureTheory.Measure.ae.{u2} α m0 μ) f g) -> (Filter.EventuallyEq.{u2, u1} α E (MeasureTheory.Measure.ae.{u2} α m (MeasureTheory.Measure.trim.{u2} α m m0 μ hm)) f g)
Case conversion may be inaccurate. Consider using '#align ae_eq_trim_of_measurable ae_eq_trim_of_measurableₓ'. -/
theorem ae_eq_trim_of_measurable {α E} {m m0 : MeasurableSpace α} {μ : Measure α}
    [MeasurableSpace E] [AddGroup E] [MeasurableSingletonClass E] [MeasurableSub₂ E] (hm : m ≤ m0)
    {f g : α → E} (hf : measurable[m] f) (hg : measurable[m] g) (hfg : f =ᵐ[μ] g) :
    f =ᶠ[@Measure.ae α m (μ.trim hm)] g :=
  by
  rwa [Filter.EventuallyEq, ae_iff, trim_measurable_set_eq hm _]
  exact @MeasurableSet.compl α _ m (@measurableSet_eq_fun α m E _ _ _ _ _ _ hf hg)
#align ae_eq_trim_of_measurable ae_eq_trim_of_measurable

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

/- warning: has_measurable_div_of_mul_inv -> measurableDiv_of_mul_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : DivInvMonoid.{u1} G] [_inst_3 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_2)))] [_inst_4 : MeasurableInv.{u1} G (DivInvMonoid.toHasInv.{u1} G _inst_2) _inst_1], MeasurableDiv.{u1} G _inst_1 (DivInvMonoid.toHasDiv.{u1} G _inst_2)
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : DivInvMonoid.{u1} G] [_inst_3 : MeasurableMul.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_2)))] [_inst_4 : MeasurableInv.{u1} G (DivInvMonoid.toInv.{u1} G _inst_2) _inst_1], MeasurableDiv.{u1} G _inst_1 (DivInvMonoid.toDiv.{u1} G _inst_2)
Case conversion may be inaccurate. Consider using '#align has_measurable_div_of_mul_inv measurableDiv_of_mul_invₓ'. -/
@[to_additive]
instance (priority := 100) measurableDiv_of_mul_inv (G : Type _) [MeasurableSpace G]
    [DivInvMonoid G] [MeasurableMul G] [MeasurableInv G] : MeasurableDiv G
    where
  measurable_div_const c := by convert measurable_inv.const_mul c; ext1; apply div_eq_mul_inv
  measurable_div_const c := by convert measurable_id.mul_const c⁻¹; ext1; apply div_eq_mul_inv
#align has_measurable_div_of_mul_inv measurableDiv_of_mul_inv
#align has_measurable_sub_of_add_neg measurableSub_of_add_neg

section Inv

variable {G α : Type _} [Inv G] [MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}
  {f : α → G} {μ : Measure α}

include m

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

/- warning: measurable_inv_iff -> measurable_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {G : Type.{u2}} [_inst_4 : Group.{u2} G] [_inst_5 : MeasurableSpace.{u2} G] [_inst_6 : MeasurableInv.{u2} G (DivInvMonoid.toHasInv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_4)) _inst_5] {f : α -> G}, Iff (Measurable.{u1, u2} α G m _inst_5 (fun (x : α) => Inv.inv.{u2} G (DivInvMonoid.toHasInv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_4)) (f x))) (Measurable.{u1, u2} α G m _inst_5 f)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {G : Type.{u2}} [_inst_4 : Group.{u2} G] [_inst_5 : MeasurableSpace.{u2} G] [_inst_6 : MeasurableInv.{u2} G (InvOneClass.toInv.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (Group.toDivisionMonoid.{u2} G _inst_4)))) _inst_5] {f : α -> G}, Iff (Measurable.{u1, u2} α G m _inst_5 (fun (x : α) => Inv.inv.{u2} G (InvOneClass.toInv.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (Group.toDivisionMonoid.{u2} G _inst_4)))) (f x))) (Measurable.{u1, u2} α G m _inst_5 f)
Case conversion may be inaccurate. Consider using '#align measurable_inv_iff measurable_inv_iffₓ'. -/
@[simp, to_additive]
theorem measurable_inv_iff {G : Type _} [Group G] [MeasurableSpace G] [MeasurableInv G]
    {f : α → G} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align measurable_inv_iff measurable_inv_iff
#align measurable_neg_iff measurable_neg_iff

/- warning: ae_measurable_inv_iff -> aemeasurable_inv_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {G : Type.{u2}} [_inst_4 : Group.{u2} G] [_inst_5 : MeasurableSpace.{u2} G] [_inst_6 : MeasurableInv.{u2} G (DivInvMonoid.toHasInv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_4)) _inst_5] {f : α -> G}, Iff (AEMeasurable.{u1, u2} α G _inst_5 m (fun (x : α) => Inv.inv.{u2} G (DivInvMonoid.toHasInv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_4)) (f x)) μ) (AEMeasurable.{u1, u2} α G _inst_5 m f μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {G : Type.{u2}} [_inst_4 : Group.{u2} G] [_inst_5 : MeasurableSpace.{u2} G] [_inst_6 : MeasurableInv.{u2} G (InvOneClass.toInv.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (Group.toDivisionMonoid.{u2} G _inst_4)))) _inst_5] {f : α -> G}, Iff (AEMeasurable.{u1, u2} α G _inst_5 m (fun (x : α) => Inv.inv.{u2} G (InvOneClass.toInv.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (Group.toDivisionMonoid.{u2} G _inst_4)))) (f x)) μ) (AEMeasurable.{u1, u2} α G _inst_5 m f μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable_inv_iff aemeasurable_inv_iffₓ'. -/
@[simp, to_additive]
theorem aemeasurable_inv_iff {G : Type _} [Group G] [MeasurableSpace G] [MeasurableInv G]
    {f : α → G} : AEMeasurable (fun x => (f x)⁻¹) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align ae_measurable_inv_iff aemeasurable_inv_iff
#align ae_measurable_neg_iff aemeasurable_neg_iff

/- warning: measurable_inv_iff₀ -> measurable_inv_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {G₀ : Type.{u2}} [_inst_4 : GroupWithZero.{u2} G₀] [_inst_5 : MeasurableSpace.{u2} G₀] [_inst_6 : MeasurableInv.{u2} G₀ (DivInvMonoid.toHasInv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_4)) _inst_5] {f : α -> G₀}, Iff (Measurable.{u1, u2} α G₀ m _inst_5 (fun (x : α) => Inv.inv.{u2} G₀ (DivInvMonoid.toHasInv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_4)) (f x))) (Measurable.{u1, u2} α G₀ m _inst_5 f)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {G₀ : Type.{u2}} [_inst_4 : GroupWithZero.{u2} G₀] [_inst_5 : MeasurableSpace.{u2} G₀] [_inst_6 : MeasurableInv.{u2} G₀ (GroupWithZero.toInv.{u2} G₀ _inst_4) _inst_5] {f : α -> G₀}, Iff (Measurable.{u1, u2} α G₀ m _inst_5 (fun (x : α) => Inv.inv.{u2} G₀ (GroupWithZero.toInv.{u2} G₀ _inst_4) (f x))) (Measurable.{u1, u2} α G₀ m _inst_5 f)
Case conversion may be inaccurate. Consider using '#align measurable_inv_iff₀ measurable_inv_iff₀ₓ'. -/
@[simp]
theorem measurable_inv_iff₀ {G₀ : Type _} [GroupWithZero G₀] [MeasurableSpace G₀] [MeasurableInv G₀]
    {f : α → G₀} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align measurable_inv_iff₀ measurable_inv_iff₀

/- warning: ae_measurable_inv_iff₀ -> aemeasurable_inv_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {G₀ : Type.{u2}} [_inst_4 : GroupWithZero.{u2} G₀] [_inst_5 : MeasurableSpace.{u2} G₀] [_inst_6 : MeasurableInv.{u2} G₀ (DivInvMonoid.toHasInv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_4)) _inst_5] {f : α -> G₀}, Iff (AEMeasurable.{u1, u2} α G₀ _inst_5 m (fun (x : α) => Inv.inv.{u2} G₀ (DivInvMonoid.toHasInv.{u2} G₀ (GroupWithZero.toDivInvMonoid.{u2} G₀ _inst_4)) (f x)) μ) (AEMeasurable.{u1, u2} α G₀ _inst_5 m f μ)
but is expected to have type
  forall {α : Type.{u1}} {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} {G₀ : Type.{u2}} [_inst_4 : GroupWithZero.{u2} G₀] [_inst_5 : MeasurableSpace.{u2} G₀] [_inst_6 : MeasurableInv.{u2} G₀ (GroupWithZero.toInv.{u2} G₀ _inst_4) _inst_5] {f : α -> G₀}, Iff (AEMeasurable.{u1, u2} α G₀ _inst_5 m (fun (x : α) => Inv.inv.{u2} G₀ (GroupWithZero.toInv.{u2} G₀ _inst_4) (f x)) μ) (AEMeasurable.{u1, u2} α G₀ _inst_5 m f μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable_inv_iff₀ aemeasurable_inv_iff₀ₓ'. -/
@[simp]
theorem aemeasurable_inv_iff₀ {G₀ : Type _} [GroupWithZero G₀] [MeasurableSpace G₀]
    [MeasurableInv G₀] {f : α → G₀} : AEMeasurable (fun x => (f x)⁻¹) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align ae_measurable_inv_iff₀ aemeasurable_inv_iff₀

omit m

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

/- warning: div_inv_monoid.has_measurable_zpow -> DivInvMonoid.measurableZpow is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : DivInvMonoid.{u1} G] [_inst_2 : MeasurableSpace.{u1} G] [_inst_3 : MeasurableMul₂.{u1} G _inst_2 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))] [_inst_4 : MeasurableInv.{u1} G (DivInvMonoid.toHasInv.{u1} G _inst_1) _inst_2], MeasurablePow.{u1, 0} G Int _inst_2 Int.instMeasurableSpace (DivInvMonoid.Pow.{u1} G _inst_1)
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : DivInvMonoid.{u1} G] [_inst_2 : MeasurableSpace.{u1} G] [_inst_3 : MeasurableMul₂.{u1} G _inst_2 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_1)))] [_inst_4 : MeasurableInv.{u1} G (DivInvMonoid.toInv.{u1} G _inst_1) _inst_2], MeasurablePow.{u1, 0} G Int _inst_2 Int.instMeasurableSpace (DivInvMonoid.Pow.{u1} G _inst_1)
Case conversion may be inaccurate. Consider using '#align div_inv_monoid.has_measurable_zpow DivInvMonoid.measurableZpowₓ'. -/
/-- `div_inv_monoid.has_pow` is measurable. -/
instance DivInvMonoid.measurableZpow (G : Type u) [DivInvMonoid G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] : MeasurablePow G ℤ :=
  ⟨measurable_from_prod_countable fun n => by
      cases' n with n n
      · simp_rw [zpow_ofNat]; exact measurable_id.pow_const _
      · simp_rw [zpow_negSucc]; exact (measurable_id.pow_const (n + 1)).inv⟩
#align div_inv_monoid.has_measurable_zpow DivInvMonoid.measurableZpow

/- warning: has_measurable_div₂_of_mul_inv -> measurableDiv₂_of_mul_inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : DivInvMonoid.{u1} G] [_inst_3 : MeasurableMul₂.{u1} G _inst_1 (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_2)))] [_inst_4 : MeasurableInv.{u1} G (DivInvMonoid.toHasInv.{u1} G _inst_2) _inst_1], MeasurableDiv₂.{u1} G _inst_1 (DivInvMonoid.toHasDiv.{u1} G _inst_2)
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : DivInvMonoid.{u1} G] [_inst_3 : MeasurableMul₂.{u1} G _inst_1 (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G _inst_2)))] [_inst_4 : MeasurableInv.{u1} G (DivInvMonoid.toInv.{u1} G _inst_2) _inst_1], MeasurableDiv₂.{u1} G _inst_1 (DivInvMonoid.toDiv.{u1} G _inst_2)
Case conversion may be inaccurate. Consider using '#align has_measurable_div₂_of_mul_inv measurableDiv₂_of_mul_invₓ'. -/
@[to_additive]
instance (priority := 100) measurableDiv₂_of_mul_inv (G : Type _) [MeasurableSpace G]
    [DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G] : MeasurableDiv₂ G :=
  ⟨by simp only [div_eq_mul_inv]; exact measurable_fst.mul measurable_snd.inv⟩
#align has_measurable_div₂_of_mul_inv measurableDiv₂_of_mul_inv
#align has_measurable_div₂_of_add_neg measurableDiv₂_of_add_neg

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

/- warning: submonoid.has_measurable_smul -> Submonoid.measurableSMul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : MeasurableSpace.{u2} α] [_inst_3 : Monoid.{u1} M] [_inst_4 : MulAction.{u1, u2} M α _inst_3] [_inst_5 : MeasurableSMul.{u1, u2} M α (MulAction.toHasSmul.{u1, u2} M α _inst_3 _inst_4) _inst_1 _inst_2] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), MeasurableSMul.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) s) α (Submonoid.hasSmul.{u1, u2} M α (Monoid.toMulOneClass.{u1} M _inst_3) (MulAction.toHasSmul.{u1, u2} M α _inst_3 _inst_4) s) (Subtype.instMeasurableSpace.{u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s) _inst_1) _inst_2
but is expected to have type
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : MeasurableSpace.{u2} α] [_inst_3 : Monoid.{u1} M] [_inst_4 : MulAction.{u1, u2} M α _inst_3] [_inst_5 : MeasurableSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_3 _inst_4) _inst_1 _inst_2] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)), MeasurableSMul.{u1, u2} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s)) α (Submonoid.smul.{u1, u2} M α (Monoid.toMulOneClass.{u1} M _inst_3) (MulAction.toSMul.{u1, u2} M α _inst_3 _inst_4) s) (Subtype.instMeasurableSpace.{u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x s) _inst_1) _inst_2
Case conversion may be inaccurate. Consider using '#align submonoid.has_measurable_smul Submonoid.measurableSMulₓ'. -/
@[to_additive]
instance Submonoid.measurableSMul {M α} [MeasurableSpace M] [MeasurableSpace α] [Monoid M]
    [MulAction M α] [MeasurableSMul M α] (s : Submonoid M) : MeasurableSMul s α :=
  ⟨fun c => by simpa only using measurable_const_smul (c : M), fun x =>
    (measurable_smul_const x : Measurable fun c : M => c • x).comp measurable_subtype_coe⟩
#align submonoid.has_measurable_smul Submonoid.measurableSMul
#align add_submonoid.has_measurable_vadd AddSubmonoid.measurableVAdd

/- warning: subgroup.has_measurable_smul -> Subgroup.measurableSMul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : MeasurableSpace.{u2} α] [_inst_3 : Group.{u1} G] [_inst_4 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))] [_inst_5 : MeasurableSMul.{u1, u2} G α (MulAction.toHasSmul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)) _inst_4) _inst_1 _inst_2] (s : Subgroup.{u1} G _inst_3), MeasurableSMul.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) s) α (MulAction.toHasSmul.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) s) α (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) s) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_3) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) s) (Subgroup.toGroup.{u1} G _inst_3 s))) (Subgroup.mulAction.{u1, u2} G _inst_3 α _inst_4 s)) (Subtype.instMeasurableSpace.{u1} G (fun (x : G) => Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_3) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.setLike.{u1} G _inst_3)) x s) _inst_1) _inst_2
but is expected to have type
  forall {G : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} G] [_inst_2 : MeasurableSpace.{u2} α] [_inst_3 : Group.{u1} G] [_inst_4 : MulAction.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))] [_inst_5 : MeasurableSMul.{u1, u2} G α (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)) _inst_4) _inst_1 _inst_2] (s : Subgroup.{u1} G _inst_3), MeasurableSMul.{u1, u2} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)) x s)) α (Submonoid.smul.{u1, u2} G α (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (MulAction.toSMul.{u1, u2} G α (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3)) _inst_4) (Subgroup.toSubmonoid.{u1} G _inst_3 s)) (Subtype.instMeasurableSpace.{u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_3) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_3) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_3)) x s) _inst_1) _inst_2
Case conversion may be inaccurate. Consider using '#align subgroup.has_measurable_smul Subgroup.measurableSMulₓ'. -/
@[to_additive]
instance Subgroup.measurableSMul {G α} [MeasurableSpace G] [MeasurableSpace α] [Group G]
    [MulAction G α] [MeasurableSMul G α] (s : Subgroup G) : MeasurableSMul s α :=
  s.toSubmonoid.MeasurableSMul
#align subgroup.has_measurable_smul Subgroup.measurableSMul
#align add_subgroup.has_measurable_vadd AddSubgroup.measurableVAdd

section Smul

variable {M β α : Type _} [MeasurableSpace M] [MeasurableSpace β] [SMul M β] {m : MeasurableSpace α}
  {f : α → M} {g : α → β}

include m

/- warning: measurable.smul -> Measurable.smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {β : Type.{u2}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : SMul.{u1, u2} M β] {m : MeasurableSpace.{u3} α} {f : α -> M} {g : α -> β} [_inst_4 : MeasurableSMul₂.{u1, u2} M β _inst_3 _inst_1 _inst_2], (Measurable.{u3, u1} α M m _inst_1 f) -> (Measurable.{u3, u2} α β m _inst_2 g) -> (Measurable.{u3, u2} α β m _inst_2 (fun (x : α) => SMul.smul.{u1, u2} M β _inst_3 (f x) (g x)))
but is expected to have type
  forall {M : Type.{u3}} {β : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} M] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : SMul.{u3, u2} M β] {m : MeasurableSpace.{u1} α} {f : α -> M} {g : α -> β} [_inst_4 : MeasurableSMul₂.{u3, u2} M β _inst_3 _inst_1 _inst_2], (Measurable.{u1, u3} α M m _inst_1 f) -> (Measurable.{u1, u2} α β m _inst_2 g) -> (Measurable.{u1, u2} α β m _inst_2 (fun (x : α) => HSMul.hSMul.{u3, u2, u2} M β β (instHSMul.{u3, u2} M β _inst_3) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align measurable.smul Measurable.smulₓ'. -/
@[measurability, to_additive]
theorem Measurable.smul [MeasurableSMul₂ M β] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x • g x :=
  measurable_smul.comp (hf.prod_mk hg)
#align measurable.smul Measurable.smul
#align measurable.vadd Measurable.vadd

/- warning: ae_measurable.smul -> AEMeasurable.smul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {β : Type.{u2}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : SMul.{u1, u2} M β] {m : MeasurableSpace.{u3} α} {f : α -> M} {g : α -> β} [_inst_4 : MeasurableSMul₂.{u1, u2} M β _inst_3 _inst_1 _inst_2] {μ : MeasureTheory.Measure.{u3} α m}, (AEMeasurable.{u3, u1} α M _inst_1 m f μ) -> (AEMeasurable.{u3, u2} α β _inst_2 m g μ) -> (AEMeasurable.{u3, u2} α β _inst_2 m (fun (x : α) => SMul.smul.{u1, u2} M β _inst_3 (f x) (g x)) μ)
but is expected to have type
  forall {M : Type.{u3}} {β : Type.{u2}} {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} M] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : SMul.{u3, u2} M β] {m : MeasurableSpace.{u1} α} {f : α -> M} {g : α -> β} [_inst_4 : MeasurableSMul₂.{u3, u2} M β _inst_3 _inst_1 _inst_2] {μ : MeasureTheory.Measure.{u1} α m}, (AEMeasurable.{u1, u3} α M _inst_1 m f μ) -> (AEMeasurable.{u1, u2} α β _inst_2 m g μ) -> (AEMeasurable.{u1, u2} α β _inst_2 m (fun (x : α) => HSMul.hSMul.{u3, u2, u2} M β β (instHSMul.{u3, u2} M β _inst_3) (f x) (g x)) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.smul AEMeasurable.smulₓ'. -/
@[measurability, to_additive]
theorem AEMeasurable.smul [MeasurableSMul₂ M β] {μ : Measure α} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun x => f x • g x) μ :=
  MeasurableSMul₂.measurable_smul.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.smul AEMeasurable.smul
#align ae_measurable.vadd AEMeasurable.vadd

omit m

#print MeasurableSMul₂.toMeasurableSMul /-
@[to_additive]
instance (priority := 100) MeasurableSMul₂.toMeasurableSMul [MeasurableSMul₂ M β] :
    MeasurableSMul M β :=
  ⟨fun c => measurable_const.smul measurable_id, fun y => measurable_id.smul measurable_const⟩
#align has_measurable_smul₂.to_has_measurable_smul MeasurableSMul₂.toMeasurableSMul
#align has_measurable_vadd₂.to_has_measurable_vadd MeasurableVAdd₂.toMeasurableVAdd
-/

include m

variable [MeasurableSMul M β] {μ : Measure α}

/- warning: measurable.smul_const -> Measurable.smul_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {β : Type.{u2}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : SMul.{u1, u2} M β] {m : MeasurableSpace.{u3} α} {f : α -> M} [_inst_4 : MeasurableSMul.{u1, u2} M β _inst_3 _inst_1 _inst_2], (Measurable.{u3, u1} α M m _inst_1 f) -> (forall (y : β), Measurable.{u3, u2} α β m _inst_2 (fun (x : α) => SMul.smul.{u1, u2} M β _inst_3 (f x) y))
but is expected to have type
  forall {M : Type.{u2}} {β : Type.{u1}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u2} M] [_inst_2 : MeasurableSpace.{u1} β] [_inst_3 : SMul.{u2, u1} M β] {m : MeasurableSpace.{u3} α} {f : α -> M} [_inst_4 : MeasurableSMul.{u2, u1} M β _inst_3 _inst_1 _inst_2], (Measurable.{u3, u2} α M m _inst_1 f) -> (forall (y : β), Measurable.{u3, u1} α β m _inst_2 (fun (x : α) => HSMul.hSMul.{u2, u1, u1} M β β (instHSMul.{u2, u1} M β _inst_3) (f x) y))
Case conversion may be inaccurate. Consider using '#align measurable.smul_const Measurable.smul_constₓ'. -/
@[measurability, to_additive]
theorem Measurable.smul_const (hf : Measurable f) (y : β) : Measurable fun x => f x • y :=
  (MeasurableSMul.measurable_smul_const y).comp hf
#align measurable.smul_const Measurable.smul_const
#align measurable.vadd_const Measurable.vadd_const

/- warning: ae_measurable.smul_const -> AEMeasurable.smul_const is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {β : Type.{u2}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : SMul.{u1, u2} M β] {m : MeasurableSpace.{u3} α} {f : α -> M} [_inst_4 : MeasurableSMul.{u1, u2} M β _inst_3 _inst_1 _inst_2] {μ : MeasureTheory.Measure.{u3} α m}, (AEMeasurable.{u3, u1} α M _inst_1 m f μ) -> (forall (y : β), AEMeasurable.{u3, u2} α β _inst_2 m (fun (x : α) => SMul.smul.{u1, u2} M β _inst_3 (f x) y) μ)
but is expected to have type
  forall {M : Type.{u2}} {β : Type.{u1}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u2} M] [_inst_2 : MeasurableSpace.{u1} β] [_inst_3 : SMul.{u2, u1} M β] {m : MeasurableSpace.{u3} α} {f : α -> M} [_inst_4 : MeasurableSMul.{u2, u1} M β _inst_3 _inst_1 _inst_2] {μ : MeasureTheory.Measure.{u3} α m}, (AEMeasurable.{u3, u2} α M _inst_1 m f μ) -> (forall (y : β), AEMeasurable.{u3, u1} α β _inst_2 m (fun (x : α) => HSMul.hSMul.{u2, u1, u1} M β β (instHSMul.{u2, u1} M β _inst_3) (f x) y) μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable.smul_const AEMeasurable.smul_constₓ'. -/
@[measurability, to_additive]
theorem AEMeasurable.smul_const (hf : AEMeasurable f μ) (y : β) :
    AEMeasurable (fun x => f x • y) μ :=
  (MeasurableSMul.measurable_smul_const y).comp_aemeasurable hf
#align ae_measurable.smul_const AEMeasurable.smul_const
#align ae_measurable.vadd_const AEMeasurable.vadd_const

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

omit m

#print Pi.measurableSMul /-
@[to_additive]
instance Pi.measurableSMul {ι : Type _} {α : ι → Type _} [∀ i, SMul M (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSMul M (α i)] : MeasurableSMul M (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_smul _, fun g =>
    measurable_pi_iff.mpr fun i => measurable_smul_const _⟩
#align pi.has_measurable_smul Pi.measurableSMul
#align pi.has_measurable_vadd Pi.measurableVAdd
-/

/- warning: add_monoid.has_measurable_smul_nat₂ -> AddMonoid.measurableSMul_nat₂ is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_5 : AddMonoid.{u1} M] [_inst_6 : MeasurableSpace.{u1} M] [_inst_7 : MeasurableAdd₂.{u1} M _inst_6 (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_5))], MeasurableSMul₂.{0, u1} Nat M (AddMonoid.SMul.{u1} M _inst_5) Nat.instMeasurableSpace _inst_6
but is expected to have type
  forall (M : Type.{u1}) [_inst_5 : AddMonoid.{u1} M] [_inst_6 : MeasurableSpace.{u1} M] [_inst_7 : MeasurableAdd₂.{u1} M _inst_6 (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M _inst_5))], MeasurableSMul₂.{0, u1} Nat M (AddMonoid.SMul.{u1} M _inst_5) Nat.instMeasurableSpace _inst_6
Case conversion may be inaccurate. Consider using '#align add_monoid.has_measurable_smul_nat₂ AddMonoid.measurableSMul_nat₂ₓ'. -/
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

/- warning: sub_neg_monoid.has_measurable_smul_int₂ -> SubNegMonoid.measurableSMul_int₂ is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_5 : SubNegMonoid.{u1} M] [_inst_6 : MeasurableSpace.{u1} M] [_inst_7 : MeasurableAdd₂.{u1} M _inst_6 (AddZeroClass.toHasAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M _inst_5)))] [_inst_8 : MeasurableNeg.{u1} M (SubNegMonoid.toHasNeg.{u1} M _inst_5) _inst_6], MeasurableSMul₂.{0, u1} Int M (SubNegMonoid.SMulInt.{u1} M _inst_5) Int.instMeasurableSpace _inst_6
but is expected to have type
  forall (M : Type.{u1}) [_inst_5 : SubNegMonoid.{u1} M] [_inst_6 : MeasurableSpace.{u1} M] [_inst_7 : MeasurableAdd₂.{u1} M _inst_6 (AddZeroClass.toAdd.{u1} M (AddMonoid.toAddZeroClass.{u1} M (SubNegMonoid.toAddMonoid.{u1} M _inst_5)))] [_inst_8 : MeasurableNeg.{u1} M (SubNegMonoid.toNeg.{u1} M _inst_5) _inst_6], MeasurableSMul₂.{0, u1} Int M (SubNegMonoid.SMulInt.{u1} M _inst_5) Int.instMeasurableSpace _inst_6
Case conversion may be inaccurate. Consider using '#align sub_neg_monoid.has_measurable_smul_int₂ SubNegMonoid.measurableSMul_int₂ₓ'. -/
/-- `sub_neg_monoid.has_smul_int` is measurable. -/
instance SubNegMonoid.measurableSMul_int₂ (M : Type _) [SubNegMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] [MeasurableNeg M] : MeasurableSMul₂ ℤ M :=
  ⟨by
    suffices Measurable fun p : M × ℤ => p.2 • p.1 by apply this.comp measurable_swap
    refine' measurable_from_prod_countable fun n => _
    induction' n with n n ih
    · simp only [ofNat_zsmul]; exact measurable_const_smul _
    · simp only [negSucc_zsmul]; exact (measurable_const_smul _).neg⟩
#align sub_neg_monoid.has_measurable_smul_int₂ SubNegMonoid.measurableSMul_int₂

end Smul

section MulAction

variable {M β α : Type _} [MeasurableSpace M] [MeasurableSpace β] [Monoid M] [MulAction M β]
  [MeasurableSMul M β] [MeasurableSpace α] {f : α → β} {μ : Measure α}

variable {G : Type _} [Group G] [MeasurableSpace G] [MulAction G β] [MeasurableSMul G β]

/- warning: measurable_const_smul_iff -> measurable_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} β] [_inst_6 : MeasurableSpace.{u2} α] {f : α -> β} {G : Type.{u3}} [_inst_7 : Group.{u3} G] [_inst_8 : MeasurableSpace.{u3} G] [_inst_9 : MulAction.{u3, u1} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_7))] [_inst_10 : MeasurableSMul.{u3, u1} G β (MulAction.toHasSmul.{u3, u1} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_7)) _inst_9) _inst_8 _inst_2] (c : G), Iff (Measurable.{u2, u1} α β _inst_6 _inst_2 (fun (x : α) => SMul.smul.{u3, u1} G β (MulAction.toHasSmul.{u3, u1} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_7)) _inst_9) c (f x))) (Measurable.{u2, u1} α β _inst_6 _inst_2 f)
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u3}} [_inst_2 : MeasurableSpace.{u2} β] [_inst_6 : MeasurableSpace.{u3} α] {f : α -> β} {G : Type.{u1}} [_inst_7 : Group.{u1} G] [_inst_8 : MeasurableSpace.{u1} G] [_inst_9 : MulAction.{u1, u2} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_7))] [_inst_10 : MeasurableSMul.{u1, u2} G β (MulAction.toSMul.{u1, u2} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_7)) _inst_9) _inst_8 _inst_2] (c : G), Iff (Measurable.{u3, u2} α β _inst_6 _inst_2 (fun (x : α) => HSMul.hSMul.{u1, u2, u2} G β β (instHSMul.{u1, u2} G β (MulAction.toSMul.{u1, u2} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_7)) _inst_9)) c (f x))) (Measurable.{u3, u2} α β _inst_6 _inst_2 f)
Case conversion may be inaccurate. Consider using '#align measurable_const_smul_iff measurable_const_smul_iffₓ'. -/
@[to_additive]
theorem measurable_const_smul_iff (c : G) : (Measurable fun x => c • f x) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align measurable_const_smul_iff measurable_const_smul_iff
#align measurable_const_vadd_iff measurable_const_vadd_iff

/- warning: ae_measurable_const_smul_iff -> aemeasurable_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} β] [_inst_6 : MeasurableSpace.{u2} α] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α _inst_6} {G : Type.{u3}} [_inst_7 : Group.{u3} G] [_inst_8 : MeasurableSpace.{u3} G] [_inst_9 : MulAction.{u3, u1} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_7))] [_inst_10 : MeasurableSMul.{u3, u1} G β (MulAction.toHasSmul.{u3, u1} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_7)) _inst_9) _inst_8 _inst_2] (c : G), Iff (AEMeasurable.{u2, u1} α β _inst_2 _inst_6 (fun (x : α) => SMul.smul.{u3, u1} G β (MulAction.toHasSmul.{u3, u1} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_7)) _inst_9) c (f x)) μ) (AEMeasurable.{u2, u1} α β _inst_2 _inst_6 f μ)
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u3}} [_inst_2 : MeasurableSpace.{u2} β] [_inst_6 : MeasurableSpace.{u3} α] {f : α -> β} {μ : MeasureTheory.Measure.{u3} α _inst_6} {G : Type.{u1}} [_inst_7 : Group.{u1} G] [_inst_8 : MeasurableSpace.{u1} G] [_inst_9 : MulAction.{u1, u2} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_7))] [_inst_10 : MeasurableSMul.{u1, u2} G β (MulAction.toSMul.{u1, u2} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_7)) _inst_9) _inst_8 _inst_2] (c : G), Iff (AEMeasurable.{u3, u2} α β _inst_2 _inst_6 (fun (x : α) => HSMul.hSMul.{u1, u2, u2} G β β (instHSMul.{u1, u2} G β (MulAction.toSMul.{u1, u2} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_7)) _inst_9)) c (f x)) μ) (AEMeasurable.{u3, u2} α β _inst_2 _inst_6 f μ)
Case conversion may be inaccurate. Consider using '#align ae_measurable_const_smul_iff aemeasurable_const_smul_iffₓ'. -/
@[to_additive]
theorem aemeasurable_const_smul_iff (c : G) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align ae_measurable_const_smul_iff aemeasurable_const_smul_iff
#align ae_measurable_const_vadd_iff aemeasurable_const_vadd_iff

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

/- warning: is_unit.measurable_const_smul_iff -> IsUnit.measurable_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {β : Type.{u2}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : Monoid.{u1} M] [_inst_4 : MulAction.{u1, u2} M β _inst_3] [_inst_5 : MeasurableSMul.{u1, u2} M β (MulAction.toHasSmul.{u1, u2} M β _inst_3 _inst_4) _inst_1 _inst_2] [_inst_6 : MeasurableSpace.{u3} α] {f : α -> β} {c : M}, (IsUnit.{u1} M _inst_3 c) -> (Iff (Measurable.{u3, u2} α β _inst_6 _inst_2 (fun (x : α) => SMul.smul.{u1, u2} M β (MulAction.toHasSmul.{u1, u2} M β _inst_3 _inst_4) c (f x))) (Measurable.{u3, u2} α β _inst_6 _inst_2 f))
but is expected to have type
  forall {M : Type.{u3}} {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u3} M] [_inst_2 : MeasurableSpace.{u1} β] [_inst_3 : Monoid.{u3} M] [_inst_4 : MulAction.{u3, u1} M β _inst_3] [_inst_5 : MeasurableSMul.{u3, u1} M β (MulAction.toSMul.{u3, u1} M β _inst_3 _inst_4) _inst_1 _inst_2] [_inst_6 : MeasurableSpace.{u2} α] {f : α -> β} {c : M}, (IsUnit.{u3} M _inst_3 c) -> (Iff (Measurable.{u2, u1} α β _inst_6 _inst_2 (fun (x : α) => HSMul.hSMul.{u3, u1, u1} M β β (instHSMul.{u3, u1} M β (MulAction.toSMul.{u3, u1} M β _inst_3 _inst_4)) c (f x))) (Measurable.{u2, u1} α β _inst_6 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align is_unit.measurable_const_smul_iff IsUnit.measurable_const_smul_iffₓ'. -/
@[to_additive]
theorem IsUnit.measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ measurable_const_smul_iff u
#align is_unit.measurable_const_smul_iff IsUnit.measurable_const_smul_iff
#align is_add_unit.measurable_const_vadd_iff IsAddUnit.measurable_const_vadd_iff

/- warning: is_unit.ae_measurable_const_smul_iff -> IsUnit.aemeasurable_const_smul_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {β : Type.{u2}} {α : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} M] [_inst_2 : MeasurableSpace.{u2} β] [_inst_3 : Monoid.{u1} M] [_inst_4 : MulAction.{u1, u2} M β _inst_3] [_inst_5 : MeasurableSMul.{u1, u2} M β (MulAction.toHasSmul.{u1, u2} M β _inst_3 _inst_4) _inst_1 _inst_2] [_inst_6 : MeasurableSpace.{u3} α] {f : α -> β} {μ : MeasureTheory.Measure.{u3} α _inst_6} {c : M}, (IsUnit.{u1} M _inst_3 c) -> (Iff (AEMeasurable.{u3, u2} α β _inst_2 _inst_6 (fun (x : α) => SMul.smul.{u1, u2} M β (MulAction.toHasSmul.{u1, u2} M β _inst_3 _inst_4) c (f x)) μ) (AEMeasurable.{u3, u2} α β _inst_2 _inst_6 f μ))
but is expected to have type
  forall {M : Type.{u3}} {β : Type.{u1}} {α : Type.{u2}} [_inst_1 : MeasurableSpace.{u3} M] [_inst_2 : MeasurableSpace.{u1} β] [_inst_3 : Monoid.{u3} M] [_inst_4 : MulAction.{u3, u1} M β _inst_3] [_inst_5 : MeasurableSMul.{u3, u1} M β (MulAction.toSMul.{u3, u1} M β _inst_3 _inst_4) _inst_1 _inst_2] [_inst_6 : MeasurableSpace.{u2} α] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α _inst_6} {c : M}, (IsUnit.{u3} M _inst_3 c) -> (Iff (AEMeasurable.{u2, u1} α β _inst_2 _inst_6 (fun (x : α) => HSMul.hSMul.{u3, u1, u1} M β β (instHSMul.{u3, u1} M β (MulAction.toSMul.{u3, u1} M β _inst_3 _inst_4)) c (f x)) μ) (AEMeasurable.{u2, u1} α β _inst_2 _inst_6 f μ))
Case conversion may be inaccurate. Consider using '#align is_unit.ae_measurable_const_smul_iff IsUnit.aemeasurable_const_smul_iffₓ'. -/
@[to_additive]
theorem IsUnit.aemeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aemeasurable_const_smul_iff u
#align is_unit.ae_measurable_const_smul_iff IsUnit.aemeasurable_const_smul_iff
#align is_add_unit.ae_measurable_const_vadd_iff IsAddUnit.aemeasurable_const_vadd_iff

variable {G₀ : Type _} [GroupWithZero G₀] [MeasurableSpace G₀] [MulAction G₀ β]
  [MeasurableSMul G₀ β]

/- warning: measurable_const_smul_iff₀ -> measurable_const_smul_iff₀ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} β] [_inst_6 : MeasurableSpace.{u2} α] {f : α -> β} {G₀ : Type.{u3}} [_inst_11 : GroupWithZero.{u3} G₀] [_inst_12 : MeasurableSpace.{u3} G₀] [_inst_13 : MulAction.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11))] [_inst_14 : MeasurableSMul.{u3, u1} G₀ β (MulAction.toHasSmul.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11)) _inst_13) _inst_12 _inst_2] {c : G₀}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11)))))))) -> (Iff (Measurable.{u2, u1} α β _inst_6 _inst_2 (fun (x : α) => SMul.smul.{u3, u1} G₀ β (MulAction.toHasSmul.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11)) _inst_13) c (f x))) (Measurable.{u2, u1} α β _inst_6 _inst_2 f))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} β] [_inst_6 : MeasurableSpace.{u2} α] {f : α -> β} {G₀ : Type.{u3}} [_inst_11 : GroupWithZero.{u3} G₀] [_inst_12 : MeasurableSpace.{u3} G₀] [_inst_13 : MulAction.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11))] [_inst_14 : MeasurableSMul.{u3, u1} G₀ β (MulAction.toSMul.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11)) _inst_13) _inst_12 _inst_2] {c : G₀}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (Zero.toOfNat0.{u3} G₀ (MonoidWithZero.toZero.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11))))) -> (Iff (Measurable.{u2, u1} α β _inst_6 _inst_2 (fun (x : α) => HSMul.hSMul.{u3, u1, u1} G₀ β β (instHSMul.{u3, u1} G₀ β (MulAction.toSMul.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11)) _inst_13)) c (f x))) (Measurable.{u2, u1} α β _inst_6 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align measurable_const_smul_iff₀ measurable_const_smul_iff₀ₓ'. -/
theorem measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  (IsUnit.mk0 c hc).measurable_const_smul_iff
#align measurable_const_smul_iff₀ measurable_const_smul_iff₀

/- warning: ae_measurable_const_smul_iff₀ -> aemeasurable_const_smul_iff₀ is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} β] [_inst_6 : MeasurableSpace.{u2} α] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α _inst_6} {G₀ : Type.{u3}} [_inst_11 : GroupWithZero.{u3} G₀] [_inst_12 : MeasurableSpace.{u3} G₀] [_inst_13 : MulAction.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11))] [_inst_14 : MeasurableSMul.{u3, u1} G₀ β (MulAction.toHasSmul.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11)) _inst_13) _inst_12 _inst_2] {c : G₀}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (OfNat.mk.{u3} G₀ 0 (Zero.zero.{u3} G₀ (MulZeroClass.toHasZero.{u3} G₀ (MulZeroOneClass.toMulZeroClass.{u3} G₀ (MonoidWithZero.toMulZeroOneClass.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11)))))))) -> (Iff (AEMeasurable.{u2, u1} α β _inst_2 _inst_6 (fun (x : α) => SMul.smul.{u3, u1} G₀ β (MulAction.toHasSmul.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11)) _inst_13) c (f x)) μ) (AEMeasurable.{u2, u1} α β _inst_2 _inst_6 f μ))
but is expected to have type
  forall {β : Type.{u1}} {α : Type.{u2}} [_inst_2 : MeasurableSpace.{u1} β] [_inst_6 : MeasurableSpace.{u2} α] {f : α -> β} {μ : MeasureTheory.Measure.{u2} α _inst_6} {G₀ : Type.{u3}} [_inst_11 : GroupWithZero.{u3} G₀] [_inst_12 : MeasurableSpace.{u3} G₀] [_inst_13 : MulAction.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11))] [_inst_14 : MeasurableSMul.{u3, u1} G₀ β (MulAction.toSMul.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11)) _inst_13) _inst_12 _inst_2] {c : G₀}, (Ne.{succ u3} G₀ c (OfNat.ofNat.{u3} G₀ 0 (Zero.toOfNat0.{u3} G₀ (MonoidWithZero.toZero.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11))))) -> (Iff (AEMeasurable.{u2, u1} α β _inst_2 _inst_6 (fun (x : α) => HSMul.hSMul.{u3, u1, u1} G₀ β β (instHSMul.{u3, u1} G₀ β (MulAction.toSMul.{u3, u1} G₀ β (MonoidWithZero.toMonoid.{u3} G₀ (GroupWithZero.toMonoidWithZero.{u3} G₀ _inst_11)) _inst_13)) c (f x)) μ) (AEMeasurable.{u2, u1} α β _inst_2 _inst_6 f μ))
Case conversion may be inaccurate. Consider using '#align ae_measurable_const_smul_iff₀ aemeasurable_const_smul_iff₀ₓ'. -/
theorem aemeasurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  (IsUnit.mk0 c hc).aemeasurable_const_smul_iff
#align ae_measurable_const_smul_iff₀ aemeasurable_const_smul_iff₀

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

include m

/- warning: list.measurable_prod' -> List.measurable_prod' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))] {m : MeasurableSpace.{u2} α} (l : List.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u2 u1, max u2 u1} (α -> M) (List.{max u2 u1} (α -> M)) (List.hasMem.{max u2 u1} (α -> M)) f l) -> (Measurable.{u2, u1} α M m _inst_2 f)) -> (Measurable.{u2, u1} α M m _inst_2 (List.prod.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Pi.instOne.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) l))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : MeasurableSpace.{u2} M] [_inst_3 : MeasurableMul₂.{u2} M _inst_2 (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))] {m : MeasurableSpace.{u1} α} (l : List.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (List.{max u2 u1} (α -> M)) (List.instMembershipList.{max u2 u1} (α -> M)) f l) -> (Measurable.{u1, u2} α M m _inst_2 f)) -> (Measurable.{u1, u2} α M m _inst_2 (List.prod.{max u2 u1} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => Monoid.toOne.{u2} M _inst_1)) l))
Case conversion may be inaccurate. Consider using '#align list.measurable_prod' List.measurable_prod'ₓ'. -/
@[measurability, to_additive]
theorem List.measurable_prod' (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) : Measurable l.Prod :=
  by
  induction' l with f l ihl; · exact measurable_one
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.measurable_prod' List.measurable_prod'
#align list.measurable_sum' List.measurable_sum'

/- warning: list.ae_measurable_prod' -> List.aemeasurable_prod' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))] {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} (l : List.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u2 u1, max u2 u1} (α -> M) (List.{max u2 u1} (α -> M)) (List.hasMem.{max u2 u1} (α -> M)) f l) -> (AEMeasurable.{u2, u1} α M _inst_2 m f μ)) -> (AEMeasurable.{u2, u1} α M _inst_2 m (List.prod.{max u2 u1} (α -> M) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Pi.instOne.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) l) μ)
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : MeasurableSpace.{u2} M] [_inst_3 : MeasurableMul₂.{u2} M _inst_2 (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))] {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (l : List.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (List.{max u2 u1} (α -> M)) (List.instMembershipList.{max u2 u1} (α -> M)) f l) -> (AEMeasurable.{u1, u2} α M _inst_2 m f μ)) -> (AEMeasurable.{u1, u2} α M _inst_2 m (List.prod.{max u2 u1} (α -> M) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => Monoid.toOne.{u2} M _inst_1)) l) μ)
Case conversion may be inaccurate. Consider using '#align list.ae_measurable_prod' List.aemeasurable_prod'ₓ'. -/
@[measurability, to_additive]
theorem List.aemeasurable_prod' (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.Prod μ := by
  induction' l with f l ihl; · exact aemeasurable_one
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.ae_measurable_prod' List.aemeasurable_prod'
#align list.ae_measurable_sum' List.aemeasurable_sum'

/- warning: list.measurable_prod -> List.measurable_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))] {m : MeasurableSpace.{u2} α} (l : List.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u2 u1, max u2 u1} (α -> M) (List.{max u2 u1} (α -> M)) (List.hasMem.{max u2 u1} (α -> M)) f l) -> (Measurable.{u2, u1} α M m _inst_2 f)) -> (Measurable.{u2, u1} α M m _inst_2 (fun (x : α) => List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.map.{max u2 u1, u1} (α -> M) M (fun (f : α -> M) => f x) l)))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : MeasurableSpace.{u2} M] [_inst_3 : MeasurableMul₂.{u2} M _inst_2 (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))] {m : MeasurableSpace.{u1} α} (l : List.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (List.{max u2 u1} (α -> M)) (List.instMembershipList.{max u2 u1} (α -> M)) f l) -> (Measurable.{u1, u2} α M m _inst_2 f)) -> (Measurable.{u1, u2} α M m _inst_2 (fun (x : α) => List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{max u2 u1, u2} (α -> M) M (fun (f : α -> M) => f x) l)))
Case conversion may be inaccurate. Consider using '#align list.measurable_prod List.measurable_prodₓ'. -/
@[measurability, to_additive]
theorem List.measurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable fun x => (l.map fun f : α → M => f x).Prod := by
  simpa only [← Pi.list_prod_apply] using l.measurable_prod' hl
#align list.measurable_prod List.measurable_prod
#align list.measurable_sum List.measurable_sum

/- warning: list.ae_measurable_prod -> List.aemeasurable_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))] {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} (l : List.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u2 u1, max u2 u1} (α -> M) (List.{max u2 u1} (α -> M)) (List.hasMem.{max u2 u1} (α -> M)) f l) -> (AEMeasurable.{u2, u1} α M _inst_2 m f μ)) -> (AEMeasurable.{u2, u1} α M _inst_2 m (fun (x : α) => List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.map.{max u2 u1, u1} (α -> M) M (fun (f : α -> M) => f x) l)) μ)
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : MeasurableSpace.{u2} M] [_inst_3 : MeasurableMul₂.{u2} M _inst_2 (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))] {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (l : List.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (List.{max u2 u1} (α -> M)) (List.instMembershipList.{max u2 u1} (α -> M)) f l) -> (AEMeasurable.{u1, u2} α M _inst_2 m f μ)) -> (AEMeasurable.{u1, u2} α M _inst_2 m (fun (x : α) => List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{max u2 u1, u2} (α -> M) M (fun (f : α -> M) => f x) l)) μ)
Case conversion may be inaccurate. Consider using '#align list.ae_measurable_prod List.aemeasurable_prodₓ'. -/
@[measurability, to_additive]
theorem List.aemeasurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable (fun x => (l.map fun f : α → M => f x).Prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.ae_measurable_prod' hl
#align list.ae_measurable_prod List.aemeasurable_prod
#align list.ae_measurable_sum List.aemeasurable_sum

omit m

end Monoid

section CommMonoid

variable {M ι α : Type _} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M]
  {m : MeasurableSpace α} {μ : Measure α} {f : ι → α → M}

include m

/- warning: multiset.measurable_prod' -> Multiset.measurable_prod' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))] {m : MeasurableSpace.{u2} α} (l : Multiset.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u2 u1, max u2 u1} (α -> M) (Multiset.{max u2 u1} (α -> M)) (Multiset.hasMem.{max u2 u1} (α -> M)) f l) -> (Measurable.{u2, u1} α M m _inst_2 f)) -> (Measurable.{u2, u1} α M m _inst_2 (Multiset.prod.{max u2 u1} (α -> M) (Pi.commMonoid.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)) l))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : MeasurableSpace.{u2} M] [_inst_3 : MeasurableMul₂.{u2} M _inst_2 (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))] {m : MeasurableSpace.{u1} α} (l : Multiset.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (Multiset.{max u2 u1} (α -> M)) (Multiset.instMembershipMultiset.{max u2 u1} (α -> M)) f l) -> (Measurable.{u1, u2} α M m _inst_2 f)) -> (Measurable.{u1, u2} α M m _inst_2 (Multiset.prod.{max u2 u1} (α -> M) (Pi.commMonoid.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)) l))
Case conversion may be inaccurate. Consider using '#align multiset.measurable_prod' Multiset.measurable_prod'ₓ'. -/
@[measurability, to_additive]
theorem Multiset.measurable_prod' (l : Multiset (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable l.Prod := by rcases l with ⟨l⟩; simpa using l.measurable_prod' (by simpa using hl)
#align multiset.measurable_prod' Multiset.measurable_prod'
#align multiset.measurable_sum' Multiset.measurable_sum'

/- warning: multiset.ae_measurable_prod' -> Multiset.aemeasurable_prod' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))] {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} (l : Multiset.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u2 u1, max u2 u1} (α -> M) (Multiset.{max u2 u1} (α -> M)) (Multiset.hasMem.{max u2 u1} (α -> M)) f l) -> (AEMeasurable.{u2, u1} α M _inst_2 m f μ)) -> (AEMeasurable.{u2, u1} α M _inst_2 m (Multiset.prod.{max u2 u1} (α -> M) (Pi.commMonoid.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)) l) μ)
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : MeasurableSpace.{u2} M] [_inst_3 : MeasurableMul₂.{u2} M _inst_2 (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))] {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (l : Multiset.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (Multiset.{max u2 u1} (α -> M)) (Multiset.instMembershipMultiset.{max u2 u1} (α -> M)) f l) -> (AEMeasurable.{u1, u2} α M _inst_2 m f μ)) -> (AEMeasurable.{u1, u2} α M _inst_2 m (Multiset.prod.{max u2 u1} (α -> M) (Pi.commMonoid.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)) l) μ)
Case conversion may be inaccurate. Consider using '#align multiset.ae_measurable_prod' Multiset.aemeasurable_prod'ₓ'. -/
@[measurability, to_additive]
theorem Multiset.aemeasurable_prod' (l : Multiset (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.Prod μ := by rcases l with ⟨l⟩;
  simpa using l.ae_measurable_prod' (by simpa using hl)
#align multiset.ae_measurable_prod' Multiset.aemeasurable_prod'
#align multiset.ae_measurable_sum' Multiset.aemeasurable_sum'

/- warning: multiset.measurable_prod -> Multiset.measurable_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))] {m : MeasurableSpace.{u2} α} (s : Multiset.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u2 u1, max u2 u1} (α -> M) (Multiset.{max u2 u1} (α -> M)) (Multiset.hasMem.{max u2 u1} (α -> M)) f s) -> (Measurable.{u2, u1} α M m _inst_2 f)) -> (Measurable.{u2, u1} α M m _inst_2 (fun (x : α) => Multiset.prod.{u1} M _inst_1 (Multiset.map.{max u2 u1, u1} (α -> M) M (fun (f : α -> M) => f x) s)))
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : MeasurableSpace.{u2} M] [_inst_3 : MeasurableMul₂.{u2} M _inst_2 (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))] {m : MeasurableSpace.{u1} α} (s : Multiset.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (Multiset.{max u2 u1} (α -> M)) (Multiset.instMembershipMultiset.{max u2 u1} (α -> M)) f s) -> (Measurable.{u1, u2} α M m _inst_2 f)) -> (Measurable.{u1, u2} α M m _inst_2 (fun (x : α) => Multiset.prod.{u2} M _inst_1 (Multiset.map.{max u2 u1, u2} (α -> M) M (fun (f : α -> M) => f x) s)))
Case conversion may be inaccurate. Consider using '#align multiset.measurable_prod Multiset.measurable_prodₓ'. -/
@[measurability, to_additive]
theorem Multiset.measurable_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, Measurable f) :
    Measurable fun x => (s.map fun f : α → M => f x).Prod := by
  simpa only [← Pi.multiset_prod_apply] using s.measurable_prod' hs
#align multiset.measurable_prod Multiset.measurable_prod
#align multiset.measurable_sum Multiset.measurable_sum

/- warning: multiset.ae_measurable_prod -> Multiset.aemeasurable_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))] {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} (s : Multiset.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.Mem.{max u2 u1, max u2 u1} (α -> M) (Multiset.{max u2 u1} (α -> M)) (Multiset.hasMem.{max u2 u1} (α -> M)) f s) -> (AEMeasurable.{u2, u1} α M _inst_2 m f μ)) -> (AEMeasurable.{u2, u1} α M _inst_2 m (fun (x : α) => Multiset.prod.{u1} M _inst_1 (Multiset.map.{max u2 u1, u1} (α -> M) M (fun (f : α -> M) => f x) s)) μ)
but is expected to have type
  forall {M : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u2} M] [_inst_2 : MeasurableSpace.{u2} M] [_inst_3 : MeasurableMul₂.{u2} M _inst_2 (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_1)))] {m : MeasurableSpace.{u1} α} {μ : MeasureTheory.Measure.{u1} α m} (s : Multiset.{max u2 u1} (α -> M)), (forall (f : α -> M), (Membership.mem.{max u2 u1, max u2 u1} (α -> M) (Multiset.{max u2 u1} (α -> M)) (Multiset.instMembershipMultiset.{max u2 u1} (α -> M)) f s) -> (AEMeasurable.{u1, u2} α M _inst_2 m f μ)) -> (AEMeasurable.{u1, u2} α M _inst_2 m (fun (x : α) => Multiset.prod.{u2} M _inst_1 (Multiset.map.{max u2 u1, u2} (α -> M) M (fun (f : α -> M) => f x) s)) μ)
Case conversion may be inaccurate. Consider using '#align multiset.ae_measurable_prod Multiset.aemeasurable_prodₓ'. -/
@[measurability, to_additive]
theorem Multiset.aemeasurable_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, AEMeasurable f μ) :
    AEMeasurable (fun x => (s.map fun f : α → M => f x).Prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.ae_measurable_prod' hs
#align multiset.ae_measurable_prod Multiset.aemeasurable_prod
#align multiset.ae_measurable_sum Multiset.aemeasurable_sum

/- warning: finset.measurable_prod' -> Finset.measurable_prod' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {ι : Type.{u2}} {α : Type.{u3}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))] {m : MeasurableSpace.{u3} α} {f : ι -> α -> M} (s : Finset.{u2} ι), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Measurable.{u3, u1} α M m _inst_2 (f i))) -> (Measurable.{u3, u1} α M m _inst_2 (Finset.prod.{max u3 u1, u2} (α -> M) ι (Pi.commMonoid.{u3, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)) s (fun (i : ι) => f i)))
but is expected to have type
  forall {M : Type.{u1}} {ι : Type.{u3}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))] {m : MeasurableSpace.{u2} α} {f : ι -> α -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) -> (Measurable.{u2, u1} α M m _inst_2 (f i))) -> (Measurable.{u2, u1} α M m _inst_2 (Finset.prod.{max u1 u2, u3} (α -> M) ι (Pi.commMonoid.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)) s (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align finset.measurable_prod' Finset.measurable_prod'ₓ'. -/
@[measurability, to_additive]
theorem Finset.measurable_prod' (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (∏ i in s, f i) :=
  Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf
#align finset.measurable_prod' Finset.measurable_prod'
#align finset.measurable_sum' Finset.measurable_sum'

/- warning: finset.measurable_prod -> Finset.measurable_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {ι : Type.{u2}} {α : Type.{u3}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))] {m : MeasurableSpace.{u3} α} {f : ι -> α -> M} (s : Finset.{u2} ι), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Measurable.{u3, u1} α M m _inst_2 (f i))) -> (Measurable.{u3, u1} α M m _inst_2 (fun (a : α) => Finset.prod.{u1, u2} M ι _inst_1 s (fun (i : ι) => f i a)))
but is expected to have type
  forall {M : Type.{u1}} {ι : Type.{u3}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))] {m : MeasurableSpace.{u2} α} {f : ι -> α -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) -> (Measurable.{u2, u1} α M m _inst_2 (f i))) -> (Measurable.{u2, u1} α M m _inst_2 (fun (a : α) => Finset.prod.{u1, u3} M ι _inst_1 s (fun (i : ι) => f i a)))
Case conversion may be inaccurate. Consider using '#align finset.measurable_prod Finset.measurable_prodₓ'. -/
@[measurability, to_additive]
theorem Finset.measurable_prod (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun a => ∏ i in s, f i a := by
  simpa only [← Finset.prod_apply] using s.measurable_prod' hf
#align finset.measurable_prod Finset.measurable_prod
#align finset.measurable_sum Finset.measurable_sum

/- warning: finset.ae_measurable_prod' -> Finset.aemeasurable_prod' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {ι : Type.{u2}} {α : Type.{u3}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))] {m : MeasurableSpace.{u3} α} {μ : MeasureTheory.Measure.{u3} α m} {f : ι -> α -> M} (s : Finset.{u2} ι), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (AEMeasurable.{u3, u1} α M _inst_2 m (f i) μ)) -> (AEMeasurable.{u3, u1} α M _inst_2 m (Finset.prod.{max u3 u1, u2} (α -> M) ι (Pi.commMonoid.{u3, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)) s (fun (i : ι) => f i)) μ)
but is expected to have type
  forall {M : Type.{u1}} {ι : Type.{u3}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))] {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {f : ι -> α -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) -> (AEMeasurable.{u2, u1} α M _inst_2 m (f i) μ)) -> (AEMeasurable.{u2, u1} α M _inst_2 m (Finset.prod.{max u1 u2, u3} (α -> M) ι (Pi.commMonoid.{u2, u1} α (fun (ᾰ : α) => M) (fun (i : α) => _inst_1)) s (fun (i : ι) => f i)) μ)
Case conversion may be inaccurate. Consider using '#align finset.ae_measurable_prod' Finset.aemeasurable_prod'ₓ'. -/
@[measurability, to_additive]
theorem Finset.aemeasurable_prod' (s : Finset ι) (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (∏ i in s, f i) μ :=
  Multiset.aemeasurable_prod' _ fun g hg =>
    let ⟨i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi
#align finset.ae_measurable_prod' Finset.aemeasurable_prod'
#align finset.ae_measurable_sum' Finset.aemeasurable_sum'

/- warning: finset.ae_measurable_prod -> Finset.aemeasurable_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {ι : Type.{u2}} {α : Type.{u3}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))] {m : MeasurableSpace.{u3} α} {μ : MeasureTheory.Measure.{u3} α m} {f : ι -> α -> M} (s : Finset.{u2} ι), (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (AEMeasurable.{u3, u1} α M _inst_2 m (f i) μ)) -> (AEMeasurable.{u3, u1} α M _inst_2 m (fun (a : α) => Finset.prod.{u1, u2} M ι _inst_1 s (fun (i : ι) => f i a)) μ)
but is expected to have type
  forall {M : Type.{u1}} {ι : Type.{u3}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u1} M] [_inst_2 : MeasurableSpace.{u1} M] [_inst_3 : MeasurableMul₂.{u1} M _inst_2 (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))] {m : MeasurableSpace.{u2} α} {μ : MeasureTheory.Measure.{u2} α m} {f : ι -> α -> M} (s : Finset.{u3} ι), (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i s) -> (AEMeasurable.{u2, u1} α M _inst_2 m (f i) μ)) -> (AEMeasurable.{u2, u1} α M _inst_2 m (fun (a : α) => Finset.prod.{u1, u3} M ι _inst_1 s (fun (i : ι) => f i a)) μ)
Case conversion may be inaccurate. Consider using '#align finset.ae_measurable_prod Finset.aemeasurable_prodₓ'. -/
@[measurability, to_additive]
theorem Finset.aemeasurable_prod (s : Finset ι) (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (fun a => ∏ i in s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.ae_measurable_prod' hf
#align finset.ae_measurable_prod Finset.aemeasurable_prod
#align finset.ae_measurable_sum Finset.aemeasurable_sum

omit m

end CommMonoid

