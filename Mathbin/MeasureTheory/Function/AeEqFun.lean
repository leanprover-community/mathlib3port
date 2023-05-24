/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou

! This file was ported from Lean 3 source module measure_theory.function.ae_eq_fun
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Integral.Lebesgue
import Mathbin.Order.Filter.Germ
import Mathbin.Topology.ContinuousFunction.Algebra
import Mathbin.MeasureTheory.Function.StronglyMeasurable.Basic

/-!

# Almost everywhere equal functions

We build a space of equivalence classes of functions, where two functions are treated as identical
if they are almost everywhere equal. We form the set of equivalence classes under the relation of
being almost everywhere equal, which is sometimes known as the `L⁰` space.
To use this space as a basis for the `L^p` spaces and for the Bochner integral, we consider
equivalence classes of strongly measurable functions (or, equivalently, of almost everywhere
strongly measurable functions.)

See `l1_space.lean` for `L¹` space.

## Notation

* `α →ₘ[μ] β` is the type of `L⁰` space, where `α` is a measurable space, `β` is a topological
  space, and `μ` is a measure on `α`. `f : α →ₘ β` is a "function" in `L⁰`.
  In comments, `[f]` is also used to denote an `L⁰` function.

  `ₘ` can be typed as `\_m`. Sometimes it is shown as a box if font is missing.

## Main statements

* The linear structure of `L⁰` :
    Addition and scalar multiplication are defined on `L⁰` in the natural way, i.e.,
    `[f] + [g] := [f + g]`, `c • [f] := [c • f]`. So defined, `α →ₘ β` inherits the linear structure
    of `β`. For example, if `β` is a module, then `α →ₘ β` is a module over the same ring.

    See `mk_add_mk`,  `neg_mk`,     `mk_sub_mk`,  `smul_mk`,
        `add_to_fun`, `neg_to_fun`, `sub_to_fun`, `smul_to_fun`

* The order structure of `L⁰` :
    `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
    And `α →ₘ β` inherits the preorder and partial order of `β`.

    TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
    linear order, since otherwise `f ⊔ g` may not be a measurable function.

## Implementation notes

* `f.to_fun`     : To find a representative of `f : α →ₘ β`, use the coercion `(f : α → β)`, which
                 is implemented as `f.to_fun`.
                 For each operation `op` in `L⁰`, there is a lemma called `coe_fn_op`,
                 characterizing, say, `(f op g : α → β)`.
* `ae_eq_fun.mk` : To constructs an `L⁰` function `α →ₘ β` from an almost everywhere strongly
                 measurable function `f : α → β`, use `ae_eq_fun.mk`
* `comp`         : Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₘ γ` when `g` is
                 continuous. Use `comp_measurable` if `g` is only measurable (this requires the
                 target space to be second countable).
* `comp₂`        : Use `comp₂ g f₁ f₂ to get `[λ a, g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`


## Tags

function space, almost everywhere equal, `L⁰`, ae_eq_fun

-/


noncomputable section

open Classical ENNReal Topology

open Set Filter TopologicalSpace ENNReal Emetric MeasureTheory Function

variable {α β γ δ : Type _} [MeasurableSpace α] {μ ν : Measure α}

namespace MeasureTheory

section MeasurableSpace

variable [TopologicalSpace β]

variable (β)

#print MeasureTheory.Measure.aeEqSetoid /-
/-- The equivalence relation of being almost everywhere equal for almost everywhere strongly
measurable functions. -/
def Measure.aeEqSetoid (μ : Measure α) : Setoid { f : α → β // AEStronglyMeasurable f μ } :=
  ⟨fun f g => (f : α → β) =ᵐ[μ] g, fun f => ae_eq_refl f, fun f g => ae_eq_symm, fun f g h =>
    ae_eq_trans⟩
#align measure_theory.measure.ae_eq_setoid MeasureTheory.Measure.aeEqSetoid
-/

variable (α)

#print MeasureTheory.AEEqFun /-
/-- The space of equivalence classes of almost everywhere strongly measurable functions, where two
    strongly measurable functions are equivalent if they agree almost everywhere, i.e.,
    they differ on a set of measure `0`.  -/
def AEEqFun (μ : Measure α) : Type _ :=
  Quotient (μ.aeEqSetoid β)
#align measure_theory.ae_eq_fun MeasureTheory.AEEqFun
-/

variable {α β}

-- mathport name: «expr →ₘ[ ] »
notation:25 α " →ₘ[" μ "] " β => AEEqFun α β μ

end MeasurableSpace

namespace AeEqFun

variable [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

#print MeasureTheory.AEEqFun.mk /-
/-- Construct the equivalence class `[f]` of an almost everywhere measurable function `f`, based
    on the equivalence relation of being almost everywhere equal. -/
def mk {β : Type _} [TopologicalSpace β] (f : α → β) (hf : AEStronglyMeasurable f μ) : α →ₘ[μ] β :=
  Quotient.mk'' ⟨f, hf⟩
#align measure_theory.ae_eq_fun.mk MeasureTheory.AEEqFun.mk
-/

/-- A measurable representative of an `ae_eq_fun` [f] -/
instance : CoeFun (α →ₘ[μ] β) fun _ => α → β :=
  ⟨fun f =>
    AEStronglyMeasurable.mk _ (Quotient.out' f : { f : α → β // AEStronglyMeasurable f μ }).2⟩

/- warning: measure_theory.ae_eq_fun.strongly_measurable -> MeasureTheory.AEEqFun.stronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), MeasureTheory.StronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ), MeasureTheory.StronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 f)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.strongly_measurable MeasureTheory.AEEqFun.stronglyMeasurableₓ'. -/
protected theorem stronglyMeasurable (f : α →ₘ[μ] β) : StronglyMeasurable f :=
  AEStronglyMeasurable.stronglyMeasurable_mk _
#align measure_theory.ae_eq_fun.strongly_measurable MeasureTheory.AEEqFun.stronglyMeasurable

/- warning: measure_theory.ae_eq_fun.ae_strongly_measurable -> MeasureTheory.AEEqFun.aestronglyMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f) μ
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ), MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 f) μ
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.ae_strongly_measurable MeasureTheory.AEEqFun.aestronglyMeasurableₓ'. -/
protected theorem aestronglyMeasurable (f : α →ₘ[μ] β) : AEStronglyMeasurable f μ :=
  f.StronglyMeasurable.AEStronglyMeasurable
#align measure_theory.ae_eq_fun.ae_strongly_measurable MeasureTheory.AEEqFun.aestronglyMeasurable

#print MeasureTheory.AEEqFun.measurable /-
protected theorem measurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α →ₘ[μ] β) : Measurable f :=
  AEStronglyMeasurable.measurable_mk _
#align measure_theory.ae_eq_fun.measurable MeasureTheory.AEEqFun.measurable
-/

#print MeasureTheory.AEEqFun.aemeasurable /-
protected theorem aemeasurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α →ₘ[μ] β) : AEMeasurable f μ :=
  f.Measurable.AEMeasurable
#align measure_theory.ae_eq_fun.ae_measurable MeasureTheory.AEEqFun.aemeasurable
-/

/- warning: measure_theory.ae_eq_fun.quot_mk_eq_mk -> MeasureTheory.AEEqFun.quot_mk_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ), Eq.{succ (max u1 u2)} (Quot.{succ (max u1 u2)} (Subtype.{max (succ u1) (succ u2)} (α -> β) (fun (f : α -> β) => MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ)) (Setoid.r.{max 1 (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (α -> β) (fun (f : α -> β) => MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ)) (MeasureTheory.Measure.aeEqSetoid.{u1, u2} α β _inst_1 _inst_2 μ))) (Quot.mk.{succ (max u1 u2)} (Subtype.{max (succ u1) (succ u2)} (α -> β) (fun (f : α -> β) => MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ)) (Setoid.r.{max 1 (succ u1) (succ u2)} (Subtype.{max (succ u1) (succ u2)} (α -> β) (fun (f : α -> β) => MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ)) (MeasureTheory.Measure.aeEqSetoid.{u1, u2} α β _inst_1 _inst_2 μ)) (Subtype.mk.{max (succ u1) (succ u2)} (α -> β) (fun (f : α -> β) => MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ) f hf)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 f μ), Eq.{max (succ u2) (succ u1)} (Quot.{max (succ u2) (succ u1)} (Subtype.{max (succ u2) (succ u1)} (α -> β) (fun (f : α -> β) => MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 f μ)) (Setoid.r.{max (succ u2) (succ u1)} (Subtype.{max (succ u2) (succ u1)} (α -> β) (fun (f : α -> β) => MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 f μ)) (MeasureTheory.Measure.aeEqSetoid.{u2, u1} α β _inst_1 _inst_2 μ))) (Quot.mk.{max (succ u2) (succ u1)} (Subtype.{max (succ u2) (succ u1)} (α -> β) (fun (f : α -> β) => MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 f μ)) (Setoid.r.{max (succ u2) (succ u1)} (Subtype.{max (succ u2) (succ u1)} (α -> β) (fun (f : α -> β) => MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 f μ)) (MeasureTheory.Measure.aeEqSetoid.{u2, u1} α β _inst_1 _inst_2 μ)) (Subtype.mk.{max (succ u2) (succ u1)} (α -> β) (fun (f : α -> β) => MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 f μ) f hf)) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ β _inst_2 f hf)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.quot_mk_eq_mk MeasureTheory.AEEqFun.quot_mk_eq_mkₓ'. -/
@[simp]
theorem quot_mk_eq_mk (f : α → β) (hf) :
    (Quot.mk (@Setoid.r _ <| μ.aeEqSetoid β) ⟨f, hf⟩ : α →ₘ[μ] β) = mk f hf :=
  rfl
#align measure_theory.ae_eq_fun.quot_mk_eq_mk MeasureTheory.AEEqFun.quot_mk_eq_mk

/- warning: measure_theory.ae_eq_fun.mk_eq_mk -> MeasureTheory.AEEqFun.mk_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] {f : α -> β} {g : α -> β} {hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ} {hg : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 g μ}, Iff (Eq.{succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 g hg)) (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] {f : α -> β} {g : α -> β} {hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 f μ} {hg : MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 g μ}, Iff (Eq.{max (succ u2) (succ u1)} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ β _inst_2 f hf) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ β _inst_2 g hg)) (Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) f g)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.mk_eq_mk MeasureTheory.AEEqFun.mk_eq_mkₓ'. -/
@[simp]
theorem mk_eq_mk {f g : α → β} {hf hg} : (mk f hf : α →ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
  Quotient.eq''
#align measure_theory.ae_eq_fun.mk_eq_mk MeasureTheory.AEEqFun.mk_eq_mk

/- warning: measure_theory.ae_eq_fun.mk_coe_fn -> MeasureTheory.AEEqFun.mk_coeFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), Eq.{succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f) (MeasureTheory.AEEqFun.aestronglyMeasurable.{u1, u2} α β _inst_1 μ _inst_2 f)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ), Eq.{max (succ u2) (succ u1)} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ β _inst_2 (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 f) (MeasureTheory.AEEqFun.aestronglyMeasurable.{u1, u2} α β _inst_1 μ _inst_2 f)) f
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.mk_coe_fn MeasureTheory.AEEqFun.mk_coeFnₓ'. -/
@[simp]
theorem mk_coeFn (f : α →ₘ[μ] β) : mk f f.AEStronglyMeasurable = f :=
  by
  conv_rhs => rw [← Quotient.out_eq' f]
  set g : { f : α → β // ae_strongly_measurable f μ } := Quotient.out' f with hg
  have : g = ⟨g.1, g.2⟩ := Subtype.eq rfl
  rw [this, ← mk, mk_eq_mk]
  exact (ae_strongly_measurable.ae_eq_mk _).symm
#align measure_theory.ae_eq_fun.mk_coe_fn MeasureTheory.AEEqFun.mk_coeFn

/- warning: measure_theory.ae_eq_fun.ext -> MeasureTheory.AEEqFun.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] {f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ} {g : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ}, (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) g)) -> (Eq.{succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] {f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ} {g : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ}, (Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 f) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 g)) -> (Eq.{max (succ u2) (succ u1)} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) f g)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.ext MeasureTheory.AEEqFun.extₓ'. -/
@[ext]
theorem ext {f g : α →ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g := by
  rwa [← f.mk_coe_fn, ← g.mk_coe_fn, mk_eq_mk]
#align measure_theory.ae_eq_fun.ext MeasureTheory.AEEqFun.ext

/- warning: measure_theory.ae_eq_fun.ext_iff -> MeasureTheory.AEEqFun.ext_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] {f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ} {g : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ}, Iff (Eq.{succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) f g) (Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] {f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ} {g : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ}, Iff (Eq.{max (succ u2) (succ u1)} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) f g) (Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 f) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 g))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.ext_iff MeasureTheory.AEEqFun.ext_iffₓ'. -/
theorem ext_iff {f g : α →ₘ[μ] β} : f = g ↔ f =ᵐ[μ] g :=
  ⟨fun h => by rw [h], fun h => ext h⟩
#align measure_theory.ae_eq_fun.ext_iff MeasureTheory.AEEqFun.ext_iff

/- warning: measure_theory.ae_eq_fun.coe_fn_mk -> MeasureTheory.AEEqFun.coeFn_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ), Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 f μ), Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ β _inst_2 f hf)) f
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_mk MeasureTheory.AEEqFun.coeFn_mkₓ'. -/
theorem coeFn_mk (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β) =ᵐ[μ] f :=
  by
  apply (ae_strongly_measurable.ae_eq_mk _).symm.trans
  exact @Quotient.mk_out' _ (μ.ae_eq_setoid β) (⟨f, hf⟩ : { f // ae_strongly_measurable f μ })
#align measure_theory.ae_eq_fun.coe_fn_mk MeasureTheory.AEEqFun.coeFn_mk

/- warning: measure_theory.ae_eq_fun.induction_on -> MeasureTheory.AEEqFun.induction_on is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) {p : (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) -> Prop}, (forall (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ), p (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf)) -> (p f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) {p : (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) -> Prop}, (forall (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 f μ), p (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ β _inst_2 f hf)) -> (p f)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.induction_on MeasureTheory.AEEqFun.induction_onₓ'. -/
@[elab_as_elim]
theorem induction_on (f : α →ₘ[μ] β) {p : (α →ₘ[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
  Quotient.inductionOn' f <| Subtype.forall.2 H
#align measure_theory.ae_eq_fun.induction_on MeasureTheory.AEEqFun.induction_on

/- warning: measure_theory.ae_eq_fun.induction_on₂ -> MeasureTheory.AEEqFun.induction_on₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] {α' : Type.{u3}} {β' : Type.{u4}} [_inst_5 : MeasurableSpace.{u3} α'] [_inst_6 : TopologicalSpace.{u4} β'] {μ' : MeasureTheory.Measure.{u3} α' _inst_5} (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (f' : MeasureTheory.AEEqFun.{u3, u4} α' β' _inst_5 _inst_6 μ') {p : (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) -> (MeasureTheory.AEEqFun.{u3, u4} α' β' _inst_5 _inst_6 μ') -> Prop}, (forall (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ) (f' : α' -> β') (hf' : MeasureTheory.AEStronglyMeasurable.{u3, u4} α' β' _inst_6 _inst_5 f' μ'), p (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf) (MeasureTheory.AEEqFun.mk.{u3, u4} α' _inst_5 μ' β' _inst_6 f' hf')) -> (p f f')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] {α' : Type.{u4}} {β' : Type.{u3}} [_inst_5 : MeasurableSpace.{u4} α'] [_inst_6 : TopologicalSpace.{u3} β'] {μ' : MeasureTheory.Measure.{u4} α' _inst_5} (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (f' : MeasureTheory.AEEqFun.{u4, u3} α' β' _inst_5 _inst_6 μ') {p : (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) -> (MeasureTheory.AEEqFun.{u4, u3} α' β' _inst_5 _inst_6 μ') -> Prop}, (forall (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 f μ) (f' : α' -> β') (hf' : MeasureTheory.AEStronglyMeasurable.{u4, u3} α' β' _inst_6 _inst_5 f' μ'), p (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ β _inst_2 f hf) (MeasureTheory.AEEqFun.mk.{u4, u3} α' _inst_5 μ' β' _inst_6 f' hf')) -> (p f f')
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.induction_on₂ MeasureTheory.AEEqFun.induction_on₂ₓ'. -/
@[elab_as_elim]
theorem induction_on₂ {α' β' : Type _} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
    (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → Prop}
    (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) : p f f' :=
  induction_on f fun f hf => induction_on f' <| H f hf
#align measure_theory.ae_eq_fun.induction_on₂ MeasureTheory.AEEqFun.induction_on₂

/- warning: measure_theory.ae_eq_fun.induction_on₃ -> MeasureTheory.AEEqFun.induction_on₃ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] {α' : Type.{u3}} {β' : Type.{u4}} [_inst_5 : MeasurableSpace.{u3} α'] [_inst_6 : TopologicalSpace.{u4} β'] {μ' : MeasureTheory.Measure.{u3} α' _inst_5} {α'' : Type.{u5}} {β'' : Type.{u6}} [_inst_7 : MeasurableSpace.{u5} α''] [_inst_8 : TopologicalSpace.{u6} β''] {μ'' : MeasureTheory.Measure.{u5} α'' _inst_7} (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (f' : MeasureTheory.AEEqFun.{u3, u4} α' β' _inst_5 _inst_6 μ') (f'' : MeasureTheory.AEEqFun.{u5, u6} α'' β'' _inst_7 _inst_8 μ'') {p : (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) -> (MeasureTheory.AEEqFun.{u3, u4} α' β' _inst_5 _inst_6 μ') -> (MeasureTheory.AEEqFun.{u5, u6} α'' β'' _inst_7 _inst_8 μ'') -> Prop}, (forall (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ) (f' : α' -> β') (hf' : MeasureTheory.AEStronglyMeasurable.{u3, u4} α' β' _inst_6 _inst_5 f' μ') (f'' : α'' -> β'') (hf'' : MeasureTheory.AEStronglyMeasurable.{u5, u6} α'' β'' _inst_8 _inst_7 f'' μ''), p (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf) (MeasureTheory.AEEqFun.mk.{u3, u4} α' _inst_5 μ' β' _inst_6 f' hf') (MeasureTheory.AEEqFun.mk.{u5, u6} α'' _inst_7 μ'' β'' _inst_8 f'' hf'')) -> (p f f' f'')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] {α' : Type.{u6}} {β' : Type.{u5}} [_inst_5 : MeasurableSpace.{u6} α'] [_inst_6 : TopologicalSpace.{u5} β'] {μ' : MeasureTheory.Measure.{u6} α' _inst_5} {α'' : Type.{u4}} {β'' : Type.{u3}} [_inst_7 : MeasurableSpace.{u4} α''] [_inst_8 : TopologicalSpace.{u3} β''] {μ'' : MeasureTheory.Measure.{u4} α'' _inst_7} (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (f' : MeasureTheory.AEEqFun.{u6, u5} α' β' _inst_5 _inst_6 μ') (f'' : MeasureTheory.AEEqFun.{u4, u3} α'' β'' _inst_7 _inst_8 μ'') {p : (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) -> (MeasureTheory.AEEqFun.{u6, u5} α' β' _inst_5 _inst_6 μ') -> (MeasureTheory.AEEqFun.{u4, u3} α'' β'' _inst_7 _inst_8 μ'') -> Prop}, (forall (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 f μ) (f' : α' -> β') (hf' : MeasureTheory.AEStronglyMeasurable.{u6, u5} α' β' _inst_6 _inst_5 f' μ') (f'' : α'' -> β'') (hf'' : MeasureTheory.AEStronglyMeasurable.{u4, u3} α'' β'' _inst_8 _inst_7 f'' μ''), p (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ β _inst_2 f hf) (MeasureTheory.AEEqFun.mk.{u6, u5} α' _inst_5 μ' β' _inst_6 f' hf') (MeasureTheory.AEEqFun.mk.{u4, u3} α'' _inst_7 μ'' β'' _inst_8 f'' hf'')) -> (p f f' f'')
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.induction_on₃ MeasureTheory.AEEqFun.induction_on₃ₓ'. -/
@[elab_as_elim]
theorem induction_on₃ {α' β' : Type _} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
    {α'' β'' : Type _} [MeasurableSpace α''] [TopologicalSpace β''] {μ'' : Measure α''}
    (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') (f'' : α'' →ₘ[μ''] β'')
    {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → (α'' →ₘ[μ''] β'') → Prop}
    (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) : p f f' f'' :=
  induction_on f fun f hf => induction_on₂ f' f'' <| H f hf
#align measure_theory.ae_eq_fun.induction_on₃ MeasureTheory.AEEqFun.induction_on₃

#print MeasureTheory.AEEqFun.comp /-
/-- Given a continuous function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. -/
def comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
  Quotient.liftOn' f (fun f => mk (g ∘ (f : α → β)) (hg.comp_aestronglyMeasurable f.2))
    fun f f' H => mk_eq_mk.2 <| H.fun_comp g
#align measure_theory.ae_eq_fun.comp MeasureTheory.AEEqFun.comp
-/

/- warning: measure_theory.ae_eq_fun.comp_mk -> MeasureTheory.AEEqFun.comp_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (g : β -> γ) (hg : Continuous.{u2, u3} β γ _inst_2 _inst_3 g) (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ), Eq.{succ (max u1 u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.comp.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 g hg (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf)) (MeasureTheory.AEEqFun.mk.{u1, u3} α _inst_1 μ γ _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) (Continuous.comp_aestronglyMeasurable.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 g (fun (x : α) => f x) hg hf))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (g : β -> γ) (hg : Continuous.{u3, u2} β γ _inst_2 _inst_3 g) (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u3} α β _inst_2 _inst_1 f μ), Eq.{max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.comp.{u1, u3, u2} α β γ _inst_1 μ _inst_2 _inst_3 g hg (MeasureTheory.AEEqFun.mk.{u1, u3} α _inst_1 μ β _inst_2 f hf)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) (Continuous.comp_aestronglyMeasurable.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 g (fun (x : α) => f x) hg hf))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp_mk MeasureTheory.AEEqFun.comp_mkₓ'. -/
@[simp]
theorem comp_mk (g : β → γ) (hg : Continuous g) (f : α → β) (hf) :
    comp g hg (mk f hf : α →ₘ[μ] β) = mk (g ∘ f) (hg.comp_aestronglyMeasurable hf) :=
  rfl
#align measure_theory.ae_eq_fun.comp_mk MeasureTheory.AEEqFun.comp_mk

/- warning: measure_theory.ae_eq_fun.comp_eq_mk -> MeasureTheory.AEEqFun.comp_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (g : β -> γ) (hg : Continuous.{u2, u3} β γ _inst_2 _inst_3 g) (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), Eq.{succ (max u1 u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.comp.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 g hg f) (MeasureTheory.AEEqFun.mk.{u1, u3} α _inst_1 μ γ _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f)) (Continuous.comp_aestronglyMeasurable.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 g (fun (x : α) => coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f x) hg (MeasureTheory.AEEqFun.aestronglyMeasurable.{u1, u2} α β _inst_1 μ _inst_2 f)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (g : β -> γ) (hg : Continuous.{u3, u2} β γ _inst_2 _inst_3 g) (f : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ), Eq.{max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.comp.{u1, u3, u2} α β γ _inst_1 μ _inst_2 _inst_3 g hg f) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f)) (Continuous.comp_aestronglyMeasurable.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 g (fun (x : α) => MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f x) hg (MeasureTheory.AEEqFun.aestronglyMeasurable.{u3, u1} α β _inst_1 μ _inst_2 f)))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp_eq_mk MeasureTheory.AEEqFun.comp_eq_mkₓ'. -/
theorem comp_eq_mk (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) :
    comp g hg f = mk (g ∘ f) (hg.comp_aestronglyMeasurable f.AEStronglyMeasurable) := by
  rw [← comp_mk g hg f f.ae_strongly_measurable, mk_coe_fn]
#align measure_theory.ae_eq_fun.comp_eq_mk MeasureTheory.AEEqFun.comp_eq_mk

/- warning: measure_theory.ae_eq_fun.coe_fn_comp -> MeasureTheory.AEEqFun.coeFn_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (g : β -> γ) (hg : Continuous.{u2, u3} β γ _inst_2 _inst_3 g) (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), Filter.EventuallyEq.{u1, u3} α γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) (MeasureTheory.AEEqFun.comp.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 g hg f)) (Function.comp.{succ u1, succ u2, succ u3} α β γ g (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (g : β -> γ) (hg : Continuous.{u3, u2} β γ _inst_2 _inst_3 g) (f : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ), Filter.EventuallyEq.{u1, u2} α γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u1, u2} α γ _inst_1 μ _inst_3 (MeasureTheory.AEEqFun.comp.{u1, u3, u2} α β γ _inst_1 μ _inst_2 _inst_3 g hg f)) (Function.comp.{succ u1, succ u3, succ u2} α β γ g (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_comp MeasureTheory.AEEqFun.coeFn_compₓ'. -/
theorem coeFn_comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f :=
  by
  rw [comp_eq_mk]
  apply coe_fn_mk
#align measure_theory.ae_eq_fun.coe_fn_comp MeasureTheory.AEEqFun.coeFn_comp

section CompMeasurable

variable [MeasurableSpace β] [PseudoMetrizableSpace β] [BorelSpace β] [MeasurableSpace γ]
  [PseudoMetrizableSpace γ] [OpensMeasurableSpace γ] [SecondCountableTopology γ]

#print MeasureTheory.AEEqFun.compMeasurable /-
/-- Given a measurable function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. This requires that `γ` has a second countable topology. -/
def compMeasurable (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
  Quotient.liftOn' f
    (fun f' => mk (g ∘ (f' : α → β)) (hg.comp_aemeasurable f'.2.AEMeasurable).AEStronglyMeasurable)
    fun f f' H => mk_eq_mk.2 <| H.fun_comp g
#align measure_theory.ae_eq_fun.comp_measurable MeasureTheory.AEEqFun.compMeasurable
-/

/- warning: measure_theory.ae_eq_fun.comp_measurable_mk -> MeasureTheory.AEEqFun.compMeasurable_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_5 : MeasurableSpace.{u2} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_7 : BorelSpace.{u2} β _inst_2 _inst_5] [_inst_8 : MeasurableSpace.{u3} γ] [_inst_9 : TopologicalSpace.PseudoMetrizableSpace.{u3} γ _inst_3] [_inst_10 : OpensMeasurableSpace.{u3} γ _inst_3 _inst_8] [_inst_11 : TopologicalSpace.SecondCountableTopology.{u3} γ _inst_3] (g : β -> γ) (hg : Measurable.{u2, u3} β γ _inst_5 _inst_8 g) (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ), Eq.{succ (max u1 u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.compMeasurable.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 g hg (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf)) (MeasureTheory.AEEqFun.mk.{u1, u3} α _inst_1 μ γ _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) (AEMeasurable.aestronglyMeasurable.{u1, u3} α γ _inst_1 μ _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g f) _inst_8 _inst_9 _inst_10 _inst_11 (Measurable.comp_aemeasurable.{u1, u3, u2} α γ β _inst_1 _inst_8 μ _inst_5 f g hg (MeasureTheory.AEStronglyMeasurable.aemeasurable.{u1, u2} α _inst_1 μ β _inst_5 _inst_2 _inst_6 _inst_7 f hf))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : MeasurableSpace.{u3} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] [_inst_7 : BorelSpace.{u3} β _inst_2 _inst_5] [_inst_8 : MeasurableSpace.{u2} γ] [_inst_9 : TopologicalSpace.PseudoMetrizableSpace.{u2} γ _inst_3] [_inst_10 : OpensMeasurableSpace.{u2} γ _inst_3 _inst_8] [_inst_11 : TopologicalSpace.SecondCountableTopology.{u2} γ _inst_3] (g : β -> γ) (hg : Measurable.{u3, u2} β γ _inst_5 _inst_8 g) (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u3} α β _inst_2 _inst_1 f μ), Eq.{max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.compMeasurable.{u1, u3, u2} α β γ _inst_1 μ _inst_2 _inst_3 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 g hg (MeasureTheory.AEEqFun.mk.{u1, u3} α _inst_1 μ β _inst_2 f hf)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) (AEMeasurable.aestronglyMeasurable.{u1, u2} α γ _inst_1 μ _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g f) _inst_8 _inst_9 _inst_10 _inst_11 (Measurable.comp_aemeasurable.{u1, u2, u3} α γ β _inst_1 _inst_8 μ _inst_5 f g hg (MeasureTheory.AEStronglyMeasurable.aemeasurable.{u1, u3} α _inst_1 μ β _inst_5 _inst_2 _inst_6 _inst_7 f hf))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp_measurable_mk MeasureTheory.AEEqFun.compMeasurable_mkₓ'. -/
@[simp]
theorem compMeasurable_mk (g : β → γ) (hg : Measurable g) (f : α → β)
    (hf : AEStronglyMeasurable f μ) :
    compMeasurable g hg (mk f hf : α →ₘ[μ] β) =
      mk (g ∘ f) (hg.comp_aemeasurable hf.AEMeasurable).AEStronglyMeasurable :=
  rfl
#align measure_theory.ae_eq_fun.comp_measurable_mk MeasureTheory.AEEqFun.compMeasurable_mk

/- warning: measure_theory.ae_eq_fun.comp_measurable_eq_mk -> MeasureTheory.AEEqFun.compMeasurable_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_5 : MeasurableSpace.{u2} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_7 : BorelSpace.{u2} β _inst_2 _inst_5] [_inst_8 : MeasurableSpace.{u3} γ] [_inst_9 : TopologicalSpace.PseudoMetrizableSpace.{u3} γ _inst_3] [_inst_10 : OpensMeasurableSpace.{u3} γ _inst_3 _inst_8] [_inst_11 : TopologicalSpace.SecondCountableTopology.{u3} γ _inst_3] (g : β -> γ) (hg : Measurable.{u2, u3} β γ _inst_5 _inst_8 g) (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), Eq.{succ (max u1 u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.compMeasurable.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 g hg f) (MeasureTheory.AEEqFun.mk.{u1, u3} α _inst_1 μ γ _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f)) (AEMeasurable.aestronglyMeasurable.{u1, u3} α γ _inst_1 μ _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ g (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f)) _inst_8 _inst_9 _inst_10 _inst_11 (Measurable.comp_aemeasurable.{u1, u3, u2} α γ β _inst_1 _inst_8 μ _inst_5 (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f) g hg (MeasureTheory.AEEqFun.aemeasurable.{u1, u2} α β _inst_1 μ _inst_2 _inst_6 _inst_5 _inst_7 f))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : MeasurableSpace.{u3} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] [_inst_7 : BorelSpace.{u3} β _inst_2 _inst_5] [_inst_8 : MeasurableSpace.{u2} γ] [_inst_9 : TopologicalSpace.PseudoMetrizableSpace.{u2} γ _inst_3] [_inst_10 : OpensMeasurableSpace.{u2} γ _inst_3 _inst_8] [_inst_11 : TopologicalSpace.SecondCountableTopology.{u2} γ _inst_3] (g : β -> γ) (hg : Measurable.{u3, u2} β γ _inst_5 _inst_8 g) (f : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ), Eq.{max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.compMeasurable.{u1, u3, u2} α β γ _inst_1 μ _inst_2 _inst_3 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 g hg f) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f)) (AEMeasurable.aestronglyMeasurable.{u1, u2} α γ _inst_1 μ _inst_3 (Function.comp.{succ u1, succ u3, succ u2} α β γ g (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f)) _inst_8 _inst_9 _inst_10 _inst_11 (Measurable.comp_aemeasurable.{u1, u2, u3} α γ β _inst_1 _inst_8 μ _inst_5 (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f) g hg (MeasureTheory.AEEqFun.aemeasurable.{u1, u3} α β _inst_1 μ _inst_2 _inst_6 _inst_5 _inst_7 f))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp_measurable_eq_mk MeasureTheory.AEEqFun.compMeasurable_eq_mkₓ'. -/
theorem compMeasurable_eq_mk (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    compMeasurable g hg f = mk (g ∘ f) (hg.comp_aemeasurable f.AEMeasurable).AEStronglyMeasurable :=
  by rw [← comp_measurable_mk g hg f f.ae_strongly_measurable, mk_coe_fn]
#align measure_theory.ae_eq_fun.comp_measurable_eq_mk MeasureTheory.AEEqFun.compMeasurable_eq_mk

/- warning: measure_theory.ae_eq_fun.coe_fn_comp_measurable -> MeasureTheory.AEEqFun.coeFn_compMeasurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_5 : MeasurableSpace.{u2} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_7 : BorelSpace.{u2} β _inst_2 _inst_5] [_inst_8 : MeasurableSpace.{u3} γ] [_inst_9 : TopologicalSpace.PseudoMetrizableSpace.{u3} γ _inst_3] [_inst_10 : OpensMeasurableSpace.{u3} γ _inst_3 _inst_8] [_inst_11 : TopologicalSpace.SecondCountableTopology.{u3} γ _inst_3] (g : β -> γ) (hg : Measurable.{u2, u3} β γ _inst_5 _inst_8 g) (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), Filter.EventuallyEq.{u1, u3} α γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) (MeasureTheory.AEEqFun.compMeasurable.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 g hg f)) (Function.comp.{succ u1, succ u2, succ u3} α β γ g (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : MeasurableSpace.{u3} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] [_inst_7 : BorelSpace.{u3} β _inst_2 _inst_5] [_inst_8 : MeasurableSpace.{u2} γ] [_inst_9 : TopologicalSpace.PseudoMetrizableSpace.{u2} γ _inst_3] [_inst_10 : OpensMeasurableSpace.{u2} γ _inst_3 _inst_8] [_inst_11 : TopologicalSpace.SecondCountableTopology.{u2} γ _inst_3] (g : β -> γ) (hg : Measurable.{u3, u2} β γ _inst_5 _inst_8 g) (f : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ), Filter.EventuallyEq.{u1, u2} α γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u1, u2} α γ _inst_1 μ _inst_3 (MeasureTheory.AEEqFun.compMeasurable.{u1, u3, u2} α β γ _inst_1 μ _inst_2 _inst_3 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 g hg f)) (Function.comp.{succ u1, succ u3, succ u2} α β γ g (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_comp_measurable MeasureTheory.AEEqFun.coeFn_compMeasurableₓ'. -/
theorem coeFn_compMeasurable (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    compMeasurable g hg f =ᵐ[μ] g ∘ f :=
  by
  rw [comp_measurable_eq_mk]
  apply coe_fn_mk
#align measure_theory.ae_eq_fun.coe_fn_comp_measurable MeasureTheory.AEEqFun.coeFn_compMeasurable

end CompMeasurable

/- warning: measure_theory.ae_eq_fun.pair -> MeasureTheory.AEEqFun.pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ], (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) -> (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) -> (MeasureTheory.AEEqFun.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ], (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) -> (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) -> (MeasureTheory.AEEqFun.{u1, max u3 u2} α (Prod.{u2, u3} β γ) _inst_1 (instTopologicalSpaceProd.{u2, u3} β γ _inst_2 _inst_3) μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.pair MeasureTheory.AEEqFun.pairₓ'. -/
/-- The class of `x ↦ (f x, g x)`. -/
def pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : α →ₘ[μ] β × γ :=
  Quotient.liftOn₂' f g (fun f g => mk (fun x => (f.1 x, g.1 x)) (f.2.prod_mk g.2))
    fun f g f' g' Hf Hg => mk_eq_mk.2 <| Hf.prod_mk Hg
#align measure_theory.ae_eq_fun.pair MeasureTheory.AEEqFun.pair

/- warning: measure_theory.ae_eq_fun.pair_mk_mk -> MeasureTheory.AEEqFun.pair_mk_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ) (g : α -> γ) (hg : MeasureTheory.AEStronglyMeasurable.{u1, u3} α γ _inst_3 _inst_1 g μ), Eq.{succ (max u1 u2 u3)} (MeasureTheory.AEEqFun.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) μ) (MeasureTheory.AEEqFun.pair.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf) (MeasureTheory.AEEqFun.mk.{u1, u3} α _inst_1 μ γ _inst_3 g hg)) (MeasureTheory.AEEqFun.mk.{u1, max u2 u3} α _inst_1 μ (Prod.{u2, u3} β γ) (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) (fun (x : α) => Prod.mk.{u2, u3} β γ (f x) (g x)) (MeasureTheory.AEStronglyMeasurable.prod_mk.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 f (fun (x : α) => g x) hf hg))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] {μ : MeasureTheory.Measure.{u3} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u3, u2} α β _inst_2 _inst_1 f μ) (g : α -> γ) (hg : MeasureTheory.AEStronglyMeasurable.{u3, u1} α γ _inst_3 _inst_1 g μ), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (MeasureTheory.AEEqFun.{u3, max u1 u2} α (Prod.{u2, u1} β γ) _inst_1 (instTopologicalSpaceProd.{u2, u1} β γ _inst_2 _inst_3) μ) (MeasureTheory.AEEqFun.pair.{u3, u2, u1} α β γ _inst_1 μ _inst_2 _inst_3 (MeasureTheory.AEEqFun.mk.{u3, u2} α _inst_1 μ β _inst_2 f hf) (MeasureTheory.AEEqFun.mk.{u3, u1} α _inst_1 μ γ _inst_3 g hg)) (MeasureTheory.AEEqFun.mk.{u3, max u1 u2} α _inst_1 μ (Prod.{u2, u1} β γ) (instTopologicalSpaceProd.{u2, u1} β γ _inst_2 _inst_3) (fun (x : α) => Prod.mk.{u2, u1} β γ (f x) (g x)) (MeasureTheory.AEStronglyMeasurable.prod_mk.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 f (fun (x : α) => g x) hf hg))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.pair_mk_mk MeasureTheory.AEEqFun.pair_mk_mkₓ'. -/
@[simp]
theorem pair_mk_mk (f : α → β) (hf) (g : α → γ) (hg) :
    (mk f hf : α →ₘ[μ] β).pair (mk g hg) = mk (fun x => (f x, g x)) (hf.prod_mk hg) :=
  rfl
#align measure_theory.ae_eq_fun.pair_mk_mk MeasureTheory.AEEqFun.pair_mk_mk

/- warning: measure_theory.ae_eq_fun.pair_eq_mk -> MeasureTheory.AEEqFun.pair_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ), Eq.{succ (max u1 u2 u3)} (MeasureTheory.AEEqFun.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) μ) (MeasureTheory.AEEqFun.pair.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 f g) (MeasureTheory.AEEqFun.mk.{u1, max u2 u3} α _inst_1 μ (Prod.{u2, u3} β γ) (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) (fun (x : α) => Prod.mk.{u2, u3} β γ (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f x) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) g x)) (MeasureTheory.AEStronglyMeasurable.prod_mk.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f) (fun (x : α) => coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) g x) (MeasureTheory.AEEqFun.aestronglyMeasurable.{u1, u2} α β _inst_1 μ _inst_2 f) (MeasureTheory.AEEqFun.aestronglyMeasurable.{u1, u3} α γ _inst_1 μ _inst_3 g)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] {μ : MeasureTheory.Measure.{u3} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (f : MeasureTheory.AEEqFun.{u3, u2} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u3, u1} α γ _inst_1 _inst_3 μ), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (MeasureTheory.AEEqFun.{u3, max u1 u2} α (Prod.{u2, u1} β γ) _inst_1 (instTopologicalSpaceProd.{u2, u1} β γ _inst_2 _inst_3) μ) (MeasureTheory.AEEqFun.pair.{u3, u2, u1} α β γ _inst_1 μ _inst_2 _inst_3 f g) (MeasureTheory.AEEqFun.mk.{u3, max u1 u2} α _inst_1 μ (Prod.{u2, u1} β γ) (instTopologicalSpaceProd.{u2, u1} β γ _inst_2 _inst_3) (fun (x : α) => Prod.mk.{u2, u1} β γ (MeasureTheory.AEEqFun.cast.{u3, u2} α β _inst_1 μ _inst_2 f x) (MeasureTheory.AEEqFun.cast.{u3, u1} α γ _inst_1 μ _inst_3 g x)) (MeasureTheory.AEStronglyMeasurable.prod_mk.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 (MeasureTheory.AEEqFun.cast.{u3, u2} α β _inst_1 μ _inst_2 f) (fun (x : α) => MeasureTheory.AEEqFun.cast.{u3, u1} α γ _inst_1 μ _inst_3 g x) (MeasureTheory.AEEqFun.aestronglyMeasurable.{u2, u3} α β _inst_1 μ _inst_2 f) (MeasureTheory.AEEqFun.aestronglyMeasurable.{u1, u3} α γ _inst_1 μ _inst_3 g)))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.pair_eq_mk MeasureTheory.AEEqFun.pair_eq_mkₓ'. -/
theorem pair_eq_mk (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
    f.pair g = mk (fun x => (f x, g x)) (f.AEStronglyMeasurable.prod_mk g.AEStronglyMeasurable) :=
  by simp only [← pair_mk_mk, mk_coe_fn]
#align measure_theory.ae_eq_fun.pair_eq_mk MeasureTheory.AEEqFun.pair_eq_mk

/- warning: measure_theory.ae_eq_fun.coe_fn_pair -> MeasureTheory.AEEqFun.coeFn_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2 u3), max (succ u1) (succ (max u2 u3))} (MeasureTheory.AEEqFun.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) μ) (fun (_x : MeasureTheory.AEEqFun.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) μ) => α -> (Prod.{u2, u3} β γ)) (MeasureTheory.AEEqFun.instCoeFun.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 μ (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3)) (MeasureTheory.AEEqFun.pair.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 f g)) (fun (x : α) => Prod.mk.{u2, u3} β γ (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f x) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) g x))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] {μ : MeasureTheory.Measure.{u3} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (f : MeasureTheory.AEEqFun.{u3, u2} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u3, u1} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u3, max u2 u1} α (Prod.{u2, u1} β γ) (MeasureTheory.Measure.ae.{u3} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u3, max u2 u1} α (Prod.{u2, u1} β γ) _inst_1 μ (instTopologicalSpaceProd.{u2, u1} β γ _inst_2 _inst_3) (MeasureTheory.AEEqFun.pair.{u3, u2, u1} α β γ _inst_1 μ _inst_2 _inst_3 f g)) (fun (x : α) => Prod.mk.{u2, u1} β γ (MeasureTheory.AEEqFun.cast.{u3, u2} α β _inst_1 μ _inst_2 f x) (MeasureTheory.AEEqFun.cast.{u3, u1} α γ _inst_1 μ _inst_3 g x))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_pair MeasureTheory.AEEqFun.coeFn_pairₓ'. -/
theorem coeFn_pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : f.pair g =ᵐ[μ] fun x => (f x, g x) :=
  by
  rw [pair_eq_mk]
  apply coe_fn_mk
#align measure_theory.ae_eq_fun.coe_fn_pair MeasureTheory.AEEqFun.coeFn_pair

/- warning: measure_theory.ae_eq_fun.comp₂ -> MeasureTheory.AEEqFun.comp₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (g : β -> γ -> δ), (Continuous.{max u2 u3, u4} (Prod.{u2, u3} β γ) δ (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u2, u3, u4} β γ δ g)) -> (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) -> (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) -> (MeasureTheory.AEEqFun.{u1, u4} α δ _inst_1 _inst_4 μ)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (g : β -> γ -> δ), (Continuous.{max u3 u2, u4} (Prod.{u2, u3} β γ) δ (instTopologicalSpaceProd.{u2, u3} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u2, u3, u4} β γ δ g)) -> (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) -> (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) -> (MeasureTheory.AEEqFun.{u1, u4} α δ _inst_1 _inst_4 μ)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp₂ MeasureTheory.AEEqFun.comp₂ₓ'. -/
/-- Given a continuous function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `λ a, g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[λ a, g (f₁ a) (f₂ a)] : α →ₘ γ` -/
def comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    α →ₘ[μ] δ :=
  comp _ hg (f₁.pair f₂)
#align measure_theory.ae_eq_fun.comp₂ MeasureTheory.AEEqFun.comp₂

/- warning: measure_theory.ae_eq_fun.comp₂_mk_mk -> MeasureTheory.AEEqFun.comp₂_mk_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (g : β -> γ -> δ) (hg : Continuous.{max u2 u3, u4} (Prod.{u2, u3} β γ) δ (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u2, u3, u4} β γ δ g)) (f₁ : α -> β) (f₂ : α -> γ) (hf₁ : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f₁ μ) (hf₂ : MeasureTheory.AEStronglyMeasurable.{u1, u3} α γ _inst_3 _inst_1 f₂ μ), Eq.{succ (max u1 u4)} (MeasureTheory.AEEqFun.{u1, u4} α δ _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.comp₂.{u1, u2, u3, u4} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 g hg (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f₁ hf₁) (MeasureTheory.AEEqFun.mk.{u1, u3} α _inst_1 μ γ _inst_3 f₂ hf₂)) (MeasureTheory.AEEqFun.mk.{u1, u4} α _inst_1 μ δ _inst_4 (fun (a : α) => g (f₁ a) (f₂ a)) (Continuous.comp_aestronglyMeasurable.{u1, max u2 u3, u4} α (Prod.{u2, u3} β γ) δ _inst_1 μ (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u2, u3, u4} β γ δ g) (fun (x : α) => Prod.mk.{u2, u3} β γ (f₁ x) (f₂ x)) hg (MeasureTheory.AEStronglyMeasurable.prod_mk.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 f₁ f₂ hf₁ hf₂)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u2} δ] (g : β -> γ -> δ) (hg : Continuous.{max u4 u3, u2} (Prod.{u3, u4} β γ) δ (instTopologicalSpaceProd.{u3, u4} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u3, u4, u2} β γ δ g)) (f₁ : α -> β) (f₂ : α -> γ) (hf₁ : MeasureTheory.AEStronglyMeasurable.{u1, u3} α β _inst_2 _inst_1 f₁ μ) (hf₂ : MeasureTheory.AEStronglyMeasurable.{u1, u4} α γ _inst_3 _inst_1 f₂ μ), Eq.{max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α δ _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.comp₂.{u1, u3, u4, u2} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 g hg (MeasureTheory.AEEqFun.mk.{u1, u3} α _inst_1 μ β _inst_2 f₁ hf₁) (MeasureTheory.AEEqFun.mk.{u1, u4} α _inst_1 μ γ _inst_3 f₂ hf₂)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ δ _inst_4 (fun (a : α) => g (f₁ a) (f₂ a)) (Continuous.comp_aestronglyMeasurable.{u1, u2, max u3 u4} α (Prod.{u3, u4} β γ) δ _inst_1 μ (instTopologicalSpaceProd.{u3, u4} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u3, u4, u2} β γ δ g) (fun (x : α) => Prod.mk.{u3, u4} β γ (f₁ x) (f₂ x)) hg (MeasureTheory.AEStronglyMeasurable.prod_mk.{u4, u3, u1} α β γ _inst_1 μ _inst_2 _inst_3 f₁ f₂ hf₁ hf₂)))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp₂_mk_mk MeasureTheory.AEEqFun.comp₂_mk_mkₓ'. -/
@[simp]
theorem comp₂_mk_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α → β) (f₂ : α → γ)
    (hf₁ hf₂) :
    comp₂ g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a)) (hg.comp_aestronglyMeasurable (hf₁.prod_mk hf₂)) :=
  rfl
#align measure_theory.ae_eq_fun.comp₂_mk_mk MeasureTheory.AEEqFun.comp₂_mk_mk

/- warning: measure_theory.ae_eq_fun.comp₂_eq_pair -> MeasureTheory.AEEqFun.comp₂_eq_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (g : β -> γ -> δ) (hg : Continuous.{max u2 u3, u4} (Prod.{u2, u3} β γ) δ (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u2, u3, u4} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ), Eq.{succ (max u1 u4)} (MeasureTheory.AEEqFun.{u1, u4} α δ _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.comp₂.{u1, u2, u3, u4} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 g hg f₁ f₂) (MeasureTheory.AEEqFun.comp.{u1, max u2 u3, u4} α (Prod.{u2, u3} β γ) δ _inst_1 μ (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u2, u3, u4} β γ δ g) hg (MeasureTheory.AEEqFun.pair.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u2} δ] (g : β -> γ -> δ) (hg : Continuous.{max u4 u3, u2} (Prod.{u3, u4} β γ) δ (instTopologicalSpaceProd.{u3, u4} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u3, u4, u2} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u4} α γ _inst_1 _inst_3 μ), Eq.{max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α δ _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.comp₂.{u1, u3, u4, u2} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 g hg f₁ f₂) (MeasureTheory.AEEqFun.comp.{u1, max u3 u4, u2} α (Prod.{u3, u4} β γ) δ _inst_1 μ (instTopologicalSpaceProd.{u3, u4} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u3, u4, u2} β γ δ g) hg (MeasureTheory.AEEqFun.pair.{u1, u3, u4} α β γ _inst_1 μ _inst_2 _inst_3 f₁ f₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp₂_eq_pair MeasureTheory.AEEqFun.comp₂_eq_pairₓ'. -/
theorem comp₂_eq_pair (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
  rfl
#align measure_theory.ae_eq_fun.comp₂_eq_pair MeasureTheory.AEEqFun.comp₂_eq_pair

/- warning: measure_theory.ae_eq_fun.comp₂_eq_mk -> MeasureTheory.AEEqFun.comp₂_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (g : β -> γ -> δ) (hg : Continuous.{max u2 u3, u4} (Prod.{u2, u3} β γ) δ (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u2, u3, u4} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ), Eq.{succ (max u1 u4)} (MeasureTheory.AEEqFun.{u1, u4} α δ _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.comp₂.{u1, u2, u3, u4} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 g hg f₁ f₂) (MeasureTheory.AEEqFun.mk.{u1, u4} α _inst_1 μ δ _inst_4 (fun (a : α) => g (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f₁ a) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) f₂ a)) (Continuous.comp_aestronglyMeasurable.{u1, max u2 u3, u4} α (Prod.{u2, u3} β γ) δ _inst_1 μ (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u2, u3, u4} β γ δ g) (fun (x : α) => Prod.mk.{u2, u3} β γ (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f₁ x) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) f₂ x)) hg (MeasureTheory.AEStronglyMeasurable.prod_mk.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f₁) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) f₂) (MeasureTheory.AEEqFun.aestronglyMeasurable.{u1, u2} α β _inst_1 μ _inst_2 f₁) (MeasureTheory.AEEqFun.aestronglyMeasurable.{u1, u3} α γ _inst_1 μ _inst_3 f₂))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u2} δ] (g : β -> γ -> δ) (hg : Continuous.{max u4 u3, u2} (Prod.{u3, u4} β γ) δ (instTopologicalSpaceProd.{u3, u4} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u3, u4, u2} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u4} α γ _inst_1 _inst_3 μ), Eq.{max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α δ _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.comp₂.{u1, u3, u4, u2} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 g hg f₁ f₂) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ δ _inst_4 (fun (a : α) => g (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f₁ a) (MeasureTheory.AEEqFun.cast.{u1, u4} α γ _inst_1 μ _inst_3 f₂ a)) (Continuous.comp_aestronglyMeasurable.{u1, u2, max u3 u4} α (Prod.{u3, u4} β γ) δ _inst_1 μ (instTopologicalSpaceProd.{u3, u4} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u3, u4, u2} β γ δ g) (fun (x : α) => Prod.mk.{u3, u4} β γ (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f₁ x) (MeasureTheory.AEEqFun.cast.{u1, u4} α γ _inst_1 μ _inst_3 f₂ x)) hg (MeasureTheory.AEStronglyMeasurable.prod_mk.{u4, u3, u1} α β γ _inst_1 μ _inst_2 _inst_3 (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f₁) (MeasureTheory.AEEqFun.cast.{u1, u4} α γ _inst_1 μ _inst_3 f₂) (MeasureTheory.AEEqFun.aestronglyMeasurable.{u3, u1} α β _inst_1 μ _inst_2 f₁) (MeasureTheory.AEEqFun.aestronglyMeasurable.{u4, u1} α γ _inst_1 μ _inst_3 f₂))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp₂_eq_mk MeasureTheory.AEEqFun.comp₂_eq_mkₓ'. -/
theorem comp₂_eq_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) :
    comp₂ g hg f₁ f₂ =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aestronglyMeasurable (f₁.AEStronglyMeasurable.prod_mk f₂.AEStronglyMeasurable)) :=
  by rw [comp₂_eq_pair, pair_eq_mk, comp_mk] <;> rfl
#align measure_theory.ae_eq_fun.comp₂_eq_mk MeasureTheory.AEEqFun.comp₂_eq_mk

/- warning: measure_theory.ae_eq_fun.coe_fn_comp₂ -> MeasureTheory.AEEqFun.coeFn_comp₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (g : β -> γ -> δ) (hg : Continuous.{max u2 u3, u4} (Prod.{u2, u3} β γ) δ (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u2, u3, u4} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u1, u4} α δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u4), max (succ u1) (succ u4)} (MeasureTheory.AEEqFun.{u1, u4} α δ _inst_1 _inst_4 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u4} α δ _inst_1 _inst_4 μ) => α -> δ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u4} α δ _inst_1 μ _inst_4) (MeasureTheory.AEEqFun.comp₂.{u1, u2, u3, u4} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 g hg f₁ f₂)) (fun (a : α) => g (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f₁ a) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) f₂ a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u2} δ] (g : β -> γ -> δ) (hg : Continuous.{max u4 u3, u2} (Prod.{u3, u4} β γ) δ (instTopologicalSpaceProd.{u3, u4} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u3, u4, u2} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u4} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u1, u2} α δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u1, u2} α δ _inst_1 μ _inst_4 (MeasureTheory.AEEqFun.comp₂.{u1, u3, u4, u2} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 g hg f₁ f₂)) (fun (a : α) => g (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f₁ a) (MeasureTheory.AEEqFun.cast.{u1, u4} α γ _inst_1 μ _inst_3 f₂ a))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_comp₂ MeasureTheory.AEEqFun.coeFn_comp₂ₓ'. -/
theorem coeFn_comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) :=
  by
  rw [comp₂_eq_mk]
  apply coe_fn_mk
#align measure_theory.ae_eq_fun.coe_fn_comp₂ MeasureTheory.AEEqFun.coeFn_comp₂

section

variable [MeasurableSpace β] [PseudoMetrizableSpace β] [BorelSpace β] [SecondCountableTopology β]
  [MeasurableSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]
  [MeasurableSpace δ] [PseudoMetrizableSpace δ] [OpensMeasurableSpace δ] [SecondCountableTopology δ]

#print MeasureTheory.AEEqFun.comp₂Measurable /-
/-- Given a measurable function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `λ a, g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[λ a, g (f₁ a) (f₂ a)] : α →ₘ γ`. This requires `δ` to have second-countable topology. -/
def comp₂Measurable (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : α →ₘ[μ] δ :=
  compMeasurable _ hg (f₁.pair f₂)
#align measure_theory.ae_eq_fun.comp₂_measurable MeasureTheory.AEEqFun.comp₂Measurable
-/

/- warning: measure_theory.ae_eq_fun.comp₂_measurable_mk_mk -> MeasureTheory.AEEqFun.comp₂Measurable_mk_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] [_inst_5 : MeasurableSpace.{u2} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_7 : BorelSpace.{u2} β _inst_2 _inst_5] [_inst_8 : TopologicalSpace.SecondCountableTopology.{u2} β _inst_2] [_inst_9 : MeasurableSpace.{u3} γ] [_inst_10 : TopologicalSpace.PseudoMetrizableSpace.{u3} γ _inst_3] [_inst_11 : BorelSpace.{u3} γ _inst_3 _inst_9] [_inst_12 : TopologicalSpace.SecondCountableTopology.{u3} γ _inst_3] [_inst_13 : MeasurableSpace.{u4} δ] [_inst_14 : TopologicalSpace.PseudoMetrizableSpace.{u4} δ _inst_4] [_inst_15 : OpensMeasurableSpace.{u4} δ _inst_4 _inst_13] [_inst_16 : TopologicalSpace.SecondCountableTopology.{u4} δ _inst_4] (g : β -> γ -> δ) (hg : Measurable.{max u2 u3, u4} (Prod.{u2, u3} β γ) δ (Prod.instMeasurableSpace.{u2, u3} β γ _inst_5 _inst_9) _inst_13 (Function.uncurry.{u2, u3, u4} β γ δ g)) (f₁ : α -> β) (f₂ : α -> γ) (hf₁ : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f₁ μ) (hf₂ : MeasureTheory.AEStronglyMeasurable.{u1, u3} α γ _inst_3 _inst_1 f₂ μ), Eq.{succ (max u1 u4)} (MeasureTheory.AEEqFun.{u1, u4} α δ _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.comp₂Measurable.{u1, u2, u3, u4} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 _inst_12 _inst_13 _inst_14 _inst_15 _inst_16 g hg (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f₁ hf₁) (MeasureTheory.AEEqFun.mk.{u1, u3} α _inst_1 μ γ _inst_3 f₂ hf₂)) (MeasureTheory.AEEqFun.mk.{u1, u4} α _inst_1 μ δ _inst_4 (fun (a : α) => g (f₁ a) (f₂ a)) (AEMeasurable.aestronglyMeasurable.{u1, u4} α δ _inst_1 μ _inst_4 (Function.comp.{succ u1, succ (max u2 u3), succ u4} α (Prod.{u2, u3} β γ) δ (Function.uncurry.{u2, u3, u4} β γ δ g) (fun (x : α) => Prod.mk.{u2, u3} β γ (f₁ x) (f₂ x))) _inst_13 _inst_14 _inst_15 _inst_16 (Measurable.comp_aemeasurable.{u1, u4, max u2 u3} α δ (Prod.{u2, u3} β γ) _inst_1 _inst_13 μ (Prod.instMeasurableSpace.{u2, u3} β γ _inst_5 _inst_9) (fun (x : α) => Prod.mk.{u2, u3} β γ (f₁ x) (f₂ x)) (Function.uncurry.{u2, u3, u4} β γ δ g) hg (AEMeasurable.prod_mk.{u1, u2, u3} α β γ _inst_1 _inst_5 _inst_9 μ f₁ f₂ (MeasureTheory.AEStronglyMeasurable.aemeasurable.{u1, u2} α _inst_1 μ β _inst_5 _inst_2 _inst_6 _inst_7 f₁ hf₁) (MeasureTheory.AEStronglyMeasurable.aemeasurable.{u1, u3} α _inst_1 μ γ _inst_9 _inst_3 _inst_10 _inst_11 f₂ hf₂)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u2} δ] [_inst_5 : MeasurableSpace.{u3} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] [_inst_7 : BorelSpace.{u3} β _inst_2 _inst_5] [_inst_8 : TopologicalSpace.SecondCountableTopology.{u3} β _inst_2] [_inst_9 : MeasurableSpace.{u4} γ] [_inst_10 : TopologicalSpace.PseudoMetrizableSpace.{u4} γ _inst_3] [_inst_11 : BorelSpace.{u4} γ _inst_3 _inst_9] [_inst_12 : TopologicalSpace.SecondCountableTopology.{u4} γ _inst_3] [_inst_13 : MeasurableSpace.{u2} δ] [_inst_14 : TopologicalSpace.PseudoMetrizableSpace.{u2} δ _inst_4] [_inst_15 : OpensMeasurableSpace.{u2} δ _inst_4 _inst_13] [_inst_16 : TopologicalSpace.SecondCountableTopology.{u2} δ _inst_4] (g : β -> γ -> δ) (hg : Measurable.{max u4 u3, u2} (Prod.{u3, u4} β γ) δ (Prod.instMeasurableSpace.{u3, u4} β γ _inst_5 _inst_9) _inst_13 (Function.uncurry.{u3, u4, u2} β γ δ g)) (f₁ : α -> β) (f₂ : α -> γ) (hf₁ : MeasureTheory.AEStronglyMeasurable.{u1, u3} α β _inst_2 _inst_1 f₁ μ) (hf₂ : MeasureTheory.AEStronglyMeasurable.{u1, u4} α γ _inst_3 _inst_1 f₂ μ), Eq.{max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α δ _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.comp₂Measurable.{u1, u3, u4, u2} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 _inst_12 _inst_13 _inst_14 _inst_15 _inst_16 g hg (MeasureTheory.AEEqFun.mk.{u1, u3} α _inst_1 μ β _inst_2 f₁ hf₁) (MeasureTheory.AEEqFun.mk.{u1, u4} α _inst_1 μ γ _inst_3 f₂ hf₂)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ δ _inst_4 (fun (a : α) => g (f₁ a) (f₂ a)) (AEMeasurable.aestronglyMeasurable.{u1, u2} α δ _inst_1 μ _inst_4 (Function.comp.{succ u1, succ (max u3 u4), succ u2} α (Prod.{u3, u4} β γ) δ (Function.uncurry.{u3, u4, u2} β γ δ g) (fun (x : α) => Prod.mk.{u3, u4} β γ (f₁ x) (f₂ x))) _inst_13 _inst_14 _inst_15 _inst_16 (Measurable.comp_aemeasurable.{u1, u2, max u3 u4} α δ (Prod.{u3, u4} β γ) _inst_1 _inst_13 μ (Prod.instMeasurableSpace.{u3, u4} β γ _inst_5 _inst_9) (fun (x : α) => Prod.mk.{u3, u4} β γ (f₁ x) (f₂ x)) (Function.uncurry.{u3, u4, u2} β γ δ g) hg (AEMeasurable.prod_mk.{u4, u3, u1} α β γ _inst_1 _inst_5 _inst_9 μ f₁ f₂ (MeasureTheory.AEStronglyMeasurable.aemeasurable.{u1, u3} α _inst_1 μ β _inst_5 _inst_2 _inst_6 _inst_7 f₁ hf₁) (MeasureTheory.AEStronglyMeasurable.aemeasurable.{u1, u4} α _inst_1 μ γ _inst_9 _inst_3 _inst_10 _inst_11 f₂ hf₂)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp₂_measurable_mk_mk MeasureTheory.AEEqFun.comp₂Measurable_mk_mkₓ'. -/
@[simp]
theorem comp₂Measurable_mk_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α → β)
    (f₂ : α → γ) (hf₁ hf₂) :
    comp₂Measurable g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aemeasurable (hf₁.AEMeasurable.prod_mk hf₂.AEMeasurable)).AEStronglyMeasurable :=
  rfl
#align measure_theory.ae_eq_fun.comp₂_measurable_mk_mk MeasureTheory.AEEqFun.comp₂Measurable_mk_mk

/- warning: measure_theory.ae_eq_fun.comp₂_measurable_eq_pair -> MeasureTheory.AEEqFun.comp₂Measurable_eq_pair is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] [_inst_5 : MeasurableSpace.{u2} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_7 : BorelSpace.{u2} β _inst_2 _inst_5] [_inst_8 : TopologicalSpace.SecondCountableTopology.{u2} β _inst_2] [_inst_9 : MeasurableSpace.{u3} γ] [_inst_10 : TopologicalSpace.PseudoMetrizableSpace.{u3} γ _inst_3] [_inst_11 : BorelSpace.{u3} γ _inst_3 _inst_9] [_inst_12 : TopologicalSpace.SecondCountableTopology.{u3} γ _inst_3] [_inst_13 : MeasurableSpace.{u4} δ] [_inst_14 : TopologicalSpace.PseudoMetrizableSpace.{u4} δ _inst_4] [_inst_15 : OpensMeasurableSpace.{u4} δ _inst_4 _inst_13] [_inst_16 : TopologicalSpace.SecondCountableTopology.{u4} δ _inst_4] (g : β -> γ -> δ) (hg : Measurable.{max u2 u3, u4} (Prod.{u2, u3} β γ) δ (Prod.instMeasurableSpace.{u2, u3} β γ _inst_5 _inst_9) _inst_13 (Function.uncurry.{u2, u3, u4} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ), Eq.{succ (max u1 u4)} (MeasureTheory.AEEqFun.{u1, u4} α δ _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.comp₂Measurable.{u1, u2, u3, u4} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 _inst_12 _inst_13 _inst_14 _inst_15 _inst_16 g hg f₁ f₂) (MeasureTheory.AEEqFun.compMeasurable.{u1, max u2 u3, u4} α (Prod.{u2, u3} β γ) δ _inst_1 μ (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) _inst_4 (Prod.instMeasurableSpace.{u2, u3} β γ _inst_5 _inst_9) (TopologicalSpace.pseudoMetrizableSpace_prod.{u2, u3} β γ _inst_2 _inst_3 _inst_6 _inst_10) (Prod.borelSpace.{u2, u3} β γ _inst_2 _inst_5 _inst_7 _inst_3 _inst_9 _inst_11 _inst_8 _inst_12) _inst_13 _inst_14 _inst_15 _inst_16 (Function.uncurry.{u2, u3, u4} β γ δ g) hg (MeasureTheory.AEEqFun.pair.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u2} δ] [_inst_5 : MeasurableSpace.{u3} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] [_inst_7 : BorelSpace.{u3} β _inst_2 _inst_5] [_inst_8 : TopologicalSpace.SecondCountableTopology.{u3} β _inst_2] [_inst_9 : MeasurableSpace.{u4} γ] [_inst_10 : TopologicalSpace.PseudoMetrizableSpace.{u4} γ _inst_3] [_inst_11 : BorelSpace.{u4} γ _inst_3 _inst_9] [_inst_12 : TopologicalSpace.SecondCountableTopology.{u4} γ _inst_3] [_inst_13 : MeasurableSpace.{u2} δ] [_inst_14 : TopologicalSpace.PseudoMetrizableSpace.{u2} δ _inst_4] [_inst_15 : OpensMeasurableSpace.{u2} δ _inst_4 _inst_13] [_inst_16 : TopologicalSpace.SecondCountableTopology.{u2} δ _inst_4] (g : β -> γ -> δ) (hg : Measurable.{max u4 u3, u2} (Prod.{u3, u4} β γ) δ (Prod.instMeasurableSpace.{u3, u4} β γ _inst_5 _inst_9) _inst_13 (Function.uncurry.{u3, u4, u2} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u4} α γ _inst_1 _inst_3 μ), Eq.{max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α δ _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.comp₂Measurable.{u1, u3, u4, u2} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 _inst_12 _inst_13 _inst_14 _inst_15 _inst_16 g hg f₁ f₂) (MeasureTheory.AEEqFun.compMeasurable.{u1, max u3 u4, u2} α (Prod.{u3, u4} β γ) δ _inst_1 μ (instTopologicalSpaceProd.{u3, u4} β γ _inst_2 _inst_3) _inst_4 (Prod.instMeasurableSpace.{u3, u4} β γ _inst_5 _inst_9) (TopologicalSpace.pseudoMetrizableSpace_prod.{u3, u4} β γ _inst_2 _inst_3 _inst_6 _inst_10) (Prod.borelSpace.{u3, u4} β γ _inst_2 _inst_5 _inst_7 _inst_3 _inst_9 _inst_11 _inst_8 _inst_12) _inst_13 _inst_14 _inst_15 _inst_16 (Function.uncurry.{u3, u4, u2} β γ δ g) hg (MeasureTheory.AEEqFun.pair.{u1, u3, u4} α β γ _inst_1 μ _inst_2 _inst_3 f₁ f₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp₂_measurable_eq_pair MeasureTheory.AEEqFun.comp₂Measurable_eq_pairₓ'. -/
theorem comp₂Measurable_eq_pair (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂Measurable g hg f₁ f₂ = compMeasurable _ hg (f₁.pair f₂) :=
  rfl
#align measure_theory.ae_eq_fun.comp₂_measurable_eq_pair MeasureTheory.AEEqFun.comp₂Measurable_eq_pair

/- warning: measure_theory.ae_eq_fun.comp₂_measurable_eq_mk -> MeasureTheory.AEEqFun.comp₂Measurable_eq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] [_inst_5 : MeasurableSpace.{u2} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_7 : BorelSpace.{u2} β _inst_2 _inst_5] [_inst_8 : TopologicalSpace.SecondCountableTopology.{u2} β _inst_2] [_inst_9 : MeasurableSpace.{u3} γ] [_inst_10 : TopologicalSpace.PseudoMetrizableSpace.{u3} γ _inst_3] [_inst_11 : BorelSpace.{u3} γ _inst_3 _inst_9] [_inst_12 : TopologicalSpace.SecondCountableTopology.{u3} γ _inst_3] [_inst_13 : MeasurableSpace.{u4} δ] [_inst_14 : TopologicalSpace.PseudoMetrizableSpace.{u4} δ _inst_4] [_inst_15 : OpensMeasurableSpace.{u4} δ _inst_4 _inst_13] [_inst_16 : TopologicalSpace.SecondCountableTopology.{u4} δ _inst_4] (g : β -> γ -> δ) (hg : Measurable.{max u2 u3, u4} (Prod.{u2, u3} β γ) δ (Prod.instMeasurableSpace.{u2, u3} β γ _inst_5 _inst_9) _inst_13 (Function.uncurry.{u2, u3, u4} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ), Eq.{succ (max u1 u4)} (MeasureTheory.AEEqFun.{u1, u4} α δ _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.comp₂Measurable.{u1, u2, u3, u4} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 _inst_12 _inst_13 _inst_14 _inst_15 _inst_16 g hg f₁ f₂) (MeasureTheory.AEEqFun.mk.{u1, u4} α _inst_1 μ δ _inst_4 (fun (a : α) => g (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f₁ a) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) f₂ a)) (AEMeasurable.aestronglyMeasurable.{u1, u4} α δ _inst_1 μ _inst_4 (Function.comp.{succ u1, succ (max u2 u3), succ u4} α (Prod.{u2, u3} β γ) δ (Function.uncurry.{u2, u3, u4} β γ δ g) (fun (x : α) => Prod.mk.{u2, u3} β γ (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f₁ x) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) f₂ x))) _inst_13 _inst_14 _inst_15 _inst_16 (Measurable.comp_aemeasurable.{u1, u4, max u2 u3} α δ (Prod.{u2, u3} β γ) _inst_1 _inst_13 μ (Prod.instMeasurableSpace.{u2, u3} β γ _inst_5 _inst_9) (fun (x : α) => Prod.mk.{u2, u3} β γ (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f₁ x) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) f₂ x)) (Function.uncurry.{u2, u3, u4} β γ δ g) hg (AEMeasurable.prod_mk.{u1, u2, u3} α β γ _inst_1 _inst_5 _inst_9 μ (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f₁) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) f₂) (MeasureTheory.AEEqFun.aemeasurable.{u1, u2} α β _inst_1 μ _inst_2 _inst_6 _inst_5 _inst_7 f₁) (MeasureTheory.AEEqFun.aemeasurable.{u1, u3} α γ _inst_1 μ _inst_3 _inst_10 _inst_9 _inst_11 f₂)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u2} δ] [_inst_5 : MeasurableSpace.{u3} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] [_inst_7 : BorelSpace.{u3} β _inst_2 _inst_5] [_inst_8 : TopologicalSpace.SecondCountableTopology.{u3} β _inst_2] [_inst_9 : MeasurableSpace.{u4} γ] [_inst_10 : TopologicalSpace.PseudoMetrizableSpace.{u4} γ _inst_3] [_inst_11 : BorelSpace.{u4} γ _inst_3 _inst_9] [_inst_12 : TopologicalSpace.SecondCountableTopology.{u4} γ _inst_3] [_inst_13 : MeasurableSpace.{u2} δ] [_inst_14 : TopologicalSpace.PseudoMetrizableSpace.{u2} δ _inst_4] [_inst_15 : OpensMeasurableSpace.{u2} δ _inst_4 _inst_13] [_inst_16 : TopologicalSpace.SecondCountableTopology.{u2} δ _inst_4] (g : β -> γ -> δ) (hg : Measurable.{max u4 u3, u2} (Prod.{u3, u4} β γ) δ (Prod.instMeasurableSpace.{u3, u4} β γ _inst_5 _inst_9) _inst_13 (Function.uncurry.{u3, u4, u2} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u4} α γ _inst_1 _inst_3 μ), Eq.{max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α δ _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.comp₂Measurable.{u1, u3, u4, u2} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 _inst_12 _inst_13 _inst_14 _inst_15 _inst_16 g hg f₁ f₂) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ δ _inst_4 (fun (a : α) => g (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f₁ a) (MeasureTheory.AEEqFun.cast.{u1, u4} α γ _inst_1 μ _inst_3 f₂ a)) (AEMeasurable.aestronglyMeasurable.{u1, u2} α δ _inst_1 μ _inst_4 (Function.comp.{succ u1, succ (max u3 u4), succ u2} α (Prod.{u3, u4} β γ) δ (Function.uncurry.{u3, u4, u2} β γ δ g) (fun (x : α) => Prod.mk.{u3, u4} β γ (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f₁ x) (MeasureTheory.AEEqFun.cast.{u1, u4} α γ _inst_1 μ _inst_3 f₂ x))) _inst_13 _inst_14 _inst_15 _inst_16 (Measurable.comp_aemeasurable.{u1, u2, max u3 u4} α δ (Prod.{u3, u4} β γ) _inst_1 _inst_13 μ (Prod.instMeasurableSpace.{u3, u4} β γ _inst_5 _inst_9) (fun (x : α) => Prod.mk.{u3, u4} β γ (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f₁ x) (MeasureTheory.AEEqFun.cast.{u1, u4} α γ _inst_1 μ _inst_3 f₂ x)) (Function.uncurry.{u3, u4, u2} β γ δ g) hg (AEMeasurable.prod_mk.{u4, u3, u1} α β γ _inst_1 _inst_5 _inst_9 μ (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f₁) (MeasureTheory.AEEqFun.cast.{u1, u4} α γ _inst_1 μ _inst_3 f₂) (MeasureTheory.AEEqFun.aemeasurable.{u1, u3} α β _inst_1 μ _inst_2 _inst_6 _inst_5 _inst_7 f₁) (MeasureTheory.AEEqFun.aemeasurable.{u1, u4} α γ _inst_1 μ _inst_3 _inst_10 _inst_9 _inst_11 f₂)))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp₂_measurable_eq_mk MeasureTheory.AEEqFun.comp₂Measurable_eq_mkₓ'. -/
theorem comp₂Measurable_eq_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) :
    comp₂Measurable g hg f₁ f₂ =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aemeasurable (f₁.AEMeasurable.prod_mk f₂.AEMeasurable)).AEStronglyMeasurable :=
  by rw [comp₂_measurable_eq_pair, pair_eq_mk, comp_measurable_mk] <;> rfl
#align measure_theory.ae_eq_fun.comp₂_measurable_eq_mk MeasureTheory.AEEqFun.comp₂Measurable_eq_mk

/- warning: measure_theory.ae_eq_fun.coe_fn_comp₂_measurable -> MeasureTheory.AEEqFun.coeFn_comp₂Measurable is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] [_inst_5 : MeasurableSpace.{u2} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_7 : BorelSpace.{u2} β _inst_2 _inst_5] [_inst_8 : TopologicalSpace.SecondCountableTopology.{u2} β _inst_2] [_inst_9 : MeasurableSpace.{u3} γ] [_inst_10 : TopologicalSpace.PseudoMetrizableSpace.{u3} γ _inst_3] [_inst_11 : BorelSpace.{u3} γ _inst_3 _inst_9] [_inst_12 : TopologicalSpace.SecondCountableTopology.{u3} γ _inst_3] [_inst_13 : MeasurableSpace.{u4} δ] [_inst_14 : TopologicalSpace.PseudoMetrizableSpace.{u4} δ _inst_4] [_inst_15 : OpensMeasurableSpace.{u4} δ _inst_4 _inst_13] [_inst_16 : TopologicalSpace.SecondCountableTopology.{u4} δ _inst_4] (g : β -> γ -> δ) (hg : Measurable.{max u2 u3, u4} (Prod.{u2, u3} β γ) δ (Prod.instMeasurableSpace.{u2, u3} β γ _inst_5 _inst_9) _inst_13 (Function.uncurry.{u2, u3, u4} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u1, u4} α δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u4), max (succ u1) (succ u4)} (MeasureTheory.AEEqFun.{u1, u4} α δ _inst_1 _inst_4 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u4} α δ _inst_1 _inst_4 μ) => α -> δ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u4} α δ _inst_1 μ _inst_4) (MeasureTheory.AEEqFun.comp₂Measurable.{u1, u2, u3, u4} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 _inst_12 _inst_13 _inst_14 _inst_15 _inst_16 g hg f₁ f₂)) (fun (a : α) => g (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f₁ a) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) f₂ a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u2} δ] [_inst_5 : MeasurableSpace.{u3} β] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] [_inst_7 : BorelSpace.{u3} β _inst_2 _inst_5] [_inst_8 : TopologicalSpace.SecondCountableTopology.{u3} β _inst_2] [_inst_9 : MeasurableSpace.{u4} γ] [_inst_10 : TopologicalSpace.PseudoMetrizableSpace.{u4} γ _inst_3] [_inst_11 : BorelSpace.{u4} γ _inst_3 _inst_9] [_inst_12 : TopologicalSpace.SecondCountableTopology.{u4} γ _inst_3] [_inst_13 : MeasurableSpace.{u2} δ] [_inst_14 : TopologicalSpace.PseudoMetrizableSpace.{u2} δ _inst_4] [_inst_15 : OpensMeasurableSpace.{u2} δ _inst_4 _inst_13] [_inst_16 : TopologicalSpace.SecondCountableTopology.{u2} δ _inst_4] (g : β -> γ -> δ) (hg : Measurable.{max u4 u3, u2} (Prod.{u3, u4} β γ) δ (Prod.instMeasurableSpace.{u3, u4} β γ _inst_5 _inst_9) _inst_13 (Function.uncurry.{u3, u4, u2} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u4} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u1, u2} α δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u1, u2} α δ _inst_1 μ _inst_4 (MeasureTheory.AEEqFun.comp₂Measurable.{u1, u3, u4, u2} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 _inst_11 _inst_12 _inst_13 _inst_14 _inst_15 _inst_16 g hg f₁ f₂)) (fun (a : α) => g (MeasureTheory.AEEqFun.cast.{u1, u3} α β _inst_1 μ _inst_2 f₁ a) (MeasureTheory.AEEqFun.cast.{u1, u4} α γ _inst_1 μ _inst_3 f₂ a))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_comp₂_measurable MeasureTheory.AEEqFun.coeFn_comp₂Measurableₓ'. -/
theorem coeFn_comp₂Measurable (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂Measurable g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) :=
  by
  rw [comp₂_measurable_eq_mk]
  apply coe_fn_mk
#align measure_theory.ae_eq_fun.coe_fn_comp₂_measurable MeasureTheory.AEEqFun.coeFn_comp₂Measurable

end

#print MeasureTheory.AEEqFun.toGerm /-
/-- Interpret `f : α →ₘ[μ] β` as a germ at `μ.ae` forgetting that `f` is almost everywhere
    strongly measurable. -/
def toGerm (f : α →ₘ[μ] β) : Germ μ.ae β :=
  Quotient.liftOn' f (fun f => ((f : α → β) : Germ μ.ae β)) fun f g H => Germ.coe_eq.2 H
#align measure_theory.ae_eq_fun.to_germ MeasureTheory.AEEqFun.toGerm
-/

/- warning: measure_theory.ae_eq_fun.mk_to_germ -> MeasureTheory.AEEqFun.mk_toGerm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) β) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α β _inst_1 μ _inst_2 (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf)) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) β) (Filter.Germ.hasCoeT.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)))) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] (f : α -> β) (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α β _inst_2 _inst_1 f μ), Eq.{max (succ u2) (succ u1)} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) β) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α β _inst_1 μ _inst_2 (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ β _inst_2 f hf)) (Filter.Germ.ofFun.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) f)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.mk_to_germ MeasureTheory.AEEqFun.mk_toGermₓ'. -/
@[simp]
theorem mk_toGerm (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β).toGerm = f :=
  rfl
#align measure_theory.ae_eq_fun.mk_to_germ MeasureTheory.AEEqFun.mk_toGerm

/- warning: measure_theory.ae_eq_fun.to_germ_eq -> MeasureTheory.AEEqFun.toGerm_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) β) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α β _inst_1 μ _inst_2 f) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) ((fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) f) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} ((fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) f) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} ((fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) f) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) β) (Filter.Germ.hasCoeT.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ)))) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ), Eq.{max (succ u2) (succ u1)} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) β) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α β _inst_1 μ _inst_2 f) (Filter.Germ.ofFun.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 f))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.to_germ_eq MeasureTheory.AEEqFun.toGerm_eqₓ'. -/
theorem toGerm_eq (f : α →ₘ[μ] β) : f.toGerm = (f : α → β) := by rw [← mk_to_germ, mk_coe_fn]
#align measure_theory.ae_eq_fun.to_germ_eq MeasureTheory.AEEqFun.toGerm_eq

/- warning: measure_theory.ae_eq_fun.to_germ_injective -> MeasureTheory.AEEqFun.toGerm_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β], Function.Injective.{succ (max u1 u2), succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) β) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α β _inst_1 μ _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) β) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α β _inst_1 μ _inst_2)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.to_germ_injective MeasureTheory.AEEqFun.toGerm_injectiveₓ'. -/
theorem toGerm_injective : Injective (toGerm : (α →ₘ[μ] β) → Germ μ.ae β) := fun f g H =>
  ext <| Germ.coe_eq.1 <| by rwa [← to_germ_eq, ← to_germ_eq]
#align measure_theory.ae_eq_fun.to_germ_injective MeasureTheory.AEEqFun.toGerm_injective

/- warning: measure_theory.ae_eq_fun.comp_to_germ -> MeasureTheory.AEEqFun.comp_toGerm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (g : β -> γ) (hg : Continuous.{u2, u3} β γ _inst_2 _inst_3 g) (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), Eq.{succ (max u1 u3)} (Filter.Germ.{u1, u3} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u1, u3} α γ _inst_1 μ _inst_3 (MeasureTheory.AEEqFun.comp.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 g hg f)) (Filter.Germ.map.{u1, u2, u3} α β γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) g (MeasureTheory.AEEqFun.toGerm.{u1, u2} α β _inst_1 μ _inst_2 f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] (g : β -> γ) (hg : Continuous.{u3, u2} β γ _inst_2 _inst_3 g) (f : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 (MeasureTheory.AEEqFun.comp.{u1, u3, u2} α β γ _inst_1 μ _inst_2 _inst_3 g hg f)) (Filter.Germ.map.{u1, u3, u2} α β γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) g (MeasureTheory.AEEqFun.toGerm.{u1, u3} α β _inst_1 μ _inst_2 f))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp_to_germ MeasureTheory.AEEqFun.comp_toGermₓ'. -/
theorem comp_toGerm (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) :
    (comp g hg f).toGerm = f.toGerm.map g :=
  induction_on f fun f hf => by simp
#align measure_theory.ae_eq_fun.comp_to_germ MeasureTheory.AEEqFun.comp_toGerm

/- warning: measure_theory.ae_eq_fun.comp_measurable_to_germ -> MeasureTheory.AEEqFun.compMeasurable_toGerm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_5 : MeasurableSpace.{u2} β] [_inst_6 : BorelSpace.{u2} β _inst_2 _inst_5] [_inst_7 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_8 : TopologicalSpace.PseudoMetrizableSpace.{u3} γ _inst_3] [_inst_9 : TopologicalSpace.SecondCountableTopology.{u3} γ _inst_3] [_inst_10 : MeasurableSpace.{u3} γ] [_inst_11 : OpensMeasurableSpace.{u3} γ _inst_3 _inst_10] (g : β -> γ) (hg : Measurable.{u2, u3} β γ _inst_5 _inst_10 g) (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), Eq.{succ (max u1 u3)} (Filter.Germ.{u1, u3} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u1, u3} α γ _inst_1 μ _inst_3 (MeasureTheory.AEEqFun.compMeasurable.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 _inst_5 _inst_7 _inst_6 _inst_10 _inst_8 _inst_11 _inst_9 g hg f)) (Filter.Germ.map.{u1, u2, u3} α β γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) g (MeasureTheory.AEEqFun.toGerm.{u1, u2} α β _inst_1 μ _inst_2 f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : MeasurableSpace.{u3} β] [_inst_6 : BorelSpace.{u3} β _inst_2 _inst_5] [_inst_7 : TopologicalSpace.PseudoMetrizableSpace.{u3} β _inst_2] [_inst_8 : TopologicalSpace.PseudoMetrizableSpace.{u2} γ _inst_3] [_inst_9 : TopologicalSpace.SecondCountableTopology.{u2} γ _inst_3] [_inst_10 : MeasurableSpace.{u2} γ] [_inst_11 : OpensMeasurableSpace.{u2} γ _inst_3 _inst_10] (g : β -> γ) (hg : Measurable.{u3, u2} β γ _inst_5 _inst_10 g) (f : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 (MeasureTheory.AEEqFun.compMeasurable.{u1, u3, u2} α β γ _inst_1 μ _inst_2 _inst_3 _inst_5 _inst_7 _inst_6 _inst_10 _inst_8 _inst_11 _inst_9 g hg f)) (Filter.Germ.map.{u1, u3, u2} α β γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) g (MeasureTheory.AEEqFun.toGerm.{u1, u3} α β _inst_1 μ _inst_2 f))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp_measurable_to_germ MeasureTheory.AEEqFun.compMeasurable_toGermₓ'. -/
theorem compMeasurable_toGerm [MeasurableSpace β] [BorelSpace β] [PseudoMetrizableSpace β]
    [PseudoMetrizableSpace γ] [SecondCountableTopology γ] [MeasurableSpace γ]
    [OpensMeasurableSpace γ] (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    (compMeasurable g hg f).toGerm = f.toGerm.map g :=
  induction_on f fun f hf => by simp
#align measure_theory.ae_eq_fun.comp_measurable_to_germ MeasureTheory.AEEqFun.compMeasurable_toGerm

/- warning: measure_theory.ae_eq_fun.comp₂_to_germ -> MeasureTheory.AEEqFun.comp₂_toGerm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (g : β -> γ -> δ) (hg : Continuous.{max u2 u3, u4} (Prod.{u2, u3} β γ) δ (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u2, u3, u4} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ), Eq.{succ (max u1 u4)} (Filter.Germ.{u1, u4} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) δ) (MeasureTheory.AEEqFun.toGerm.{u1, u4} α δ _inst_1 μ _inst_4 (MeasureTheory.AEEqFun.comp₂.{u1, u2, u3, u4} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 g hg f₁ f₂)) (Filter.Germ.map₂.{u1, u2, u3, u4} α β γ δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) g (MeasureTheory.AEEqFun.toGerm.{u1, u2} α β _inst_1 μ _inst_2 f₁) (MeasureTheory.AEEqFun.toGerm.{u1, u3} α γ _inst_1 μ _inst_3 f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u4} γ] [_inst_4 : TopologicalSpace.{u2} δ] (g : β -> γ -> δ) (hg : Continuous.{max u4 u3, u2} (Prod.{u3, u4} β γ) δ (instTopologicalSpaceProd.{u3, u4} β γ _inst_2 _inst_3) _inst_4 (Function.uncurry.{u3, u4, u2} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u3} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u4} α γ _inst_1 _inst_3 μ), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) δ) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α δ _inst_1 μ _inst_4 (MeasureTheory.AEEqFun.comp₂.{u1, u3, u4, u2} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 g hg f₁ f₂)) (Filter.Germ.map₂.{u1, u3, u4, u2} α β γ δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) g (MeasureTheory.AEEqFun.toGerm.{u1, u3} α β _inst_1 μ _inst_2 f₁) (MeasureTheory.AEEqFun.toGerm.{u1, u4} α γ _inst_1 μ _inst_3 f₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp₂_to_germ MeasureTheory.AEEqFun.comp₂_toGermₓ'. -/
theorem comp₂_toGerm (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : (comp₂ g hg f₁ f₂).toGerm = f₁.toGerm.zipWith g f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ hf₁ f₂ hf₂ => by simp
#align measure_theory.ae_eq_fun.comp₂_to_germ MeasureTheory.AEEqFun.comp₂_toGerm

/- warning: measure_theory.ae_eq_fun.comp₂_measurable_to_germ -> MeasureTheory.AEEqFun.comp₂Measurable_toGerm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_2] [_inst_6 : TopologicalSpace.SecondCountableTopology.{u2} β _inst_2] [_inst_7 : MeasurableSpace.{u2} β] [_inst_8 : BorelSpace.{u2} β _inst_2 _inst_7] [_inst_9 : TopologicalSpace.PseudoMetrizableSpace.{u3} γ _inst_3] [_inst_10 : TopologicalSpace.SecondCountableTopology.{u3} γ _inst_3] [_inst_11 : MeasurableSpace.{u3} γ] [_inst_12 : BorelSpace.{u3} γ _inst_3 _inst_11] [_inst_13 : TopologicalSpace.PseudoMetrizableSpace.{u4} δ _inst_4] [_inst_14 : TopologicalSpace.SecondCountableTopology.{u4} δ _inst_4] [_inst_15 : MeasurableSpace.{u4} δ] [_inst_16 : OpensMeasurableSpace.{u4} δ _inst_4 _inst_15] (g : β -> γ -> δ) (hg : Measurable.{max u2 u3, u4} (Prod.{u2, u3} β γ) δ (Prod.instMeasurableSpace.{u2, u3} β γ _inst_7 _inst_11) _inst_15 (Function.uncurry.{u2, u3, u4} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ), Eq.{succ (max u1 u4)} (Filter.Germ.{u1, u4} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) δ) (MeasureTheory.AEEqFun.toGerm.{u1, u4} α δ _inst_1 μ _inst_4 (MeasureTheory.AEEqFun.comp₂Measurable.{u1, u2, u3, u4} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 _inst_7 _inst_5 _inst_8 _inst_6 _inst_11 _inst_9 _inst_12 _inst_10 _inst_15 _inst_13 _inst_16 _inst_14 g hg f₁ f₂)) (Filter.Germ.map₂.{u1, u2, u3, u4} α β γ δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) g (MeasureTheory.AEEqFun.toGerm.{u1, u2} α β _inst_1 μ _inst_2 f₁) (MeasureTheory.AEEqFun.toGerm.{u1, u3} α γ _inst_1 μ _inst_3 f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u4}} {γ : Type.{u3}} {δ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u4} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u2} δ] [_inst_5 : TopologicalSpace.PseudoMetrizableSpace.{u4} β _inst_2] [_inst_6 : TopologicalSpace.SecondCountableTopology.{u4} β _inst_2] [_inst_7 : MeasurableSpace.{u4} β] [_inst_8 : BorelSpace.{u4} β _inst_2 _inst_7] [_inst_9 : TopologicalSpace.PseudoMetrizableSpace.{u3} γ _inst_3] [_inst_10 : TopologicalSpace.SecondCountableTopology.{u3} γ _inst_3] [_inst_11 : MeasurableSpace.{u3} γ] [_inst_12 : BorelSpace.{u3} γ _inst_3 _inst_11] [_inst_13 : TopologicalSpace.PseudoMetrizableSpace.{u2} δ _inst_4] [_inst_14 : TopologicalSpace.SecondCountableTopology.{u2} δ _inst_4] [_inst_15 : MeasurableSpace.{u2} δ] [_inst_16 : OpensMeasurableSpace.{u2} δ _inst_4 _inst_15] (g : β -> γ -> δ) (hg : Measurable.{max u3 u4, u2} (Prod.{u4, u3} β γ) δ (Prod.instMeasurableSpace.{u4, u3} β γ _inst_7 _inst_11) _inst_15 (Function.uncurry.{u4, u3, u2} β γ δ g)) (f₁ : MeasureTheory.AEEqFun.{u1, u4} α β _inst_1 _inst_2 μ) (f₂ : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) δ) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α δ _inst_1 μ _inst_4 (MeasureTheory.AEEqFun.comp₂Measurable.{u1, u4, u3, u2} α β γ δ _inst_1 μ _inst_2 _inst_3 _inst_4 _inst_7 _inst_5 _inst_8 _inst_6 _inst_11 _inst_9 _inst_12 _inst_10 _inst_15 _inst_13 _inst_16 _inst_14 g hg f₁ f₂)) (Filter.Germ.map₂.{u1, u4, u3, u2} α β γ δ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) g (MeasureTheory.AEEqFun.toGerm.{u1, u4} α β _inst_1 μ _inst_2 f₁) (MeasureTheory.AEEqFun.toGerm.{u1, u3} α γ _inst_1 μ _inst_3 f₂))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.comp₂_measurable_to_germ MeasureTheory.AEEqFun.comp₂Measurable_toGermₓ'. -/
theorem comp₂Measurable_toGerm [PseudoMetrizableSpace β] [SecondCountableTopology β]
    [MeasurableSpace β] [BorelSpace β] [PseudoMetrizableSpace γ] [SecondCountableTopology γ]
    [MeasurableSpace γ] [BorelSpace γ] [PseudoMetrizableSpace δ] [SecondCountableTopology δ]
    [MeasurableSpace δ] [OpensMeasurableSpace δ] (g : β → γ → δ) (hg : Measurable (uncurry g))
    (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    (comp₂Measurable g hg f₁ f₂).toGerm = f₁.toGerm.zipWith g f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ hf₁ f₂ hf₂ => by simp
#align measure_theory.ae_eq_fun.comp₂_measurable_to_germ MeasureTheory.AEEqFun.comp₂Measurable_toGerm

#print MeasureTheory.AEEqFun.LiftPred /-
/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
    for almost all `a` -/
def LiftPred (p : β → Prop) (f : α →ₘ[μ] β) : Prop :=
  f.toGerm.LiftPred p
#align measure_theory.ae_eq_fun.lift_pred MeasureTheory.AEEqFun.LiftPred
-/

#print MeasureTheory.AEEqFun.LiftRel /-
/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
    `(f a, g a)` for almost all `a` -/
def LiftRel (r : β → γ → Prop) (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : Prop :=
  f.toGerm.LiftRel r g.toGerm
#align measure_theory.ae_eq_fun.lift_rel MeasureTheory.AEEqFun.LiftRel
-/

/- warning: measure_theory.ae_eq_fun.lift_rel_mk_mk -> MeasureTheory.AEEqFun.liftRel_mk_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {r : β -> γ -> Prop} {f : α -> β} {g : α -> γ} {hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ} {hg : MeasureTheory.AEStronglyMeasurable.{u1, u3} α γ _inst_3 _inst_1 g μ}, Iff (MeasureTheory.AEEqFun.LiftRel.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 r (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf) (MeasureTheory.AEEqFun.mk.{u1, u3} α _inst_1 μ γ _inst_3 g hg)) (Filter.Eventually.{u1} α (fun (a : α) => r (f a) (g a)) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] {μ : MeasureTheory.Measure.{u3} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {r : β -> γ -> Prop} {f : α -> β} {g : α -> γ} {hf : MeasureTheory.AEStronglyMeasurable.{u3, u2} α β _inst_2 _inst_1 f μ} {hg : MeasureTheory.AEStronglyMeasurable.{u3, u1} α γ _inst_3 _inst_1 g μ}, Iff (MeasureTheory.AEEqFun.LiftRel.{u3, u2, u1} α β γ _inst_1 μ _inst_2 _inst_3 r (MeasureTheory.AEEqFun.mk.{u3, u2} α _inst_1 μ β _inst_2 f hf) (MeasureTheory.AEEqFun.mk.{u3, u1} α _inst_1 μ γ _inst_3 g hg)) (Filter.Eventually.{u3} α (fun (a : α) => r (f a) (g a)) (MeasureTheory.Measure.ae.{u3} α _inst_1 μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.lift_rel_mk_mk MeasureTheory.AEEqFun.liftRel_mk_mkₓ'. -/
theorem liftRel_mk_mk {r : β → γ → Prop} {f : α → β} {g : α → γ} {hf hg} :
    LiftRel r (mk f hf : α →ₘ[μ] β) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
  Iff.rfl
#align measure_theory.ae_eq_fun.lift_rel_mk_mk MeasureTheory.AEEqFun.liftRel_mk_mk

/- warning: measure_theory.ae_eq_fun.lift_rel_iff_coe_fn -> MeasureTheory.AEEqFun.liftRel_iff_coeFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] {r : β -> γ -> Prop} {f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ} {g : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ}, Iff (MeasureTheory.AEEqFun.LiftRel.{u1, u2, u3} α β γ _inst_1 μ _inst_2 _inst_3 r f g) (Filter.Eventually.{u1} α (fun (a : α) => r (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f a) (coeFn.{succ (max u1 u3), max (succ u1) (succ u3)} (MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u3} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u3} α γ _inst_1 μ _inst_3) g a)) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u3} α] {μ : MeasureTheory.Measure.{u3} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] {r : β -> γ -> Prop} {f : MeasureTheory.AEEqFun.{u3, u2} α β _inst_1 _inst_2 μ} {g : MeasureTheory.AEEqFun.{u3, u1} α γ _inst_1 _inst_3 μ}, Iff (MeasureTheory.AEEqFun.LiftRel.{u3, u2, u1} α β γ _inst_1 μ _inst_2 _inst_3 r f g) (Filter.Eventually.{u3} α (fun (a : α) => r (MeasureTheory.AEEqFun.cast.{u3, u2} α β _inst_1 μ _inst_2 f a) (MeasureTheory.AEEqFun.cast.{u3, u1} α γ _inst_1 μ _inst_3 g a)) (MeasureTheory.Measure.ae.{u3} α _inst_1 μ))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.lift_rel_iff_coe_fn MeasureTheory.AEEqFun.liftRel_iff_coeFnₓ'. -/
theorem liftRel_iff_coeFn {r : β → γ → Prop} {f : α →ₘ[μ] β} {g : α →ₘ[μ] γ} :
    LiftRel r f g ↔ ∀ᵐ a ∂μ, r (f a) (g a) := by rw [← lift_rel_mk_mk, mk_coe_fn, mk_coe_fn]
#align measure_theory.ae_eq_fun.lift_rel_iff_coe_fn MeasureTheory.AEEqFun.liftRel_iff_coeFn

section Order

instance [Preorder β] : Preorder (α →ₘ[μ] β) :=
  Preorder.lift toGerm

/- warning: measure_theory.ae_eq_fun.mk_le_mk -> MeasureTheory.AEEqFun.mk_le_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : Preorder.{u2} β] {f : α -> β} {g : α -> β} (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ) (hg : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 g μ), Iff (LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toHasLe.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 _inst_5)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 g hg)) (Filter.EventuallyLE.{u1, u2} α β (Preorder.toHasLe.{u2} β _inst_5) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f g)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : Preorder.{u2} β] {f : α -> β} {g : α -> β} (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 f μ) (hg : MeasureTheory.AEStronglyMeasurable.{u1, u2} α β _inst_2 _inst_1 g μ), Iff (LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toLE.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 _inst_5)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 f hf) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 g hg)) (Filter.EventuallyLE.{u1, u2} α β (Preorder.toLE.{u2} β _inst_5) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) f g)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.mk_le_mk MeasureTheory.AEEqFun.mk_le_mkₓ'. -/
@[simp]
theorem mk_le_mk [Preorder β] {f g : α → β} (hf hg) : (mk f hf : α →ₘ[μ] β) ≤ mk g hg ↔ f ≤ᵐ[μ] g :=
  Iff.rfl
#align measure_theory.ae_eq_fun.mk_le_mk MeasureTheory.AEEqFun.mk_le_mk

/- warning: measure_theory.ae_eq_fun.coe_fn_le -> MeasureTheory.AEEqFun.coeFn_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : Preorder.{u2} β] {f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ} {g : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ}, Iff (Filter.EventuallyLE.{u1, u2} α β (Preorder.toHasLe.{u2} β _inst_5) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) g)) (LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toHasLe.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 _inst_5)) f g)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : Preorder.{u2} β] {f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ} {g : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ}, Iff (Filter.EventuallyLE.{u1, u2} α β (Preorder.toLE.{u2} β _inst_5) (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u1, u2} α β _inst_1 μ _inst_2 f) (MeasureTheory.AEEqFun.cast.{u1, u2} α β _inst_1 μ _inst_2 g)) (LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toLE.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 _inst_5)) f g)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_le MeasureTheory.AEEqFun.coeFn_leₓ'. -/
@[simp, norm_cast]
theorem coeFn_le [Preorder β] {f g : α →ₘ[μ] β} : (f : α → β) ≤ᵐ[μ] g ↔ f ≤ g :=
  liftRel_iff_coeFn.symm
#align measure_theory.ae_eq_fun.coe_fn_le MeasureTheory.AEEqFun.coeFn_le

instance [PartialOrder β] : PartialOrder (α →ₘ[μ] β) :=
  PartialOrder.lift toGerm toGerm_injective

section Lattice

section Sup

variable [SemilatticeSup β] [ContinuousSup β]

instance : Sup (α →ₘ[μ] β) where sup f g := AEEqFun.comp₂ (· ⊔ ·) continuous_sup f g

/- warning: measure_theory.ae_eq_fun.coe_fn_sup -> MeasureTheory.AEEqFun.coeFn_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : SemilatticeSup.{u2} β] [_inst_6 : ContinuousSup.{u2} β _inst_2 (SemilatticeSup.toHasSup.{u2} β _inst_5)] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) (Sup.sup.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instSup.{u1, u2} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g)) (fun (x : α) => Sup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β _inst_5) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f x) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) g x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : SemilatticeSup.{u1} β] [_inst_6 : ContinuousSup.{u1} β _inst_2 (SemilatticeSup.toSup.{u1} β _inst_5)] (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ), Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 (Sup.sup.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instSup.{u2, u1} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g)) (fun (x : α) => Sup.sup.{u1} β (SemilatticeSup.toSup.{u1} β _inst_5) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 f x) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 g x))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_sup MeasureTheory.AEEqFun.coeFn_supₓ'. -/
theorem coeFn_sup (f g : α →ₘ[μ] β) : ⇑(f ⊔ g) =ᵐ[μ] fun x => f x ⊔ g x :=
  coeFn_comp₂ _ _ _ _
#align measure_theory.ae_eq_fun.coe_fn_sup MeasureTheory.AEEqFun.coeFn_sup

/- warning: measure_theory.ae_eq_fun.le_sup_left -> MeasureTheory.AEEqFun.le_sup_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : SemilatticeSup.{u2} β] [_inst_6 : ContinuousSup.{u2} β _inst_2 (SemilatticeSup.toHasSup.{u2} β _inst_5)] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toHasLe.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_5)))) f (Sup.sup.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instSup.{u1, u2} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : SemilatticeSup.{u1} β] [_inst_6 : ContinuousSup.{u1} β _inst_2 (SemilatticeSup.toSup.{u1} β _inst_5)] (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ), LE.le.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (Preorder.toLE.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u2, u1} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5)))) f (Sup.sup.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instSup.{u2, u1} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.le_sup_left MeasureTheory.AEEqFun.le_sup_leftₓ'. -/
protected theorem le_sup_left (f g : α →ₘ[μ] β) : f ≤ f ⊔ g :=
  by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_sup f g]with _ ha
  rw [ha]
  exact le_sup_left
#align measure_theory.ae_eq_fun.le_sup_left MeasureTheory.AEEqFun.le_sup_left

/- warning: measure_theory.ae_eq_fun.le_sup_right -> MeasureTheory.AEEqFun.le_sup_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : SemilatticeSup.{u2} β] [_inst_6 : ContinuousSup.{u2} β _inst_2 (SemilatticeSup.toHasSup.{u2} β _inst_5)] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toHasLe.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_5)))) g (Sup.sup.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instSup.{u1, u2} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : SemilatticeSup.{u1} β] [_inst_6 : ContinuousSup.{u1} β _inst_2 (SemilatticeSup.toSup.{u1} β _inst_5)] (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ), LE.le.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (Preorder.toLE.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u2, u1} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5)))) g (Sup.sup.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instSup.{u2, u1} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.le_sup_right MeasureTheory.AEEqFun.le_sup_rightₓ'. -/
protected theorem le_sup_right (f g : α →ₘ[μ] β) : g ≤ f ⊔ g :=
  by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_sup f g]with _ ha
  rw [ha]
  exact le_sup_right
#align measure_theory.ae_eq_fun.le_sup_right MeasureTheory.AEEqFun.le_sup_right

/- warning: measure_theory.ae_eq_fun.sup_le -> MeasureTheory.AEEqFun.sup_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : SemilatticeSup.{u2} β] [_inst_6 : ContinuousSup.{u2} β _inst_2 (SemilatticeSup.toHasSup.{u2} β _inst_5)] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (f' : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), (LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toHasLe.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_5)))) f f') -> (LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toHasLe.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_5)))) g f') -> (LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toHasLe.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeSup.toPartialOrder.{u2} β _inst_5)))) (Sup.sup.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instSup.{u1, u2} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g) f')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : SemilatticeSup.{u1} β] [_inst_6 : ContinuousSup.{u1} β _inst_2 (SemilatticeSup.toSup.{u1} β _inst_5)] (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (f' : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ), (LE.le.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (Preorder.toLE.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u2, u1} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5)))) f f') -> (LE.le.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (Preorder.toLE.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u2, u1} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5)))) g f') -> (LE.le.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (Preorder.toLE.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u2, u1} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u1} β (SemilatticeSup.toPartialOrder.{u1} β _inst_5)))) (Sup.sup.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instSup.{u2, u1} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g) f')
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.sup_le MeasureTheory.AEEqFun.sup_leₓ'. -/
protected theorem sup_le (f g f' : α →ₘ[μ] β) (hf : f ≤ f') (hg : g ≤ f') : f ⊔ g ≤ f' :=
  by
  rw [← coe_fn_le] at hf hg⊢
  filter_upwards [hf, hg, coe_fn_sup f g]with _ haf hag ha_sup
  rw [ha_sup]
  exact sup_le haf hag
#align measure_theory.ae_eq_fun.sup_le MeasureTheory.AEEqFun.sup_le

end Sup

section Inf

variable [SemilatticeInf β] [ContinuousInf β]

instance : Inf (α →ₘ[μ] β) where inf f g := AEEqFun.comp₂ (· ⊓ ·) continuous_inf f g

/- warning: measure_theory.ae_eq_fun.coe_fn_inf -> MeasureTheory.AEEqFun.coeFn_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : SemilatticeInf.{u2} β] [_inst_6 : ContinuousInf.{u2} β _inst_2 (SemilatticeInf.toHasInf.{u2} β _inst_5)] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) (Inf.inf.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instInf.{u1, u2} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g)) (fun (x : α) => Inf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β _inst_5) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) f x) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) g x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : SemilatticeInf.{u1} β] [_inst_6 : ContinuousInf.{u1} β _inst_2 (SemilatticeInf.toInf.{u1} β _inst_5)] (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ), Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 (Inf.inf.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instInf.{u2, u1} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g)) (fun (x : α) => Inf.inf.{u1} β (SemilatticeInf.toInf.{u1} β _inst_5) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 f x) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 g x))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_inf MeasureTheory.AEEqFun.coeFn_infₓ'. -/
theorem coeFn_inf (f g : α →ₘ[μ] β) : ⇑(f ⊓ g) =ᵐ[μ] fun x => f x ⊓ g x :=
  coeFn_comp₂ _ _ _ _
#align measure_theory.ae_eq_fun.coe_fn_inf MeasureTheory.AEEqFun.coeFn_inf

/- warning: measure_theory.ae_eq_fun.inf_le_left -> MeasureTheory.AEEqFun.inf_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : SemilatticeInf.{u2} β] [_inst_6 : ContinuousInf.{u2} β _inst_2 (SemilatticeInf.toHasInf.{u2} β _inst_5)] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toHasLe.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_5)))) (Inf.inf.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instInf.{u1, u2} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : SemilatticeInf.{u1} β] [_inst_6 : ContinuousInf.{u1} β _inst_2 (SemilatticeInf.toInf.{u1} β _inst_5)] (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ), LE.le.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (Preorder.toLE.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u2, u1} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_5)))) (Inf.inf.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instInf.{u2, u1} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g) f
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.inf_le_left MeasureTheory.AEEqFun.inf_le_leftₓ'. -/
protected theorem inf_le_left (f g : α →ₘ[μ] β) : f ⊓ g ≤ f :=
  by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_inf f g]with _ ha
  rw [ha]
  exact inf_le_left
#align measure_theory.ae_eq_fun.inf_le_left MeasureTheory.AEEqFun.inf_le_left

/- warning: measure_theory.ae_eq_fun.inf_le_right -> MeasureTheory.AEEqFun.inf_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : SemilatticeInf.{u2} β] [_inst_6 : ContinuousInf.{u2} β _inst_2 (SemilatticeInf.toHasInf.{u2} β _inst_5)] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toHasLe.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_5)))) (Inf.inf.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instInf.{u1, u2} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g) g
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : SemilatticeInf.{u1} β] [_inst_6 : ContinuousInf.{u1} β _inst_2 (SemilatticeInf.toInf.{u1} β _inst_5)] (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ), LE.le.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (Preorder.toLE.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u2, u1} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_5)))) (Inf.inf.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instInf.{u2, u1} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g) g
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.inf_le_right MeasureTheory.AEEqFun.inf_le_rightₓ'. -/
protected theorem inf_le_right (f g : α →ₘ[μ] β) : f ⊓ g ≤ g :=
  by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_inf f g]with _ ha
  rw [ha]
  exact inf_le_right
#align measure_theory.ae_eq_fun.inf_le_right MeasureTheory.AEEqFun.inf_le_right

/- warning: measure_theory.ae_eq_fun.le_inf -> MeasureTheory.AEEqFun.le_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : SemilatticeInf.{u2} β] [_inst_6 : ContinuousInf.{u2} β _inst_2 (SemilatticeInf.toHasInf.{u2} β _inst_5)] (f' : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ), (LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toHasLe.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_5)))) f' f) -> (LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toHasLe.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_5)))) f' g) -> (LE.le.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (Preorder.toHasLe.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u1, u2} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β _inst_5)))) f' (Inf.inf.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instInf.{u1, u2} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : SemilatticeInf.{u1} β] [_inst_6 : ContinuousInf.{u1} β _inst_2 (SemilatticeInf.toInf.{u1} β _inst_5)] (f' : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (f : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (g : MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ), (LE.le.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (Preorder.toLE.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u2, u1} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_5)))) f' f) -> (LE.le.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (Preorder.toLE.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u2, u1} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_5)))) f' g) -> (LE.le.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (Preorder.toLE.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instPreorder.{u2, u1} α β _inst_1 μ _inst_2 (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β _inst_5)))) f' (Inf.inf.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instInf.{u2, u1} α β _inst_1 μ _inst_2 _inst_5 _inst_6) f g))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.le_inf MeasureTheory.AEEqFun.le_infₓ'. -/
protected theorem le_inf (f' f g : α →ₘ[μ] β) (hf : f' ≤ f) (hg : f' ≤ g) : f' ≤ f ⊓ g :=
  by
  rw [← coe_fn_le] at hf hg⊢
  filter_upwards [hf, hg, coe_fn_inf f g]with _ haf hag ha_inf
  rw [ha_inf]
  exact le_inf haf hag
#align measure_theory.ae_eq_fun.le_inf MeasureTheory.AEEqFun.le_inf

end Inf

instance [Lattice β] [TopologicalLattice β] : Lattice (α →ₘ[μ] β) :=
  { AEEqFun.instPartialOrder with
    sup := Sup.sup
    le_sup_left := AEEqFun.le_sup_left
    le_sup_right := AEEqFun.le_sup_right
    sup_le := AEEqFun.sup_le
    inf := Inf.inf
    inf_le_left := AEEqFun.inf_le_left
    inf_le_right := AEEqFun.inf_le_right
    le_inf := AEEqFun.le_inf }

end Lattice

end Order

variable (α)

#print MeasureTheory.AEEqFun.const /-
/-- The equivalence class of a constant function: `[λ a:α, b]`, based on the equivalence relation of
    being almost everywhere equal -/
def const (b : β) : α →ₘ[μ] β :=
  mk (fun a : α => b) aestronglyMeasurable_const
#align measure_theory.ae_eq_fun.const MeasureTheory.AEEqFun.const
-/

/- warning: measure_theory.ae_eq_fun.coe_fn_const -> MeasureTheory.AEEqFun.coeFn_const is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] (b : β), Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_2) (MeasureTheory.AEEqFun.const.{u1, u2} α β _inst_1 μ _inst_2 b)) (Function.const.{succ u2, succ u1} β α b)
but is expected to have type
  forall (α : Type.{u2}) {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_2 : TopologicalSpace.{u1} β] (b : β), Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_2 (MeasureTheory.AEEqFun.const.{u2, u1} α β _inst_1 μ _inst_2 b)) (Function.const.{succ u1, succ u2} β α b)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_const MeasureTheory.AEEqFun.coeFn_constₓ'. -/
theorem coeFn_const (b : β) : (const α b : α →ₘ[μ] β) =ᵐ[μ] Function.const α b :=
  coeFn_mk _ _
#align measure_theory.ae_eq_fun.coe_fn_const MeasureTheory.AEEqFun.coeFn_const

variable {α}

instance [Inhabited β] : Inhabited (α →ₘ[μ] β) :=
  ⟨const α default⟩

@[to_additive]
instance [One β] : One (α →ₘ[μ] β) :=
  ⟨const α 1⟩

/- warning: measure_theory.ae_eq_fun.one_def -> MeasureTheory.AEEqFun.one_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : One.{u2} β], Eq.{succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (OfNat.ofNat.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) 1 (OfNat.mk.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) 1 (One.one.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instOne.{u1, u2} α β _inst_1 μ _inst_2 _inst_5)))) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 (fun (a : α) => OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_5))) (MeasureTheory.aestronglyMeasurable_const.{u1, u2} α β _inst_1 μ _inst_2 (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_5)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : One.{u2} β], Eq.{max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (OfNat.ofNat.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) 1 (One.toOfNat1.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_2 μ) (MeasureTheory.AEEqFun.instOne.{u1, u2} α β _inst_1 μ _inst_2 _inst_5))) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ β _inst_2 (fun (a : α) => OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β _inst_5)) (MeasureTheory.aestronglyMeasurable_const.{u2, u1} α β _inst_1 μ _inst_2 (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β _inst_5))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.one_def MeasureTheory.AEEqFun.one_defₓ'. -/
@[to_additive]
theorem one_def [One β] : (1 : α →ₘ[μ] β) = mk (fun a : α => 1) aestronglyMeasurable_const :=
  rfl
#align measure_theory.ae_eq_fun.one_def MeasureTheory.AEEqFun.one_def
#align measure_theory.ae_eq_fun.zero_def MeasureTheory.AEEqFun.zero_def

#print MeasureTheory.AEEqFun.coeFn_one /-
@[to_additive]
theorem coeFn_one [One β] : ⇑(1 : α →ₘ[μ] β) =ᵐ[μ] 1 :=
  coeFn_const _ _
#align measure_theory.ae_eq_fun.coe_fn_one MeasureTheory.AEEqFun.coeFn_one
#align measure_theory.ae_eq_fun.coe_fn_zero MeasureTheory.AEEqFun.coeFn_zero
-/

#print MeasureTheory.AEEqFun.one_toGerm /-
@[simp, to_additive]
theorem one_toGerm [One β] : (1 : α →ₘ[μ] β).toGerm = 1 :=
  rfl
#align measure_theory.ae_eq_fun.one_to_germ MeasureTheory.AEEqFun.one_toGerm
#align measure_theory.ae_eq_fun.zero_to_germ MeasureTheory.AEEqFun.zero_toGerm
-/

-- Note we set up the scalar actions before the `monoid` structures in case we want to
-- try to override the `nsmul` or `zsmul` fields in future.
section SMul

variable {𝕜 𝕜' : Type _}

variable [SMul 𝕜 γ] [ContinuousConstSMul 𝕜 γ]

variable [SMul 𝕜' γ] [ContinuousConstSMul 𝕜' γ]

instance : SMul 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun c f => comp ((· • ·) c) (continuous_id.const_smul c) f⟩

/- warning: measure_theory.ae_eq_fun.smul_mk -> MeasureTheory.AEEqFun.smul_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] {𝕜 : Type.{u3}} [_inst_5 : SMul.{u3, u2} 𝕜 γ] [_inst_6 : ContinuousConstSMul.{u3, u2} 𝕜 γ _inst_3 _inst_5] (c : 𝕜) (f : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α γ _inst_3 _inst_1 f μ), Eq.{succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (SMul.smul.{u3, max u1 u2} 𝕜 (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instSMul.{u1, u2, u3} α γ _inst_1 μ _inst_3 𝕜 _inst_5 _inst_6) c (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 f hf)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 (SMul.smul.{u3, max u1 u2} 𝕜 (α -> γ) (Function.hasSMul.{u1, u3, u2} α 𝕜 γ _inst_5) c f) (MeasureTheory.AEStronglyMeasurable.const_smul.{u1, u2, u3} α γ _inst_1 μ _inst_3 f 𝕜 _inst_5 _inst_6 hf c))
but is expected to have type
  forall {α : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u3} α] {μ : MeasureTheory.Measure.{u3} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] {𝕜 : Type.{u1}} [_inst_5 : SMul.{u1, u2} 𝕜 γ] [_inst_6 : ContinuousConstSMul.{u1, u2} 𝕜 γ _inst_3 _inst_5] (c : 𝕜) (f : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u3, u2} α γ _inst_3 _inst_1 f μ), Eq.{max (succ u3) (succ u2)} (MeasureTheory.AEEqFun.{u3, u2} α γ _inst_1 _inst_3 μ) (HSMul.hSMul.{u1, max u3 u2, max u3 u2} 𝕜 (MeasureTheory.AEEqFun.{u3, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u3, u2} α γ _inst_1 _inst_3 μ) (instHSMul.{u1, max u3 u2} 𝕜 (MeasureTheory.AEEqFun.{u3, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instSMul.{u3, u2, u1} α γ _inst_1 μ _inst_3 𝕜 _inst_5 _inst_6)) c (MeasureTheory.AEEqFun.mk.{u3, u2} α _inst_1 μ γ _inst_3 f hf)) (MeasureTheory.AEEqFun.mk.{u3, u2} α _inst_1 μ γ _inst_3 (HSMul.hSMul.{u1, max u3 u2, max u3 u2} 𝕜 (α -> γ) (α -> γ) (instHSMul.{u1, max u3 u2} 𝕜 (α -> γ) (Pi.instSMul.{u3, u2, u1} α 𝕜 (fun (a._@.Mathlib.MeasureTheory.Function.AEEqFun._hyg.7207 : α) => γ) (fun (i : α) => _inst_5))) c f) (MeasureTheory.AEStronglyMeasurable.const_smul.{u3, u2, u1} α γ _inst_1 μ _inst_3 f 𝕜 _inst_5 _inst_6 hf c))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.smul_mk MeasureTheory.AEEqFun.smul_mkₓ'. -/
@[simp]
theorem smul_mk (c : 𝕜) (f : α → γ) (hf : AEStronglyMeasurable f μ) :
    c • (mk f hf : α →ₘ[μ] γ) = mk (c • f) (hf.const_smul _) :=
  rfl
#align measure_theory.ae_eq_fun.smul_mk MeasureTheory.AEEqFun.smul_mk

/- warning: measure_theory.ae_eq_fun.coe_fn_smul -> MeasureTheory.AEEqFun.coeFn_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] {𝕜 : Type.{u3}} [_inst_5 : SMul.{u3, u2} 𝕜 γ] [_inst_6 : ContinuousConstSMul.{u3, u2} 𝕜 γ _inst_3 _inst_5] (c : 𝕜) (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u1, u2} α γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) (SMul.smul.{u3, max u1 u2} 𝕜 (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instSMul.{u1, u2, u3} α γ _inst_1 μ _inst_3 𝕜 _inst_5 _inst_6) c f)) (SMul.smul.{u3, max u1 u2} 𝕜 (α -> γ) (Function.hasSMul.{u1, u3, u2} α 𝕜 γ _inst_5) c (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) f))
but is expected to have type
  forall {α : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u3} α] {μ : MeasureTheory.Measure.{u3} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] {𝕜 : Type.{u1}} [_inst_5 : SMul.{u1, u2} 𝕜 γ] [_inst_6 : ContinuousConstSMul.{u1, u2} 𝕜 γ _inst_3 _inst_5] (c : 𝕜) (f : MeasureTheory.AEEqFun.{u3, u2} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u3, u2} α γ (MeasureTheory.Measure.ae.{u3} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u3, u2} α γ _inst_1 μ _inst_3 (HSMul.hSMul.{u1, max u3 u2, max u3 u2} 𝕜 (MeasureTheory.AEEqFun.{u3, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u3, u2} α γ _inst_1 _inst_3 μ) (instHSMul.{u1, max u3 u2} 𝕜 (MeasureTheory.AEEqFun.{u3, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instSMul.{u3, u2, u1} α γ _inst_1 μ _inst_3 𝕜 _inst_5 _inst_6)) c f)) (HSMul.hSMul.{u1, max u3 u2, max u3 u2} 𝕜 (α -> γ) (α -> γ) (instHSMul.{u1, max u3 u2} 𝕜 (α -> γ) (Pi.instSMul.{u3, u2, u1} α 𝕜 (fun (a._@.Mathlib.MeasureTheory.Function.AEEqFun._hyg.1013 : α) => γ) (fun (i : α) => _inst_5))) c (MeasureTheory.AEEqFun.cast.{u3, u2} α γ _inst_1 μ _inst_3 f))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_smul MeasureTheory.AEEqFun.coeFn_smulₓ'. -/
theorem coeFn_smul (c : 𝕜) (f : α →ₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • f :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_smul MeasureTheory.AEEqFun.coeFn_smul

/- warning: measure_theory.ae_eq_fun.smul_to_germ -> MeasureTheory.AEEqFun.smul_toGerm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] {𝕜 : Type.{u3}} [_inst_5 : SMul.{u3, u2} 𝕜 γ] [_inst_6 : ContinuousConstSMul.{u3, u2} 𝕜 γ _inst_3 _inst_5] (c : 𝕜) (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 (SMul.smul.{u3, max u1 u2} 𝕜 (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instSMul.{u1, u2, u3} α γ _inst_1 μ _inst_3 𝕜 _inst_5 _inst_6) c f)) (SMul.smul.{u3, max u1 u2} 𝕜 (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (Filter.Germ.hasSmul.{u1, u3, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) 𝕜 γ _inst_5) c (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 f))
but is expected to have type
  forall {α : Type.{u3}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u3} α] {μ : MeasureTheory.Measure.{u3} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] {𝕜 : Type.{u1}} [_inst_5 : SMul.{u1, u2} 𝕜 γ] [_inst_6 : ContinuousConstSMul.{u1, u2} 𝕜 γ _inst_3 _inst_5] (c : 𝕜) (f : MeasureTheory.AEEqFun.{u3, u2} α γ _inst_1 _inst_3 μ), Eq.{max (succ u3) (succ u2)} (Filter.Germ.{u3, u2} α (MeasureTheory.Measure.ae.{u3} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u3, u2} α γ _inst_1 μ _inst_3 (HSMul.hSMul.{u1, max u3 u2, max u3 u2} 𝕜 (MeasureTheory.AEEqFun.{u3, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u3, u2} α γ _inst_1 _inst_3 μ) (instHSMul.{u1, max u3 u2} 𝕜 (MeasureTheory.AEEqFun.{u3, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instSMul.{u3, u2, u1} α γ _inst_1 μ _inst_3 𝕜 _inst_5 _inst_6)) c f)) (HSMul.hSMul.{u1, max u3 u2, max u3 u2} 𝕜 (Filter.Germ.{u3, u2} α (MeasureTheory.Measure.ae.{u3} α _inst_1 μ) γ) (Filter.Germ.{u3, u2} α (MeasureTheory.Measure.ae.{u3} α _inst_1 μ) γ) (instHSMul.{u1, max u3 u2} 𝕜 (Filter.Germ.{u3, u2} α (MeasureTheory.Measure.ae.{u3} α _inst_1 μ) γ) (Filter.Germ.smul.{u3, u1, u2} α (MeasureTheory.Measure.ae.{u3} α _inst_1 μ) 𝕜 γ _inst_5)) c (MeasureTheory.AEEqFun.toGerm.{u3, u2} α γ _inst_1 μ _inst_3 f))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.smul_to_germ MeasureTheory.AEEqFun.smul_toGermₓ'. -/
theorem smul_toGerm (c : 𝕜) (f : α →ₘ[μ] γ) : (c • f).toGerm = c • f.toGerm :=
  comp_toGerm _ _ _
#align measure_theory.ae_eq_fun.smul_to_germ MeasureTheory.AEEqFun.smul_toGerm

instance [SMulCommClass 𝕜 𝕜' γ] : SMulCommClass 𝕜 𝕜' (α →ₘ[μ] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_comm]⟩

instance [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' γ] : IsScalarTower 𝕜 𝕜' (α →ₘ[μ] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_assoc]⟩

instance [SMul 𝕜ᵐᵒᵖ γ] [IsCentralScalar 𝕜 γ] : IsCentralScalar 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun a f => induction_on f fun f hf => by simp_rw [smul_mk, op_smul_eq_smul]⟩

end SMul

section Mul

variable [Mul γ] [ContinuousMul γ]

@[to_additive]
instance : Mul (α →ₘ[μ] γ) :=
  ⟨comp₂ (· * ·) continuous_mul⟩

/- warning: measure_theory.ae_eq_fun.mk_mul_mk -> MeasureTheory.AEEqFun.mk_mul_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Mul.{u2} γ] [_inst_6 : ContinuousMul.{u2} γ _inst_3 _inst_5] (f : α -> γ) (g : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α γ _inst_3 _inst_1 f μ) (hg : MeasureTheory.AEStronglyMeasurable.{u1, u2} α γ _inst_3 _inst_1 g μ), Eq.{succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (instHMul.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instMul.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 f hf) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 g hg)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> γ) (α -> γ) (α -> γ) (instHMul.{max u1 u2} (α -> γ) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_5))) f g) (MeasureTheory.AEStronglyMeasurable.mul.{u1, u2} α γ _inst_1 μ _inst_3 f g _inst_5 _inst_6 hf hg))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Mul.{u1} γ] [_inst_6 : ContinuousMul.{u1} γ _inst_3 _inst_5] (f : α -> γ) (g : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α γ _inst_3 _inst_1 f μ) (hg : MeasureTheory.AEStronglyMeasurable.{u2, u1} α γ _inst_3 _inst_1 g μ), Eq.{max (succ u2) (succ u1)} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (instHMul.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instMul.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 f hf) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 g hg)) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> γ) (α -> γ) (α -> γ) (instHMul.{max u2 u1} (α -> γ) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_5))) f g) (MeasureTheory.AEStronglyMeasurable.mul.{u2, u1} α γ _inst_1 μ _inst_3 f g _inst_5 _inst_6 hf hg))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.mk_mul_mk MeasureTheory.AEEqFun.mk_mul_mkₓ'. -/
@[simp, to_additive]
theorem mk_mul_mk (f g : α → γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    (mk f hf : α →ₘ[μ] γ) * mk g hg = mk (f * g) (hf.mul hg) :=
  rfl
#align measure_theory.ae_eq_fun.mk_mul_mk MeasureTheory.AEEqFun.mk_mul_mk
#align measure_theory.ae_eq_fun.mk_add_mk MeasureTheory.AEEqFun.mk_add_mk

/- warning: measure_theory.ae_eq_fun.coe_fn_mul -> MeasureTheory.AEEqFun.coeFn_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Mul.{u2} γ] [_inst_6 : ContinuousMul.{u2} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (g : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u1, u2} α γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (instHMul.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instMul.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f g)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (α -> γ) (α -> γ) (α -> γ) (instHMul.{max u1 u2} (α -> γ) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_5))) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) f) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) g))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Mul.{u1} γ] [_inst_6 : ContinuousMul.{u1} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (g : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u2, u1} α γ (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (instHMul.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instMul.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f g)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (α -> γ) (α -> γ) (α -> γ) (instHMul.{max u2 u1} (α -> γ) (Pi.instMul.{u2, u1} α (fun (ᾰ : α) => γ) (fun (i : α) => _inst_5))) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 f) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 g))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_mul MeasureTheory.AEEqFun.coeFn_mulₓ'. -/
@[to_additive]
theorem coeFn_mul (f g : α →ₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g :=
  coeFn_comp₂ _ _ _ _
#align measure_theory.ae_eq_fun.coe_fn_mul MeasureTheory.AEEqFun.coeFn_mul
#align measure_theory.ae_eq_fun.coe_fn_add MeasureTheory.AEEqFun.coeFn_add

/- warning: measure_theory.ae_eq_fun.mul_to_germ -> MeasureTheory.AEEqFun.mul_toGerm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Mul.{u2} γ] [_inst_6 : ContinuousMul.{u2} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (g : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (instHMul.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instMul.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f g)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (instHMul.{max u1 u2} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (Filter.Germ.hasMul.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ _inst_5)) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 f) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 g))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Mul.{u1} γ] [_inst_6 : ContinuousMul.{u1} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (g : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ), Eq.{max (succ u2) (succ u1)} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α γ _inst_1 μ _inst_3 (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (instHMul.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instMul.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f g)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (instHMul.{max u2 u1} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (Filter.Germ.mul.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ _inst_5)) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α γ _inst_1 μ _inst_3 f) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α γ _inst_1 μ _inst_3 g))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.mul_to_germ MeasureTheory.AEEqFun.mul_toGermₓ'. -/
@[simp, to_additive]
theorem mul_toGerm (f g : α →ₘ[μ] γ) : (f * g).toGerm = f.toGerm * g.toGerm :=
  comp₂_toGerm _ _ _ _
#align measure_theory.ae_eq_fun.mul_to_germ MeasureTheory.AEEqFun.mul_toGerm
#align measure_theory.ae_eq_fun.add_to_germ MeasureTheory.AEEqFun.add_toGerm

end Mul

instance [AddMonoid γ] [ContinuousAdd γ] : AddMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.AddMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

instance [AddCommMonoid γ] [ContinuousAdd γ] : AddCommMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.AddCommMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

section Monoid

variable [Monoid γ] [ContinuousMul γ]

instance : Pow (α →ₘ[μ] γ) ℕ :=
  ⟨fun f n => comp _ (continuous_pow n) f⟩

/- warning: measure_theory.ae_eq_fun.mk_pow -> MeasureTheory.AEEqFun.mk_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Monoid.{u2} γ] [_inst_6 : ContinuousMul.{u2} γ _inst_3 (MulOneClass.toHasMul.{u2} γ (Monoid.toMulOneClass.{u2} γ _inst_5))] (f : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α γ _inst_3 _inst_1 f μ) (n : Nat), Eq.{succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (HPow.hPow.{max u1 u2, 0, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) Nat (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (instHPow.{max u1 u2, 0} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) Nat (MeasureTheory.AEEqFun.instPowNat.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 f hf) n) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> γ) Nat (α -> γ) (instHPow.{max u1 u2, 0} (α -> γ) Nat (Pi.hasPow.{u1, u2, 0} α Nat (fun (ᾰ : α) => γ) (fun (i : α) => Monoid.Pow.{u2} γ _inst_5))) f n) (Continuous.comp_aestronglyMeasurable.{u1, u2, u2} α γ γ _inst_1 μ _inst_3 _inst_3 (fun (a : γ) => HPow.hPow.{u2, 0, u2} γ Nat γ (instHPow.{u2, 0} γ Nat (Monoid.Pow.{u2} γ _inst_5)) a n) (fun (x : α) => f x) (continuous_pow.{u2} γ _inst_3 _inst_5 _inst_6 n) hf))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Monoid.{u1} γ] [_inst_6 : ContinuousMul.{u1} γ _inst_3 (MulOneClass.toMul.{u1} γ (Monoid.toMulOneClass.{u1} γ _inst_5))] (f : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α γ _inst_3 _inst_1 f μ) (n : Nat), Eq.{max (succ u2) (succ u1)} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (HPow.hPow.{max u2 u1, 0, max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) Nat (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (instHPow.{max u2 u1, 0} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) Nat (MeasureTheory.AEEqFun.instPowNat.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 f hf) n) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 (HPow.hPow.{max u2 u1, 0, max u2 u1} (α -> γ) Nat (α -> γ) (instHPow.{max u2 u1, 0} (α -> γ) Nat (Pi.instPow.{u2, u1, 0} α Nat (fun (ᾰ : α) => γ) (fun (i : α) => Monoid.Pow.{u1} γ _inst_5))) f n) (Continuous.comp_aestronglyMeasurable.{u2, u1, u1} α γ γ _inst_1 μ _inst_3 _inst_3 (fun (a : γ) => HPow.hPow.{u1, 0, u1} γ Nat γ (instHPow.{u1, 0} γ Nat (Monoid.Pow.{u1} γ _inst_5)) a n) (fun (x : α) => f x) (continuous_pow.{u1} γ _inst_3 _inst_5 _inst_6 n) hf))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.mk_pow MeasureTheory.AEEqFun.mk_powₓ'. -/
@[simp]
theorem mk_pow (f : α → γ) (hf) (n : ℕ) :
    (mk f hf : α →ₘ[μ] γ) ^ n = mk (f ^ n) ((continuous_pow n).comp_aestronglyMeasurable hf) :=
  rfl
#align measure_theory.ae_eq_fun.mk_pow MeasureTheory.AEEqFun.mk_pow

/- warning: measure_theory.ae_eq_fun.coe_fn_pow -> MeasureTheory.AEEqFun.coeFn_pow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Monoid.{u2} γ] [_inst_6 : ContinuousMul.{u2} γ _inst_3 (MulOneClass.toHasMul.{u2} γ (Monoid.toMulOneClass.{u2} γ _inst_5))] (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (n : Nat), Filter.EventuallyEq.{u1, u2} α γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) (HPow.hPow.{max u1 u2, 0, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) Nat (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (instHPow.{max u1 u2, 0} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) Nat (MeasureTheory.AEEqFun.instPowNat.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f n)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> γ) Nat (α -> γ) (instHPow.{max u1 u2, 0} (α -> γ) Nat (Pi.hasPow.{u1, u2, 0} α Nat (fun (ᾰ : α) => γ) (fun (i : α) => Monoid.Pow.{u2} γ _inst_5))) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) f) n)
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Monoid.{u1} γ] [_inst_6 : ContinuousMul.{u1} γ _inst_3 (MulOneClass.toMul.{u1} γ (Monoid.toMulOneClass.{u1} γ _inst_5))] (f : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (n : Nat), Filter.EventuallyEq.{u2, u1} α γ (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 (HPow.hPow.{max u2 u1, 0, max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) Nat (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (instHPow.{max u2 u1, 0} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) Nat (MeasureTheory.AEEqFun.instPowNat.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f n)) (HPow.hPow.{max u2 u1, 0, max u2 u1} (α -> γ) Nat (α -> γ) (instHPow.{max u2 u1, 0} (α -> γ) Nat (Pi.instPow.{u2, u1, 0} α Nat (fun (ᾰ : α) => γ) (fun (i : α) => Monoid.Pow.{u1} γ _inst_5))) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 f) n)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_pow MeasureTheory.AEEqFun.coeFn_powₓ'. -/
theorem coeFn_pow (f : α →ₘ[μ] γ) (n : ℕ) : ⇑(f ^ n) =ᵐ[μ] f ^ n :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_pow MeasureTheory.AEEqFun.coeFn_pow

/- warning: measure_theory.ae_eq_fun.pow_to_germ -> MeasureTheory.AEEqFun.pow_toGerm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Monoid.{u2} γ] [_inst_6 : ContinuousMul.{u2} γ _inst_3 (MulOneClass.toHasMul.{u2} γ (Monoid.toMulOneClass.{u2} γ _inst_5))] (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (n : Nat), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 (HPow.hPow.{max u1 u2, 0, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) Nat (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (instHPow.{max u1 u2, 0} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) Nat (MeasureTheory.AEEqFun.instPowNat.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f n)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) Nat (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (instHPow.{max u1 u2, 0} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) Nat (Filter.Germ.hasPow.{u1, 0, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) Nat γ (Monoid.Pow.{u2} γ _inst_5))) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 f) n)
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Monoid.{u1} γ] [_inst_6 : ContinuousMul.{u1} γ _inst_3 (MulOneClass.toMul.{u1} γ (Monoid.toMulOneClass.{u1} γ _inst_5))] (f : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (n : Nat), Eq.{max (succ u2) (succ u1)} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α γ _inst_1 μ _inst_3 (HPow.hPow.{max u2 u1, 0, max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) Nat (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (instHPow.{max u2 u1, 0} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) Nat (MeasureTheory.AEEqFun.instPowNat.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f n)) (HPow.hPow.{max u2 u1, 0, max u2 u1} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) Nat (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (instHPow.{max u2 u1, 0} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) Nat (Filter.Germ.pow.{u2, 0, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) Nat γ (Monoid.Pow.{u1} γ _inst_5))) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α γ _inst_1 μ _inst_3 f) n)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.pow_to_germ MeasureTheory.AEEqFun.pow_toGermₓ'. -/
@[simp]
theorem pow_toGerm (f : α →ₘ[μ] γ) (n : ℕ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _
#align measure_theory.ae_eq_fun.pow_to_germ MeasureTheory.AEEqFun.pow_toGerm

@[to_additive]
instance : Monoid (α →ₘ[μ] γ) :=
  toGerm_injective.Monoid toGerm one_toGerm mul_toGerm pow_toGerm

/- warning: measure_theory.ae_eq_fun.to_germ_monoid_hom -> MeasureTheory.AEEqFun.toGermMonoidHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Monoid.{u2} γ] [_inst_6 : ContinuousMul.{u2} γ _inst_3 (MulOneClass.toHasMul.{u2} γ (Monoid.toMulOneClass.{u2} γ _inst_5))], MonoidHom.{max u1 u2, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (Monoid.toMulOneClass.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instMonoid.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) (Monoid.toMulOneClass.{max u1 u2} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (Filter.Germ.monoid.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ _inst_5))
but is expected to have type
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Monoid.{u2} γ] [_inst_6 : ContinuousMul.{u2} γ _inst_3 (MulOneClass.toMul.{u2} γ (Monoid.toMulOneClass.{u2} γ _inst_5))], MonoidHom.{max u2 u1, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (Monoid.toMulOneClass.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instMonoid.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) (Monoid.toMulOneClass.{max u1 u2} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (Filter.Germ.monoid.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ _inst_5))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.to_germ_monoid_hom MeasureTheory.AEEqFun.toGermMonoidHomₓ'. -/
/-- `ae_eq_fun.to_germ` as a `monoid_hom`. -/
@[to_additive "`ae_eq_fun.to_germ` as an `add_monoid_hom`.", simps]
def toGermMonoidHom : (α →ₘ[μ] γ) →* μ.ae.Germ γ
    where
  toFun := toGerm
  map_one' := one_toGerm
  map_mul' := mul_toGerm
#align measure_theory.ae_eq_fun.to_germ_monoid_hom MeasureTheory.AEEqFun.toGermMonoidHom
#align measure_theory.ae_eq_fun.to_germ_add_monoid_hom MeasureTheory.AEEqFun.toGermAddMonoidHom

end Monoid

@[to_additive]
instance [CommMonoid γ] [ContinuousMul γ] : CommMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.CommMonoid toGerm one_toGerm mul_toGerm pow_toGerm

section Group

variable [Group γ] [TopologicalGroup γ]

section Inv

@[to_additive]
instance : Inv (α →ₘ[μ] γ) :=
  ⟨comp Inv.inv continuous_inv⟩

/- warning: measure_theory.ae_eq_fun.inv_mk -> MeasureTheory.AEEqFun.inv_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Group.{u2} γ] [_inst_6 : TopologicalGroup.{u2} γ _inst_3 _inst_5] (f : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α γ _inst_3 _inst_1 f μ), Eq.{succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (Inv.inv.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instInv.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 f hf)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 (Inv.inv.{max u1 u2} (α -> γ) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => γ) (fun (i : α) => DivInvMonoid.toHasInv.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5))) f) (MeasureTheory.AEStronglyMeasurable.inv.{u1, u2} α γ _inst_1 μ _inst_3 f _inst_5 _inst_6 hf))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Group.{u1} γ] [_inst_6 : TopologicalGroup.{u1} γ _inst_3 _inst_5] (f : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α γ _inst_3 _inst_1 f μ), Eq.{max (succ u2) (succ u1)} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (Inv.inv.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instInv.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 f hf)) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 (Inv.inv.{max u1 u2} (α -> γ) (Pi.instInv.{u2, u1} α (fun (ᾰ : α) => γ) (fun (i : α) => InvOneClass.toInv.{u1} γ (DivInvOneMonoid.toInvOneClass.{u1} γ (DivisionMonoid.toDivInvOneMonoid.{u1} γ (Group.toDivisionMonoid.{u1} γ _inst_5))))) f) (MeasureTheory.AEStronglyMeasurable.inv.{u2, u1} α γ _inst_1 μ _inst_3 f _inst_5 _inst_6 hf))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.inv_mk MeasureTheory.AEEqFun.inv_mkₓ'. -/
@[simp, to_additive]
theorem inv_mk (f : α → γ) (hf) : (mk f hf : α →ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv :=
  rfl
#align measure_theory.ae_eq_fun.inv_mk MeasureTheory.AEEqFun.inv_mk
#align measure_theory.ae_eq_fun.neg_mk MeasureTheory.AEEqFun.neg_mk

/- warning: measure_theory.ae_eq_fun.coe_fn_inv -> MeasureTheory.AEEqFun.coeFn_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Group.{u2} γ] [_inst_6 : TopologicalGroup.{u2} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u1, u2} α γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) (Inv.inv.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instInv.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6) f)) (Inv.inv.{max u1 u2} (α -> γ) (Pi.instInv.{u1, u2} α (fun (ᾰ : α) => γ) (fun (i : α) => DivInvMonoid.toHasInv.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5))) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) f))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Group.{u1} γ] [_inst_6 : TopologicalGroup.{u1} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u2, u1} α γ (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 (Inv.inv.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instInv.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6) f)) (Inv.inv.{max u2 u1} (α -> γ) (Pi.instInv.{u2, u1} α (fun (ᾰ : α) => γ) (fun (i : α) => InvOneClass.toInv.{u1} γ (DivInvOneMonoid.toInvOneClass.{u1} γ (DivisionMonoid.toDivInvOneMonoid.{u1} γ (Group.toDivisionMonoid.{u1} γ _inst_5))))) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 f))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_inv MeasureTheory.AEEqFun.coeFn_invₓ'. -/
@[to_additive]
theorem coeFn_inv (f : α →ₘ[μ] γ) : ⇑f⁻¹ =ᵐ[μ] f⁻¹ :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_inv MeasureTheory.AEEqFun.coeFn_inv
#align measure_theory.ae_eq_fun.coe_fn_neg MeasureTheory.AEEqFun.coeFn_neg

/- warning: measure_theory.ae_eq_fun.inv_to_germ -> MeasureTheory.AEEqFun.inv_toGerm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Group.{u2} γ] [_inst_6 : TopologicalGroup.{u2} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 (Inv.inv.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instInv.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6) f)) (Inv.inv.{max u1 u2} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (Filter.Germ.hasInv.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ (DivInvMonoid.toHasInv.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5))) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 f))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Group.{u1} γ] [_inst_6 : TopologicalGroup.{u1} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ), Eq.{max (succ u2) (succ u1)} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α γ _inst_1 μ _inst_3 (Inv.inv.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instInv.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6) f)) (Inv.inv.{max u2 u1} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (Filter.Germ.inv.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ (InvOneClass.toInv.{u1} γ (DivInvOneMonoid.toInvOneClass.{u1} γ (DivisionMonoid.toDivInvOneMonoid.{u1} γ (Group.toDivisionMonoid.{u1} γ _inst_5))))) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α γ _inst_1 μ _inst_3 f))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.inv_to_germ MeasureTheory.AEEqFun.inv_toGermₓ'. -/
@[to_additive]
theorem inv_toGerm (f : α →ₘ[μ] γ) : f⁻¹.toGerm = f.toGerm⁻¹ :=
  comp_toGerm _ _ _
#align measure_theory.ae_eq_fun.inv_to_germ MeasureTheory.AEEqFun.inv_toGerm
#align measure_theory.ae_eq_fun.neg_to_germ MeasureTheory.AEEqFun.neg_toGerm

end Inv

section Div

@[to_additive]
instance : Div (α →ₘ[μ] γ) :=
  ⟨comp₂ Div.div continuous_div'⟩

/- warning: measure_theory.ae_eq_fun.mk_div -> MeasureTheory.AEEqFun.mk_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Group.{u2} γ] [_inst_6 : TopologicalGroup.{u2} γ _inst_3 _inst_5] (f : α -> γ) (g : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α γ _inst_3 _inst_1 f μ) (hg : MeasureTheory.AEStronglyMeasurable.{u1, u2} α γ _inst_3 _inst_1 g μ), Eq.{succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> γ) (α -> γ) (α -> γ) (instHDiv.{max u1 u2} (α -> γ) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => γ) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5)))) f g) (MeasureTheory.AEStronglyMeasurable.div.{u1, u2} α γ _inst_1 μ _inst_3 f g _inst_5 _inst_6 hf hg)) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (instHDiv.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instDiv.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 f hf) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 g hg))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Group.{u1} γ] [_inst_6 : TopologicalGroup.{u1} γ _inst_3 _inst_5] (f : α -> γ) (g : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α γ _inst_3 _inst_1 f μ) (hg : MeasureTheory.AEStronglyMeasurable.{u2, u1} α γ _inst_3 _inst_1 g μ), Eq.{max (succ u2) (succ u1)} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> γ) (α -> γ) (α -> γ) (instHDiv.{max u2 u1} (α -> γ) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => γ) (fun (i : α) => DivInvMonoid.toDiv.{u1} γ (Group.toDivInvMonoid.{u1} γ _inst_5)))) f g) (MeasureTheory.AEStronglyMeasurable.div.{u2, u1} α γ _inst_1 μ _inst_3 f g _inst_5 _inst_6 hf hg)) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (instHDiv.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instDiv.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 f hf) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 g hg))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.mk_div MeasureTheory.AEEqFun.mk_divₓ'. -/
@[simp, to_additive]
theorem mk_div (f g : α → γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    mk (f / g) (hf.div hg) = (mk f hf : α →ₘ[μ] γ) / mk g hg :=
  rfl
#align measure_theory.ae_eq_fun.mk_div MeasureTheory.AEEqFun.mk_div
#align measure_theory.ae_eq_fun.mk_sub MeasureTheory.AEEqFun.mk_sub

/- warning: measure_theory.ae_eq_fun.coe_fn_div -> MeasureTheory.AEEqFun.coeFn_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Group.{u2} γ] [_inst_6 : TopologicalGroup.{u2} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (g : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u1, u2} α γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (instHDiv.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instDiv.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f g)) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (α -> γ) (α -> γ) (α -> γ) (instHDiv.{max u1 u2} (α -> γ) (Pi.instDiv.{u1, u2} α (fun (ᾰ : α) => γ) (fun (i : α) => DivInvMonoid.toHasDiv.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5)))) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) f) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) g))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Group.{u1} γ] [_inst_6 : TopologicalGroup.{u1} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (g : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u2, u1} α γ (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (instHDiv.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instDiv.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f g)) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (α -> γ) (α -> γ) (α -> γ) (instHDiv.{max u2 u1} (α -> γ) (Pi.instDiv.{u2, u1} α (fun (ᾰ : α) => γ) (fun (i : α) => DivInvMonoid.toDiv.{u1} γ (Group.toDivInvMonoid.{u1} γ _inst_5)))) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 f) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 g))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_div MeasureTheory.AEEqFun.coeFn_divₓ'. -/
@[to_additive]
theorem coeFn_div (f g : α →ₘ[μ] γ) : ⇑(f / g) =ᵐ[μ] f / g :=
  coeFn_comp₂ _ _ _ _
#align measure_theory.ae_eq_fun.coe_fn_div MeasureTheory.AEEqFun.coeFn_div
#align measure_theory.ae_eq_fun.coe_fn_sub MeasureTheory.AEEqFun.coeFn_sub

/- warning: measure_theory.ae_eq_fun.div_to_germ -> MeasureTheory.AEEqFun.div_toGerm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Group.{u2} γ] [_inst_6 : TopologicalGroup.{u2} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (g : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (instHDiv.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instDiv.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f g)) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (instHDiv.{max u1 u2} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (Filter.Germ.hasDiv.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ (DivInvMonoid.toHasDiv.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5)))) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 f) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 g))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Group.{u1} γ] [_inst_6 : TopologicalGroup.{u1} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (g : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ), Eq.{max (succ u2) (succ u1)} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α γ _inst_1 μ _inst_3 (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (instHDiv.{max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.instDiv.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f g)) (HDiv.hDiv.{max u2 u1, max u2 u1, max u2 u1} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (instHDiv.{max u2 u1} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (Filter.Germ.div.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ (DivInvMonoid.toDiv.{u1} γ (Group.toDivInvMonoid.{u1} γ _inst_5)))) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α γ _inst_1 μ _inst_3 f) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α γ _inst_1 μ _inst_3 g))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.div_to_germ MeasureTheory.AEEqFun.div_toGermₓ'. -/
@[to_additive]
theorem div_toGerm (f g : α →ₘ[μ] γ) : (f / g).toGerm = f.toGerm / g.toGerm :=
  comp₂_toGerm _ _ _ _
#align measure_theory.ae_eq_fun.div_to_germ MeasureTheory.AEEqFun.div_toGerm
#align measure_theory.ae_eq_fun.sub_to_germ MeasureTheory.AEEqFun.sub_toGerm

end Div

section Zpow

#print MeasureTheory.AEEqFun.instPowInt /-
instance instPowInt : Pow (α →ₘ[μ] γ) ℤ :=
  ⟨fun f n => comp _ (continuous_zpow n) f⟩
#align measure_theory.ae_eq_fun.has_int_pow MeasureTheory.AEEqFun.instPowInt
-/

/- warning: measure_theory.ae_eq_fun.mk_zpow -> MeasureTheory.AEEqFun.mk_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Group.{u2} γ] [_inst_6 : TopologicalGroup.{u2} γ _inst_3 _inst_5] (f : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α γ _inst_3 _inst_1 f μ) (n : Int), Eq.{succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (HPow.hPow.{max u1 u2, 0, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) Int (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (instHPow.{max u1 u2, 0} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) Int (MeasureTheory.AEEqFun.instPowInt.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 f hf) n) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> γ) Int (α -> γ) (instHPow.{max u1 u2, 0} (α -> γ) Int (Pi.hasPow.{u1, u2, 0} α Int (fun (ᾰ : α) => γ) (fun (i : α) => DivInvMonoid.Pow.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5)))) f n) (Continuous.comp_aestronglyMeasurable.{u1, u2, u2} α γ γ _inst_1 μ _inst_3 _inst_3 (fun (a : γ) => HPow.hPow.{u2, 0, u2} γ Int γ (instHPow.{u2, 0} γ Int (DivInvMonoid.Pow.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5))) a n) (fun (x : α) => f x) (continuous_zpow.{u2} γ _inst_3 _inst_5 _inst_6 n) hf))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Group.{u1} γ] [_inst_6 : TopologicalGroup.{u1} γ _inst_3 _inst_5] (f : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α γ _inst_3 _inst_1 f μ) (n : Int), Eq.{max (succ u2) (succ u1)} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (HPow.hPow.{max u2 u1, 0, max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) Int (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (instHPow.{max u2 u1, 0} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) Int (MeasureTheory.AEEqFun.instPowInt.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 f hf) n) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 (HPow.hPow.{max u2 u1, 0, max u2 u1} (α -> γ) Int (α -> γ) (instHPow.{max u2 u1, 0} (α -> γ) Int (Pi.instPow.{u2, u1, 0} α Int (fun (ᾰ : α) => γ) (fun (i : α) => DivInvMonoid.Pow.{u1} γ (Group.toDivInvMonoid.{u1} γ _inst_5)))) f n) (Continuous.comp_aestronglyMeasurable.{u2, u1, u1} α γ γ _inst_1 μ _inst_3 _inst_3 (fun (a : γ) => HPow.hPow.{u1, 0, u1} γ Int γ (instHPow.{u1, 0} γ Int (DivInvMonoid.Pow.{u1} γ (Group.toDivInvMonoid.{u1} γ _inst_5))) a n) (fun (x : α) => f x) (continuous_zpow.{u1} γ _inst_3 _inst_5 _inst_6 n) hf))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.mk_zpow MeasureTheory.AEEqFun.mk_zpowₓ'. -/
@[simp]
theorem mk_zpow (f : α → γ) (hf) (n : ℤ) :
    (mk f hf : α →ₘ[μ] γ) ^ n = mk (f ^ n) ((continuous_zpow n).comp_aestronglyMeasurable hf) :=
  rfl
#align measure_theory.ae_eq_fun.mk_zpow MeasureTheory.AEEqFun.mk_zpow

/- warning: measure_theory.ae_eq_fun.coe_fn_zpow -> MeasureTheory.AEEqFun.coeFn_zpow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Group.{u2} γ] [_inst_6 : TopologicalGroup.{u2} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (n : Int), Filter.EventuallyEq.{u1, u2} α γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) (HPow.hPow.{max u1 u2, 0, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) Int (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (instHPow.{max u1 u2, 0} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) Int (MeasureTheory.AEEqFun.instPowInt.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f n)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (α -> γ) Int (α -> γ) (instHPow.{max u1 u2, 0} (α -> γ) Int (Pi.hasPow.{u1, u2, 0} α Int (fun (ᾰ : α) => γ) (fun (i : α) => DivInvMonoid.Pow.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5)))) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) f) n)
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Group.{u1} γ] [_inst_6 : TopologicalGroup.{u1} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (n : Int), Filter.EventuallyEq.{u2, u1} α γ (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 (HPow.hPow.{max u2 u1, 0, max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) Int (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (instHPow.{max u2 u1, 0} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) Int (MeasureTheory.AEEqFun.instPowInt.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f n)) (HPow.hPow.{max u2 u1, 0, max u2 u1} (α -> γ) Int (α -> γ) (instHPow.{max u2 u1, 0} (α -> γ) Int (Pi.instPow.{u2, u1, 0} α Int (fun (ᾰ : α) => γ) (fun (i : α) => DivInvMonoid.Pow.{u1} γ (Group.toDivInvMonoid.{u1} γ _inst_5)))) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 f) n)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_zpow MeasureTheory.AEEqFun.coeFn_zpowₓ'. -/
theorem coeFn_zpow (f : α →ₘ[μ] γ) (n : ℤ) : ⇑(f ^ n) =ᵐ[μ] f ^ n :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_zpow MeasureTheory.AEEqFun.coeFn_zpow

/- warning: measure_theory.ae_eq_fun.zpow_to_germ -> MeasureTheory.AEEqFun.zpow_toGerm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : Group.{u2} γ] [_inst_6 : TopologicalGroup.{u2} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (n : Int), Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 (HPow.hPow.{max u1 u2, 0, max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) Int (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (instHPow.{max u1 u2, 0} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) Int (MeasureTheory.AEEqFun.instPowInt.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f n)) (HPow.hPow.{max u1 u2, 0, max u1 u2} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) Int (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) (instHPow.{max u1 u2, 0} (Filter.Germ.{u1, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) γ) Int (Filter.Germ.hasPow.{u1, 0, u2} α (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) Int γ (DivInvMonoid.Pow.{u2} γ (Group.toDivInvMonoid.{u2} γ _inst_5)))) (MeasureTheory.AEEqFun.toGerm.{u1, u2} α γ _inst_1 μ _inst_3 f) n)
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : Group.{u1} γ] [_inst_6 : TopologicalGroup.{u1} γ _inst_3 _inst_5] (f : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (n : Int), Eq.{max (succ u2) (succ u1)} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α γ _inst_1 μ _inst_3 (HPow.hPow.{max u2 u1, 0, max u2 u1} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) Int (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (instHPow.{max u2 u1, 0} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) Int (MeasureTheory.AEEqFun.instPowInt.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6)) f n)) (HPow.hPow.{max u2 u1, 0, max u2 u1} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) Int (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) (instHPow.{max u2 u1, 0} (Filter.Germ.{u2, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) γ) Int (Filter.Germ.pow.{u2, 0, u1} α (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) Int γ (DivInvMonoid.Pow.{u1} γ (Group.toDivInvMonoid.{u1} γ _inst_5)))) (MeasureTheory.AEEqFun.toGerm.{u2, u1} α γ _inst_1 μ _inst_3 f) n)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.zpow_to_germ MeasureTheory.AEEqFun.zpow_toGermₓ'. -/
@[simp]
theorem zpow_toGerm (f : α →ₘ[μ] γ) (n : ℤ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _
#align measure_theory.ae_eq_fun.zpow_to_germ MeasureTheory.AEEqFun.zpow_toGerm

end Zpow

end Group

instance [AddGroup γ] [TopologicalAddGroup γ] : AddGroup (α →ₘ[μ] γ) :=
  toGerm_injective.AddGroup toGerm zero_toGerm add_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) fun _ _ => smul_toGerm _ _

instance [AddCommGroup γ] [TopologicalAddGroup γ] : AddCommGroup (α →ₘ[μ] γ) :=
  toGerm_injective.AddCommGroup toGerm zero_toGerm add_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) fun _ _ => smul_toGerm _ _

@[to_additive]
instance [Group γ] [TopologicalGroup γ] : Group (α →ₘ[μ] γ) :=
  toGerm_injective.Group _ one_toGerm mul_toGerm inv_toGerm div_toGerm pow_toGerm zpow_toGerm

@[to_additive]
instance [CommGroup γ] [TopologicalGroup γ] : CommGroup (α →ₘ[μ] γ) :=
  toGerm_injective.CommGroup _ one_toGerm mul_toGerm inv_toGerm div_toGerm pow_toGerm zpow_toGerm

section Module

variable {𝕜 : Type _}

instance [Monoid 𝕜] [MulAction 𝕜 γ] [ContinuousConstSMul 𝕜 γ] : MulAction 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.MulAction toGerm smul_toGerm

instance [Monoid 𝕜] [AddMonoid γ] [ContinuousAdd γ] [DistribMulAction 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : DistribMulAction 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.DistribMulAction (toGermAddMonoidHom : (α →ₘ[μ] γ) →+ _) fun c : 𝕜 =>
    smul_toGerm c

instance [Semiring 𝕜] [AddCommMonoid γ] [ContinuousAdd γ] [Module 𝕜 γ] [ContinuousConstSMul 𝕜 γ] :
    Module 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.Module 𝕜 (toGermAddMonoidHom : (α →ₘ[μ] γ) →+ _) smul_toGerm

end Module

open ENNReal

/- warning: measure_theory.ae_eq_fun.lintegral -> MeasureTheory.AEEqFun.lintegral is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1}, (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) -> ENNReal
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1}, (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) -> ENNReal
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.lintegral MeasureTheory.AEEqFun.lintegralₓ'. -/
/-- For `f : α → ℝ≥0∞`, define `∫ [f]` to be `∫ f` -/
def lintegral (f : α →ₘ[μ] ℝ≥0∞) : ℝ≥0∞ :=
  Quotient.liftOn' f (fun f => ∫⁻ a, (f : α → ℝ≥0∞) a ∂μ) fun f g => lintegral_congr_ae
#align measure_theory.ae_eq_fun.lintegral MeasureTheory.AEEqFun.lintegral

/- warning: measure_theory.ae_eq_fun.lintegral_mk -> MeasureTheory.AEEqFun.lintegral_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (f : α -> ENNReal) (hf : MeasureTheory.AEStronglyMeasurable.{u1, 0} α ENNReal ENNReal.topologicalSpace _inst_1 f μ), Eq.{1} ENNReal (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ (MeasureTheory.AEEqFun.mk.{u1, 0} α _inst_1 μ ENNReal ENNReal.topologicalSpace f hf)) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => f a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (f : α -> ENNReal) (hf : MeasureTheory.AEStronglyMeasurable.{u1, 0} α ENNReal ENNReal.instTopologicalSpaceENNReal _inst_1 f μ), Eq.{1} ENNReal (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ (MeasureTheory.AEEqFun.mk.{u1, 0} α _inst_1 μ ENNReal ENNReal.instTopologicalSpaceENNReal f hf)) (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => f a))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.lintegral_mk MeasureTheory.AEEqFun.lintegral_mkₓ'. -/
@[simp]
theorem lintegral_mk (f : α → ℝ≥0∞) (hf) : (mk f hf : α →ₘ[μ] ℝ≥0∞).lintegral = ∫⁻ a, f a ∂μ :=
  rfl
#align measure_theory.ae_eq_fun.lintegral_mk MeasureTheory.AEEqFun.lintegral_mk

/- warning: measure_theory.ae_eq_fun.lintegral_coe_fn -> MeasureTheory.AEEqFun.lintegral_coeFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (f : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => coeFn.{succ u1, succ u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) (fun (_x : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) => α -> ENNReal) (MeasureTheory.AEEqFun.instCoeFun.{u1, 0} α ENNReal _inst_1 μ ENNReal.topologicalSpace) f a)) (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ f)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (f : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ), Eq.{1} ENNReal (MeasureTheory.lintegral.{u1} α _inst_1 μ (fun (a : α) => MeasureTheory.AEEqFun.cast.{u1, 0} α ENNReal _inst_1 μ ENNReal.instTopologicalSpaceENNReal f a)) (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ f)
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.lintegral_coe_fn MeasureTheory.AEEqFun.lintegral_coeFnₓ'. -/
theorem lintegral_coeFn (f : α →ₘ[μ] ℝ≥0∞) : (∫⁻ a, f a ∂μ) = f.lintegral := by
  rw [← lintegral_mk, mk_coe_fn]
#align measure_theory.ae_eq_fun.lintegral_coe_fn MeasureTheory.AEEqFun.lintegral_coeFn

/- warning: measure_theory.ae_eq_fun.lintegral_zero -> MeasureTheory.AEEqFun.lintegral_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1}, Eq.{1} ENNReal (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ (OfNat.ofNat.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) 0 (OfNat.mk.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) 0 (Zero.zero.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) (MeasureTheory.AEEqFun.instZero.{u1, 0} α ENNReal _inst_1 μ ENNReal.topologicalSpace ENNReal.hasZero))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1}, Eq.{1} ENNReal (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ (OfNat.ofNat.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) 0 (Zero.toOfNat0.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) (MeasureTheory.AEEqFun.instZero.{u1, 0} α ENNReal _inst_1 μ ENNReal.instTopologicalSpaceENNReal instENNRealZero)))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.lintegral_zero MeasureTheory.AEEqFun.lintegral_zeroₓ'. -/
@[simp]
theorem lintegral_zero : lintegral (0 : α →ₘ[μ] ℝ≥0∞) = 0 :=
  lintegral_zero
#align measure_theory.ae_eq_fun.lintegral_zero MeasureTheory.AEEqFun.lintegral_zero

/- warning: measure_theory.ae_eq_fun.lintegral_eq_zero_iff -> MeasureTheory.AEEqFun.lintegral_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {f : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ}, Iff (Eq.{1} ENNReal (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ f) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{succ u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) f (OfNat.ofNat.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) 0 (OfNat.mk.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) 0 (Zero.zero.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) (MeasureTheory.AEEqFun.instZero.{u1, 0} α ENNReal _inst_1 μ ENNReal.topologicalSpace ENNReal.hasZero)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {f : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ}, Iff (Eq.{1} ENNReal (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ f) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{succ u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) f (OfNat.ofNat.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) 0 (Zero.toOfNat0.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) (MeasureTheory.AEEqFun.instZero.{u1, 0} α ENNReal _inst_1 μ ENNReal.instTopologicalSpaceENNReal instENNRealZero))))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.lintegral_eq_zero_iff MeasureTheory.AEEqFun.lintegral_eq_zero_iffₓ'. -/
@[simp]
theorem lintegral_eq_zero_iff {f : α →ₘ[μ] ℝ≥0∞} : lintegral f = 0 ↔ f = 0 :=
  induction_on f fun f hf => (lintegral_eq_zero_iff' hf.AEMeasurable).trans mk_eq_mk.symm
#align measure_theory.ae_eq_fun.lintegral_eq_zero_iff MeasureTheory.AEEqFun.lintegral_eq_zero_iff

/- warning: measure_theory.ae_eq_fun.lintegral_add -> MeasureTheory.AEEqFun.lintegral_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (f : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) (g : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ), Eq.{1} ENNReal (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) (instHAdd.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) (MeasureTheory.AEEqFun.instAdd.{u1, 0} α ENNReal _inst_1 μ ENNReal.topologicalSpace (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) ENNReal.continuousAdd)) f g)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ f) (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ g))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} (f : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) (g : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ), Eq.{1} ENNReal (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ (HAdd.hAdd.{u1, u1, u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) (instHAdd.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) (MeasureTheory.AEEqFun.instAdd.{u1, 0} α ENNReal _inst_1 μ ENNReal.instTopologicalSpaceENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))) ENNReal.instContinuousAddENNRealInstTopologicalSpaceENNRealToAddToDistribToNonUnitalNonAssocSemiringToNonAssocSemiringToSemiringToOrderedSemiringToOrderedCommSemiringInstCanonicallyOrderedCommSemiringENNReal)) f g)) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ f) (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ g))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.lintegral_add MeasureTheory.AEEqFun.lintegral_addₓ'. -/
theorem lintegral_add (f g : α →ₘ[μ] ℝ≥0∞) : lintegral (f + g) = lintegral f + lintegral g :=
  induction_on₂ f g fun f hf g hg => by simp [lintegral_add_left' hf.ae_measurable]
#align measure_theory.ae_eq_fun.lintegral_add MeasureTheory.AEEqFun.lintegral_add

/- warning: measure_theory.ae_eq_fun.lintegral_mono -> MeasureTheory.AEEqFun.lintegral_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {f : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ} {g : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ}, (LE.le.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) (Preorder.toHasLe.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.topologicalSpace μ) (MeasureTheory.AEEqFun.instPreorder.{u1, 0} α ENNReal _inst_1 μ ENNReal.topologicalSpace (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))))) f g) -> (LE.le.{0} ENNReal (Preorder.toHasLe.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ f) (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ g))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {f : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ} {g : MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ}, (LE.le.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) (Preorder.toLE.{u1} (MeasureTheory.AEEqFun.{u1, 0} α ENNReal _inst_1 ENNReal.instTopologicalSpaceENNReal μ) (MeasureTheory.AEEqFun.instPreorder.{u1, 0} α ENNReal _inst_1 μ ENNReal.instTopologicalSpaceENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))))) f g) -> (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OmegaCompletePartialOrder.toPartialOrder.{0} ENNReal (CompleteLattice.instOmegaCompletePartialOrder.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))) (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ f) (MeasureTheory.AEEqFun.lintegral.{u1} α _inst_1 μ g))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.lintegral_mono MeasureTheory.AEEqFun.lintegral_monoₓ'. -/
theorem lintegral_mono {f g : α →ₘ[μ] ℝ≥0∞} : f ≤ g → lintegral f ≤ lintegral g :=
  induction_on₂ f g fun f hf g hg hfg => lintegral_mono_ae hfg
#align measure_theory.ae_eq_fun.lintegral_mono MeasureTheory.AEEqFun.lintegral_mono

section Abs

/- warning: measure_theory.ae_eq_fun.coe_fn_abs -> MeasureTheory.AEEqFun.coeFn_abs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {β : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} β] [_inst_6 : Lattice.{u2} β] [_inst_7 : TopologicalLattice.{u2} β _inst_5 _inst_6] [_inst_8 : AddGroup.{u2} β] [_inst_9 : TopologicalAddGroup.{u2} β _inst_5 _inst_8] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_5 μ), Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_5 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_5 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_5) (Abs.abs.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_5 μ) (Neg.toHasAbs.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_5 μ) (MeasureTheory.AEEqFun.instNeg.{u1, u2} α β _inst_1 μ _inst_5 _inst_8 _inst_9) (MeasureTheory.AEEqFun.instSup.{u1, u2} α β _inst_1 μ _inst_5 (Lattice.toSemilatticeSup.{u2} β _inst_6) (TopologicalLattice.to_continuousSup.{u2} β _inst_5 _inst_6 _inst_7))) f)) (fun (x : α) => Abs.abs.{u2} β (Neg.toHasAbs.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_8)) (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β _inst_6))) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_5 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_5 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_5) f x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} {β : Type.{u2}} [_inst_5 : TopologicalSpace.{u2} β] [_inst_6 : Lattice.{u2} β] [_inst_7 : TopologicalLattice.{u2} β _inst_5 _inst_6] [_inst_8 : AddGroup.{u2} β] [_inst_9 : TopologicalAddGroup.{u2} β _inst_5 _inst_8] (f : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_5 μ), Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u1, u2} α β _inst_1 μ _inst_5 (Abs.abs.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_5 μ) (Neg.toHasAbs.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_5 μ) (MeasureTheory.AEEqFun.instNeg.{u1, u2} α β _inst_1 μ _inst_5 _inst_8 _inst_9) (MeasureTheory.AEEqFun.instSup.{u1, u2} α β _inst_1 μ _inst_5 (Lattice.toSemilatticeSup.{u2} β _inst_6) (TopologicalLattice.toContinuousSup.{u2} β _inst_5 _inst_6 _inst_7))) f)) (fun (x : α) => Abs.abs.{u2} β (Neg.toHasAbs.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_8)))) (SemilatticeSup.toSup.{u2} β (Lattice.toSemilatticeSup.{u2} β _inst_6))) (MeasureTheory.AEEqFun.cast.{u1, u2} α β _inst_1 μ _inst_5 f x))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_abs MeasureTheory.AEEqFun.coeFn_absₓ'. -/
theorem coeFn_abs {β} [TopologicalSpace β] [Lattice β] [TopologicalLattice β] [AddGroup β]
    [TopologicalAddGroup β] (f : α →ₘ[μ] β) : ⇑(|f|) =ᵐ[μ] fun x => |f x| :=
  by
  simp_rw [abs_eq_sup_neg]
  filter_upwards [ae_eq_fun.coe_fn_sup f (-f), ae_eq_fun.coe_fn_neg f]with x hx_sup hx_neg
  rw [hx_sup, hx_neg, Pi.neg_apply]
#align measure_theory.ae_eq_fun.coe_fn_abs MeasureTheory.AEEqFun.coeFn_abs

end Abs

section PosPart

variable [LinearOrder γ] [OrderClosedTopology γ] [Zero γ]

#print MeasureTheory.AEEqFun.posPart /-
/-- Positive part of an `ae_eq_fun`. -/
def posPart (f : α →ₘ[μ] γ) : α →ₘ[μ] γ :=
  comp (fun x => max x 0) (continuous_id.max continuous_const) f
#align measure_theory.ae_eq_fun.pos_part MeasureTheory.AEEqFun.posPart
-/

/- warning: measure_theory.ae_eq_fun.pos_part_mk -> MeasureTheory.AEEqFun.posPart_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : LinearOrder.{u2} γ] [_inst_6 : OrderClosedTopology.{u2} γ _inst_3 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_5))))] [_inst_7 : Zero.{u2} γ] (f : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u1, u2} α γ _inst_3 _inst_1 f μ), Eq.{succ (max u1 u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.posPart.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6 _inst_7 (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 f hf)) (MeasureTheory.AEEqFun.mk.{u1, u2} α _inst_1 μ γ _inst_3 (fun (x : α) => LinearOrder.max.{u2} γ _inst_5 (f x) (OfNat.ofNat.{u2} γ 0 (OfNat.mk.{u2} γ 0 (Zero.zero.{u2} γ _inst_7)))) (Continuous.comp_aestronglyMeasurable.{u1, u2, u2} α γ γ _inst_1 μ _inst_3 _inst_3 (fun (b : γ) => LinearOrder.max.{u2} γ _inst_5 (id.{succ u2} γ b) (OfNat.ofNat.{u2} γ 0 (OfNat.mk.{u2} γ 0 (Zero.zero.{u2} γ _inst_7)))) (fun (x : α) => f x) (Continuous.max.{u2, u2} γ γ _inst_3 _inst_5 _inst_6 (id.{succ u2} γ) (fun (a : γ) => OfNat.ofNat.{u2} γ 0 (OfNat.mk.{u2} γ 0 (Zero.zero.{u2} γ _inst_7))) _inst_3 (continuous_id.{u2} γ _inst_3) (continuous_const.{u2, u2} γ γ _inst_3 _inst_3 (OfNat.ofNat.{u2} γ 0 (OfNat.mk.{u2} γ 0 (Zero.zero.{u2} γ _inst_7))))) hf))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : LinearOrder.{u1} γ] [_inst_6 : OrderClosedTopology.{u1} γ _inst_3 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_5)))))] [_inst_7 : Zero.{u1} γ] (f : α -> γ) (hf : MeasureTheory.AEStronglyMeasurable.{u2, u1} α γ _inst_3 _inst_1 f μ), Eq.{max (succ u2) (succ u1)} (MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ) (MeasureTheory.AEEqFun.posPart.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6 _inst_7 (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 f hf)) (MeasureTheory.AEEqFun.mk.{u2, u1} α _inst_1 μ γ _inst_3 (fun (x : α) => Max.max.{u1} γ (LinearOrder.toMax.{u1} γ _inst_5) (f x) (OfNat.ofNat.{u1} γ 0 (Zero.toOfNat0.{u1} γ _inst_7))) (Continuous.comp_aestronglyMeasurable.{u2, u1, u1} α γ γ _inst_1 μ _inst_3 _inst_3 (fun (b : γ) => Max.max.{u1} γ (LinearOrder.toMax.{u1} γ _inst_5) (id.{succ u1} γ b) (OfNat.ofNat.{u1} γ 0 (Zero.toOfNat0.{u1} γ _inst_7))) (fun (x : α) => f x) (Continuous.max.{u1, u1} γ γ _inst_3 _inst_5 _inst_6 (id.{succ u1} γ) (fun (a : γ) => OfNat.ofNat.{u1} γ 0 (Zero.toOfNat0.{u1} γ _inst_7)) _inst_3 (continuous_id.{u1} γ _inst_3) (continuous_const.{u1, u1} γ γ _inst_3 _inst_3 (OfNat.ofNat.{u1} γ 0 (Zero.toOfNat0.{u1} γ _inst_7)))) hf))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.pos_part_mk MeasureTheory.AEEqFun.posPart_mkₓ'. -/
@[simp]
theorem posPart_mk (f : α → γ) (hf) :
    posPart (mk f hf : α →ₘ[μ] γ) =
      mk (fun x => max (f x) 0)
        ((continuous_id.max continuous_const).comp_aestronglyMeasurable hf) :=
  rfl
#align measure_theory.ae_eq_fun.pos_part_mk MeasureTheory.AEEqFun.posPart_mk

/- warning: measure_theory.ae_eq_fun.coe_fn_pos_part -> MeasureTheory.AEEqFun.coeFn_posPart is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] {μ : MeasureTheory.Measure.{u1} α _inst_1} [_inst_3 : TopologicalSpace.{u2} γ] [_inst_5 : LinearOrder.{u2} γ] [_inst_6 : OrderClosedTopology.{u2} γ _inst_3 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_5))))] [_inst_7 : Zero.{u2} γ] (f : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u1, u2} α γ (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) (MeasureTheory.AEEqFun.posPart.{u1, u2} α γ _inst_1 μ _inst_3 _inst_5 _inst_6 _inst_7 f)) (fun (a : α) => LinearOrder.max.{u2} γ _inst_5 (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_3 μ) => α -> γ) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α γ _inst_1 μ _inst_3) f a) (OfNat.ofNat.{u2} γ 0 (OfNat.mk.{u2} γ 0 (Zero.zero.{u2} γ _inst_7))))
but is expected to have type
  forall {α : Type.{u2}} {γ : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] {μ : MeasureTheory.Measure.{u2} α _inst_1} [_inst_3 : TopologicalSpace.{u1} γ] [_inst_5 : LinearOrder.{u1} γ] [_inst_6 : OrderClosedTopology.{u1} γ _inst_3 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_5)))))] [_inst_7 : Zero.{u1} γ] (f : MeasureTheory.AEEqFun.{u2, u1} α γ _inst_1 _inst_3 μ), Filter.EventuallyEq.{u2, u1} α γ (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 (MeasureTheory.AEEqFun.posPart.{u2, u1} α γ _inst_1 μ _inst_3 _inst_5 _inst_6 _inst_7 f)) (fun (a : α) => Max.max.{u1} γ (LinearOrder.toMax.{u1} γ _inst_5) (MeasureTheory.AEEqFun.cast.{u2, u1} α γ _inst_1 μ _inst_3 f a) (OfNat.ofNat.{u1} γ 0 (Zero.toOfNat0.{u1} γ _inst_7)))
Case conversion may be inaccurate. Consider using '#align measure_theory.ae_eq_fun.coe_fn_pos_part MeasureTheory.AEEqFun.coeFn_posPartₓ'. -/
theorem coeFn_posPart (f : α →ₘ[μ] γ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0 :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_pos_part MeasureTheory.AEEqFun.coeFn_posPart

end PosPart

end AeEqFun

end MeasureTheory

namespace ContinuousMap

open MeasureTheory

variable [TopologicalSpace α] [BorelSpace α] (μ)

variable [TopologicalSpace β] [SecondCountableTopologyEither α β] [PseudoMetrizableSpace β]

#print ContinuousMap.toAEEqFun /-
/-- The equivalence class of `μ`-almost-everywhere measurable functions associated to a continuous
map. -/
def toAEEqFun (f : C(α, β)) : α →ₘ[μ] β :=
  AEEqFun.mk f f.Continuous.AEStronglyMeasurable
#align continuous_map.to_ae_eq_fun ContinuousMap.toAEEqFun
-/

/- warning: continuous_map.coe_fn_to_ae_eq_fun -> ContinuousMap.coeFn_toAEEqFun is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : BorelSpace.{u1} α _inst_2 _inst_1] [_inst_4 : TopologicalSpace.{u2} β] [_inst_5 : SecondCountableTopologyEither.{u1, u2} α β _inst_2 _inst_4] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_4] (f : ContinuousMap.{u1, u2} α β _inst_2 _inst_4), Filter.EventuallyEq.{u1, u2} α β (MeasureTheory.Measure.ae.{u1} α _inst_1 μ) (coeFn.{succ (max u1 u2), max (succ u1) (succ u2)} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_4 μ) (fun (_x : MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_4 μ) => α -> β) (MeasureTheory.AEEqFun.instCoeFun.{u1, u2} α β _inst_1 μ _inst_4) (ContinuousMap.toAEEqFun.{u1, u2} α β _inst_1 μ _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (ContinuousMap.{u1, u2} α β _inst_2 _inst_4) (fun (_x : ContinuousMap.{u1, u2} α β _inst_2 _inst_4) => α -> β) (ContinuousMap.hasCoeToFun.{u1, u2} α β _inst_2 _inst_4) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : MeasurableSpace.{u2} α] (μ : MeasureTheory.Measure.{u2} α _inst_1) [_inst_2 : TopologicalSpace.{u2} α] [_inst_3 : BorelSpace.{u2} α _inst_2 _inst_1] [_inst_4 : TopologicalSpace.{u1} β] [_inst_5 : SecondCountableTopologyEither.{u2, u1} α β _inst_2 _inst_4] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u1} β _inst_4] (f : ContinuousMap.{u2, u1} α β _inst_2 _inst_4), Filter.EventuallyEq.{u2, u1} α β (MeasureTheory.Measure.ae.{u2} α _inst_1 μ) (MeasureTheory.AEEqFun.cast.{u2, u1} α β _inst_1 μ _inst_4 (ContinuousMap.toAEEqFun.{u2, u1} α β _inst_1 μ _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (ContinuousMap.{u2, u1} α β _inst_2 _inst_4) α (fun (_x : α) => (fun (x._@.Mathlib.Topology.ContinuousFunction.Basic._hyg.699 : α) => β) _x) (ContinuousMapClass.toFunLike.{max u2 u1, u2, u1} (ContinuousMap.{u2, u1} α β _inst_2 _inst_4) α β _inst_2 _inst_4 (ContinuousMap.instContinuousMapClassContinuousMap.{u2, u1} α β _inst_2 _inst_4)) f)
Case conversion may be inaccurate. Consider using '#align continuous_map.coe_fn_to_ae_eq_fun ContinuousMap.coeFn_toAEEqFunₓ'. -/
theorem coeFn_toAEEqFun (f : C(α, β)) : f.toAEEqFun μ =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _
#align continuous_map.coe_fn_to_ae_eq_fun ContinuousMap.coeFn_toAEEqFun

variable [Group β] [TopologicalGroup β]

/- warning: continuous_map.to_ae_eq_fun_mul_hom -> ContinuousMap.toAEEqFunMulHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : BorelSpace.{u1} α _inst_2 _inst_1] [_inst_4 : TopologicalSpace.{u2} β] [_inst_5 : SecondCountableTopologyEither.{u1, u2} α β _inst_2 _inst_4] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_4] [_inst_7 : Group.{u2} β] [_inst_8 : TopologicalGroup.{u2} β _inst_4 _inst_7], MonoidHom.{max u1 u2, max u1 u2} (ContinuousMap.{u1, u2} α β _inst_2 _inst_4) (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_4 μ) (ContinuousMap.mulOneClass.{u1, u2} α β _inst_2 _inst_4 (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_7))) (TopologicalGroup.to_continuousMul.{u2} β _inst_4 _inst_7 _inst_8)) (Monoid.toMulOneClass.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.instMonoid.{u1, u2} α β _inst_1 μ _inst_4 (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_7)) (TopologicalGroup.to_continuousMul.{u2} β _inst_4 _inst_7 _inst_8)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : BorelSpace.{u1} α _inst_2 _inst_1] [_inst_4 : TopologicalSpace.{u2} β] [_inst_5 : SecondCountableTopologyEither.{u1, u2} α β _inst_2 _inst_4] [_inst_6 : TopologicalSpace.PseudoMetrizableSpace.{u2} β _inst_4] [_inst_7 : Group.{u2} β] [_inst_8 : TopologicalGroup.{u2} β _inst_4 _inst_7], MonoidHom.{max u2 u1, max u2 u1} (ContinuousMap.{u1, u2} α β _inst_2 _inst_4) (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_4 μ) (ContinuousMap.instMulOneClassContinuousMap.{u1, u2} α β _inst_2 _inst_4 (Monoid.toMulOneClass.{u2} β (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_7))) (TopologicalGroup.toContinuousMul.{u2} β _inst_4 _inst_7 _inst_8)) (Monoid.toMulOneClass.{max u1 u2} (MeasureTheory.AEEqFun.{u1, u2} α β _inst_1 _inst_4 μ) (MeasureTheory.AEEqFun.instMonoid.{u1, u2} α β _inst_1 μ _inst_4 (DivInvMonoid.toMonoid.{u2} β (Group.toDivInvMonoid.{u2} β _inst_7)) (TopologicalGroup.toContinuousMul.{u2} β _inst_4 _inst_7 _inst_8)))
Case conversion may be inaccurate. Consider using '#align continuous_map.to_ae_eq_fun_mul_hom ContinuousMap.toAEEqFunMulHomₓ'. -/
/-- The `mul_hom` from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
@[to_additive
      "The `add_hom` from the group of continuous maps from `α` to `β` to the group of\nequivalence classes of `μ`-almost-everywhere measurable functions."]
def toAEEqFunMulHom : C(α, β) →* α →ₘ[μ] β
    where
  toFun := ContinuousMap.toAEEqFun μ
  map_one' := rfl
  map_mul' f g :=
    AEEqFun.mk_mul_mk _ _ f.Continuous.AEStronglyMeasurable g.Continuous.AEStronglyMeasurable
#align continuous_map.to_ae_eq_fun_mul_hom ContinuousMap.toAEEqFunMulHom
#align continuous_map.to_ae_eq_fun_add_hom ContinuousMap.toAEEqFunAddHom

variable {𝕜 : Type _} [Semiring 𝕜]

variable [TopologicalSpace γ] [PseudoMetrizableSpace γ] [AddCommGroup γ] [Module 𝕜 γ]
  [TopologicalAddGroup γ] [ContinuousConstSMul 𝕜 γ] [SecondCountableTopologyEither α γ]

/- warning: continuous_map.to_ae_eq_fun_linear_map -> ContinuousMap.toAEEqFunLinearMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : BorelSpace.{u1} α _inst_2 _inst_1] {𝕜 : Type.{u3}} [_inst_9 : Semiring.{u3} 𝕜] [_inst_10 : TopologicalSpace.{u2} γ] [_inst_11 : TopologicalSpace.PseudoMetrizableSpace.{u2} γ _inst_10] [_inst_12 : AddCommGroup.{u2} γ] [_inst_13 : Module.{u3, u2} 𝕜 γ _inst_9 (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12)] [_inst_14 : TopologicalAddGroup.{u2} γ _inst_10 (AddCommGroup.toAddGroup.{u2} γ _inst_12)] [_inst_15 : ContinuousConstSMul.{u3, u2} 𝕜 γ _inst_10 (SMulZeroClass.toHasSmul.{u3, u2} 𝕜 γ (AddZeroClass.toHasZero.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12)))) (SMulWithZero.toSmulZeroClass.{u3, u2} 𝕜 γ (MulZeroClass.toHasZero.{u3} 𝕜 (MulZeroOneClass.toMulZeroClass.{u3} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u3} 𝕜 (Semiring.toMonoidWithZero.{u3} 𝕜 _inst_9)))) (AddZeroClass.toHasZero.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12)))) (MulActionWithZero.toSMulWithZero.{u3, u2} 𝕜 γ (Semiring.toMonoidWithZero.{u3} 𝕜 _inst_9) (AddZeroClass.toHasZero.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12)))) (Module.toMulActionWithZero.{u3, u2} 𝕜 γ _inst_9 (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12) _inst_13))))] [_inst_16 : SecondCountableTopologyEither.{u1, u2} α γ _inst_2 _inst_10], LinearMap.{u3, u3, max u1 u2, max u1 u2} 𝕜 𝕜 _inst_9 _inst_9 (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 _inst_9)) (ContinuousMap.{u1, u2} α γ _inst_2 _inst_10) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_10 μ) (ContinuousMap.addCommMonoid.{u1, u2} α γ _inst_2 _inst_10 (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12) (ContinuousMap.toAEEqFunLinearMap._proof_1.{u2} γ _inst_10 _inst_12 _inst_14)) (MeasureTheory.AEEqFun.instAddCommMonoid.{u1, u2} α γ _inst_1 μ _inst_10 (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12) (ContinuousMap.toAEEqFunLinearMap._proof_2.{u2} γ _inst_10 _inst_12 _inst_14)) (ContinuousMap.module.{u1, u3, u2} α _inst_2 𝕜 γ _inst_10 _inst_9 (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12) (ContinuousMap.toAEEqFunLinearMap._proof_3.{u2} γ _inst_10 _inst_12 _inst_14) _inst_13 _inst_15) (MeasureTheory.AEEqFun.instModule.{u1, u2, u3} α γ _inst_1 μ _inst_10 𝕜 _inst_9 (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12) (ContinuousMap.toAEEqFunLinearMap._proof_4.{u2} γ _inst_10 _inst_12 _inst_14) _inst_13 _inst_15)
but is expected to have type
  forall {α : Type.{u1}} {γ : Type.{u2}} [_inst_1 : MeasurableSpace.{u1} α] (μ : MeasureTheory.Measure.{u1} α _inst_1) [_inst_2 : TopologicalSpace.{u1} α] [_inst_3 : BorelSpace.{u1} α _inst_2 _inst_1] {𝕜 : Type.{u3}} [_inst_9 : Semiring.{u3} 𝕜] [_inst_10 : TopologicalSpace.{u2} γ] [_inst_11 : TopologicalSpace.PseudoMetrizableSpace.{u2} γ _inst_10] [_inst_12 : AddCommGroup.{u2} γ] [_inst_13 : Module.{u3, u2} 𝕜 γ _inst_9 (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12)] [_inst_14 : TopologicalAddGroup.{u2} γ _inst_10 (AddCommGroup.toAddGroup.{u2} γ _inst_12)] [_inst_15 : ContinuousConstSMul.{u3, u2} 𝕜 γ _inst_10 (SMulZeroClass.toSMul.{u3, u2} 𝕜 γ (NegZeroClass.toZero.{u2} γ (SubNegZeroMonoid.toNegZeroClass.{u2} γ (SubtractionMonoid.toSubNegZeroMonoid.{u2} γ (SubtractionCommMonoid.toSubtractionMonoid.{u2} γ (AddCommGroup.toDivisionAddCommMonoid.{u2} γ _inst_12))))) (SMulWithZero.toSMulZeroClass.{u3, u2} 𝕜 γ (MonoidWithZero.toZero.{u3} 𝕜 (Semiring.toMonoidWithZero.{u3} 𝕜 _inst_9)) (NegZeroClass.toZero.{u2} γ (SubNegZeroMonoid.toNegZeroClass.{u2} γ (SubtractionMonoid.toSubNegZeroMonoid.{u2} γ (SubtractionCommMonoid.toSubtractionMonoid.{u2} γ (AddCommGroup.toDivisionAddCommMonoid.{u2} γ _inst_12))))) (MulActionWithZero.toSMulWithZero.{u3, u2} 𝕜 γ (Semiring.toMonoidWithZero.{u3} 𝕜 _inst_9) (NegZeroClass.toZero.{u2} γ (SubNegZeroMonoid.toNegZeroClass.{u2} γ (SubtractionMonoid.toSubNegZeroMonoid.{u2} γ (SubtractionCommMonoid.toSubtractionMonoid.{u2} γ (AddCommGroup.toDivisionAddCommMonoid.{u2} γ _inst_12))))) (Module.toMulActionWithZero.{u3, u2} 𝕜 γ _inst_9 (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12) _inst_13))))] [_inst_16 : SecondCountableTopologyEither.{u1, u2} α γ _inst_2 _inst_10], LinearMap.{u3, u3, max u2 u1, max u2 u1} 𝕜 𝕜 _inst_9 _inst_9 (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 _inst_9)) (ContinuousMap.{u1, u2} α γ _inst_2 _inst_10) (MeasureTheory.AEEqFun.{u1, u2} α γ _inst_1 _inst_10 μ) (ContinuousMap.instAddCommMonoidContinuousMap.{u1, u2} α γ _inst_2 _inst_10 (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12) (TopologicalAddGroup.toContinuousAdd.{u2} γ _inst_10 (AddCommGroup.toAddGroup.{u2} γ _inst_12) _inst_14)) (MeasureTheory.AEEqFun.instAddCommMonoid.{u1, u2} α γ _inst_1 μ _inst_10 (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12) (TopologicalAddGroup.toContinuousAdd.{u2} γ _inst_10 (AddCommGroup.toAddGroup.{u2} γ _inst_12) _inst_14)) (ContinuousMap.module.{u1, u3, u2} α _inst_2 𝕜 γ _inst_10 _inst_9 (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12) (TopologicalAddGroup.toContinuousAdd.{u2} γ _inst_10 (AddCommGroup.toAddGroup.{u2} γ _inst_12) _inst_14) _inst_13 _inst_15) (MeasureTheory.AEEqFun.instModule.{u1, u2, u3} α γ _inst_1 μ _inst_10 𝕜 _inst_9 (AddCommGroup.toAddCommMonoid.{u2} γ _inst_12) (TopologicalAddGroup.toContinuousAdd.{u2} γ _inst_10 (AddCommGroup.toAddGroup.{u2} γ _inst_12) _inst_14) _inst_13 _inst_15)
Case conversion may be inaccurate. Consider using '#align continuous_map.to_ae_eq_fun_linear_map ContinuousMap.toAEEqFunLinearMapₓ'. -/
/-- The linear map from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
def toAEEqFunLinearMap : C(α, γ) →ₗ[𝕜] α →ₘ[μ] γ :=
  { toAEEqFunAddHom μ with
    map_smul' := fun c f => AEEqFun.smul_mk c f f.Continuous.AEStronglyMeasurable }
#align continuous_map.to_ae_eq_fun_linear_map ContinuousMap.toAEEqFunLinearMap

end ContinuousMap

-- Guard against import creep
assert_not_exists inner_product_space

