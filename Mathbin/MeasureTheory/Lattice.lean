/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import MeasureTheory.Measure.AeMeasurable

#align_import measure_theory.lattice from "leanprover-community/mathlib"@"781cb2eed038c4caf53bdbd8d20a95e5822d77df"

/-!
# Typeclasses for measurability of lattice operations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define classes `has_measurable_sup` and `has_measurable_inf` and prove dot-style
lemmas (`measurable.sup`, `ae_measurable.sup` etc). For binary operations we define two typeclasses:

- `has_measurable_sup` says that both left and right sup are measurable;
- `has_measurable_sup₂` says that `λ p : α × α, p.1 ⊔ p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `has_measurable_sup₂`
etc require `α` to have a second countable topology.

For instances relating, e.g., `has_continuous_sup` to `has_measurable_sup` see file
`measure_theory.borel_space`.

## Tags

measurable function, lattice operation

-/


open MeasureTheory

#print MeasurableSup /-
/-- We say that a type `has_measurable_sup` if `((⊔) c)` and `(⊔ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (⊔)` see `has_measurable_sup₂`. -/
class MeasurableSup (M : Type _) [MeasurableSpace M] [Sup M] : Prop where
  measurable_const_sup : ∀ c : M, Measurable ((· ⊔ ·) c)
  measurable_sup_const : ∀ c : M, Measurable (· ⊔ c)
#align has_measurable_sup MeasurableSup
-/

#print MeasurableSup₂ /-
/-- We say that a type `has_measurable_sup₂` if `uncurry (⊔)` is a measurable functions.
For a typeclass assuming measurability of `((⊔) c)` and `(⊔ c)` see `has_measurable_sup`. -/
class MeasurableSup₂ (M : Type _) [MeasurableSpace M] [Sup M] : Prop where
  measurable_sup : Measurable fun p : M × M => p.1 ⊔ p.2
#align has_measurable_sup₂ MeasurableSup₂
-/

export MeasurableSup₂ (measurable_sup)

export MeasurableSup (measurable_const_sup measurable_sup_const)

#print MeasurableInf /-
/-- We say that a type `has_measurable_inf` if `((⊓) c)` and `(⊓ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (⊓)` see `has_measurable_inf₂`. -/
class MeasurableInf (M : Type _) [MeasurableSpace M] [Inf M] : Prop where
  measurable_const_inf : ∀ c : M, Measurable ((· ⊓ ·) c)
  measurable_inf_const : ∀ c : M, Measurable (· ⊓ c)
#align has_measurable_inf MeasurableInf
-/

#print MeasurableInf₂ /-
/-- We say that a type `has_measurable_inf₂` if `uncurry (⊔)` is a measurable functions.
For a typeclass assuming measurability of `((⊔) c)` and `(⊔ c)` see `has_measurable_inf`. -/
class MeasurableInf₂ (M : Type _) [MeasurableSpace M] [Inf M] : Prop where
  measurable_inf : Measurable fun p : M × M => p.1 ⊓ p.2
#align has_measurable_inf₂ MeasurableInf₂
-/

export MeasurableInf₂ (measurable_inf)

export MeasurableInf (measurable_const_inf measurable_inf_const)

variable {M : Type _} [MeasurableSpace M]

section OrderDual

instance (priority := 100) [Inf M] [MeasurableInf M] : MeasurableSup Mᵒᵈ :=
  ⟨@measurable_const_inf M _ _ _, @measurable_inf_const M _ _ _⟩

instance (priority := 100) [Sup M] [MeasurableSup M] : MeasurableInf Mᵒᵈ :=
  ⟨@measurable_const_sup M _ _ _, @measurable_sup_const M _ _ _⟩

instance (priority := 100) [Inf M] [MeasurableInf₂ M] : MeasurableSup₂ Mᵒᵈ :=
  ⟨@measurable_inf M _ _ _⟩

instance (priority := 100) [Sup M] [MeasurableSup₂ M] : MeasurableInf₂ Mᵒᵈ :=
  ⟨@measurable_sup M _ _ _⟩

end OrderDual

variable {α : Type _} {m : MeasurableSpace α} {μ : Measure α} {f g : α → M}

section Sup

variable [Sup M]

section MeasurableSup

variable [MeasurableSup M]

#print Measurable.const_sup /-
@[measurability]
theorem Measurable.const_sup (hf : Measurable f) (c : M) : Measurable fun x => c ⊔ f x :=
  (measurable_const_sup c).comp hf
#align measurable.const_sup Measurable.const_sup
-/

#print AEMeasurable.const_sup /-
@[measurability]
theorem AEMeasurable.const_sup (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c ⊔ f x) μ :=
  (MeasurableSup.measurable_const_sup c).comp_aemeasurable hf
#align ae_measurable.const_sup AEMeasurable.const_sup
-/

#print Measurable.sup_const /-
@[measurability]
theorem Measurable.sup_const (hf : Measurable f) (c : M) : Measurable fun x => f x ⊔ c :=
  (measurable_sup_const c).comp hf
#align measurable.sup_const Measurable.sup_const
-/

#print AEMeasurable.sup_const /-
@[measurability]
theorem AEMeasurable.sup_const (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x ⊔ c) μ :=
  (measurable_sup_const c).comp_aemeasurable hf
#align ae_measurable.sup_const AEMeasurable.sup_const
-/

end MeasurableSup

section MeasurableSup₂

variable [MeasurableSup₂ M]

#print Measurable.sup' /-
@[measurability]
theorem Measurable.sup' (hf : Measurable f) (hg : Measurable g) : Measurable (f ⊔ g) :=
  measurable_sup.comp (hf.prod_mk hg)
#align measurable.sup' Measurable.sup'
-/

#print Measurable.sup /-
@[measurability]
theorem Measurable.sup (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a ⊔ g a :=
  measurable_sup.comp (hf.prod_mk hg)
#align measurable.sup Measurable.sup
-/

#print AEMeasurable.sup' /-
@[measurability]
theorem AEMeasurable.sup' (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f ⊔ g) μ :=
  measurable_sup.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.sup' AEMeasurable.sup'
-/

#print AEMeasurable.sup /-
@[measurability]
theorem AEMeasurable.sup (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a ⊔ g a) μ :=
  measurable_sup.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.sup AEMeasurable.sup
-/

#print MeasurableSup₂.toMeasurableSup /-
instance (priority := 100) MeasurableSup₂.toMeasurableSup : MeasurableSup M :=
  ⟨fun c => measurable_const.sup measurable_id, fun c => measurable_id.sup measurable_const⟩
#align has_measurable_sup₂.to_has_measurable_sup MeasurableSup₂.toMeasurableSup
-/

end MeasurableSup₂

end Sup

section Inf

variable [Inf M]

section MeasurableInf

variable [MeasurableInf M]

#print Measurable.const_inf /-
@[measurability]
theorem Measurable.const_inf (hf : Measurable f) (c : M) : Measurable fun x => c ⊓ f x :=
  (measurable_const_inf c).comp hf
#align measurable.const_inf Measurable.const_inf
-/

#print AEMeasurable.const_inf /-
@[measurability]
theorem AEMeasurable.const_inf (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c ⊓ f x) μ :=
  (MeasurableInf.measurable_const_inf c).comp_aemeasurable hf
#align ae_measurable.const_inf AEMeasurable.const_inf
-/

#print Measurable.inf_const /-
@[measurability]
theorem Measurable.inf_const (hf : Measurable f) (c : M) : Measurable fun x => f x ⊓ c :=
  (measurable_inf_const c).comp hf
#align measurable.inf_const Measurable.inf_const
-/

#print AEMeasurable.inf_const /-
@[measurability]
theorem AEMeasurable.inf_const (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x ⊓ c) μ :=
  (measurable_inf_const c).comp_aemeasurable hf
#align ae_measurable.inf_const AEMeasurable.inf_const
-/

end MeasurableInf

section MeasurableInf₂

variable [MeasurableInf₂ M]

#print Measurable.inf' /-
@[measurability]
theorem Measurable.inf' (hf : Measurable f) (hg : Measurable g) : Measurable (f ⊓ g) :=
  measurable_inf.comp (hf.prod_mk hg)
#align measurable.inf' Measurable.inf'
-/

#print Measurable.inf /-
@[measurability]
theorem Measurable.inf (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a ⊓ g a :=
  measurable_inf.comp (hf.prod_mk hg)
#align measurable.inf Measurable.inf
-/

#print AEMeasurable.inf' /-
@[measurability]
theorem AEMeasurable.inf' (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f ⊓ g) μ :=
  measurable_inf.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.inf' AEMeasurable.inf'
-/

#print AEMeasurable.inf /-
@[measurability]
theorem AEMeasurable.inf (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a ⊓ g a) μ :=
  measurable_inf.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.inf AEMeasurable.inf
-/

#print MeasurableInf₂.to_hasMeasurableInf /-
instance (priority := 100) MeasurableInf₂.to_hasMeasurableInf : MeasurableInf M :=
  ⟨fun c => measurable_const.inf measurable_id, fun c => measurable_id.inf measurable_const⟩
#align has_measurable_inf₂.to_has_measurable_inf MeasurableInf₂.to_hasMeasurableInf
-/

end MeasurableInf₂

end Inf

section SemilatticeSup

open Finset

variable {δ : Type _} [MeasurableSpace δ] [SemilatticeSup α] [MeasurableSup₂ α]

#print Finset.measurable_sup' /-
@[measurability]
theorem Finset.measurable_sup' {ι : Type _} {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀ n ∈ s, Measurable (f n)) : Measurable (s.sup' hs f) :=
  Finset.sup'_induction hs _ (fun f hf g hg => hf.sup hg) fun n hn => hf n hn
#align finset.measurable_sup' Finset.measurable_sup'
-/

#print Finset.measurable_range_sup' /-
@[measurability]
theorem Finset.measurable_range_sup' {f : ℕ → δ → α} {n : ℕ} (hf : ∀ k ≤ n, Measurable (f k)) :
    Measurable ((range (n + 1)).sup' nonempty_range_succ f) :=
  by
  simp_rw [← Nat.lt_succ_iff] at hf
  refine' Finset.measurable_sup' _ _
  simpa [Finset.mem_range]
#align finset.measurable_range_sup' Finset.measurable_range_sup'
-/

#print Finset.measurable_range_sup'' /-
@[measurability]
theorem Finset.measurable_range_sup'' {f : ℕ → δ → α} {n : ℕ} (hf : ∀ k ≤ n, Measurable (f k)) :
    Measurable fun x => (range (n + 1)).sup' nonempty_range_succ fun k => f k x :=
  by
  convert Finset.measurable_range_sup' hf
  ext x
  simp
#align finset.measurable_range_sup'' Finset.measurable_range_sup''
-/

end SemilatticeSup

