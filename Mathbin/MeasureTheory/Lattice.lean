/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.lattice
! leanprover-community/mathlib commit 0743cc5d9d86bcd1bba10f480e948a257d65056f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.AeMeasurable

/-!
# Typeclasses for measurability of lattice operations

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

/-- We say that a type `has_measurable_sup` if `((⊔) c)` and `(⊔ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (⊔)` see `has_measurable_sup₂`. -/
class HasMeasurableSup (M : Type _) [MeasurableSpace M] [HasSup M] : Prop where
  measurableConstSup : ∀ c : M, Measurable ((· ⊔ ·) c)
  measurableSupConst : ∀ c : M, Measurable (· ⊔ c)
#align has_measurable_sup HasMeasurableSup

/-- We say that a type `has_measurable_sup₂` if `uncurry (⊔)` is a measurable functions.
For a typeclass assuming measurability of `((⊔) c)` and `(⊔ c)` see `has_measurable_sup`. -/
class HasMeasurableSup₂ (M : Type _) [MeasurableSpace M] [HasSup M] : Prop where
  measurableSup : Measurable fun p : M × M => p.1 ⊔ p.2
#align has_measurable_sup₂ HasMeasurableSup₂

export HasMeasurableSup₂ (measurableSup)

export HasMeasurableSup (measurableConstSup measurableSupConst)

/-- We say that a type `has_measurable_inf` if `((⊓) c)` and `(⊓ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (⊓)` see `has_measurable_inf₂`. -/
class HasMeasurableInf (M : Type _) [MeasurableSpace M] [HasInf M] : Prop where
  measurableConstInf : ∀ c : M, Measurable ((· ⊓ ·) c)
  measurableInfConst : ∀ c : M, Measurable (· ⊓ c)
#align has_measurable_inf HasMeasurableInf

/-- We say that a type `has_measurable_inf₂` if `uncurry (⊔)` is a measurable functions.
For a typeclass assuming measurability of `((⊔) c)` and `(⊔ c)` see `has_measurable_inf`. -/
class HasMeasurableInf₂ (M : Type _) [MeasurableSpace M] [HasInf M] : Prop where
  measurableInf : Measurable fun p : M × M => p.1 ⊓ p.2
#align has_measurable_inf₂ HasMeasurableInf₂

export HasMeasurableInf₂ (measurableInf)

export HasMeasurableInf (measurableConstInf measurableInfConst)

variable {M : Type _} [MeasurableSpace M]

section OrderDual

instance (priority := 100) [HasInf M] [HasMeasurableInf M] : HasMeasurableSup Mᵒᵈ :=
  ⟨@measurableConstInf M _ _ _, @measurableInfConst M _ _ _⟩

instance (priority := 100) [HasSup M] [HasMeasurableSup M] : HasMeasurableInf Mᵒᵈ :=
  ⟨@measurableConstSup M _ _ _, @measurableSupConst M _ _ _⟩

instance (priority := 100) [HasInf M] [HasMeasurableInf₂ M] : HasMeasurableSup₂ Mᵒᵈ :=
  ⟨@measurableInf M _ _ _⟩

instance (priority := 100) [HasSup M] [HasMeasurableSup₂ M] : HasMeasurableInf₂ Mᵒᵈ :=
  ⟨@measurableSup M _ _ _⟩

end OrderDual

variable {α : Type _} {m : MeasurableSpace α} {μ : Measure α} {f g : α → M}

include m

section Sup

variable [HasSup M]

section MeasurableSup

variable [HasMeasurableSup M]

@[measurability]
theorem Measurable.constSup (hf : Measurable f) (c : M) : Measurable fun x => c ⊔ f x :=
  (measurableConstSup c).comp hf
#align measurable.const_sup Measurable.constSup

@[measurability]
theorem AeMeasurable.constSup (hf : AeMeasurable f μ) (c : M) : AeMeasurable (fun x => c ⊔ f x) μ :=
  (HasMeasurableSup.measurableConstSup c).compAeMeasurable hf
#align ae_measurable.const_sup AeMeasurable.constSup

@[measurability]
theorem Measurable.supConst (hf : Measurable f) (c : M) : Measurable fun x => f x ⊔ c :=
  (measurableSupConst c).comp hf
#align measurable.sup_const Measurable.supConst

@[measurability]
theorem AeMeasurable.supConst (hf : AeMeasurable f μ) (c : M) : AeMeasurable (fun x => f x ⊔ c) μ :=
  (measurableSupConst c).compAeMeasurable hf
#align ae_measurable.sup_const AeMeasurable.supConst

end MeasurableSup

section MeasurableSup₂

variable [HasMeasurableSup₂ M]

@[measurability]
theorem Measurable.sup' (hf : Measurable f) (hg : Measurable g) : Measurable (f ⊔ g) :=
  measurableSup.comp (hf.prod_mk hg)
#align measurable.sup' Measurable.sup'

@[measurability]
theorem Measurable.sup (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a ⊔ g a :=
  measurableSup.comp (hf.prod_mk hg)
#align measurable.sup Measurable.sup

@[measurability]
theorem AeMeasurable.sup' (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (f ⊔ g) μ :=
  measurableSup.compAeMeasurable (hf.prod_mk hg)
#align ae_measurable.sup' AeMeasurable.sup'

@[measurability]
theorem AeMeasurable.sup (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (fun a => f a ⊔ g a) μ :=
  measurableSup.compAeMeasurable (hf.prod_mk hg)
#align ae_measurable.sup AeMeasurable.sup

omit m

instance (priority := 100) HasMeasurableSup₂.toHasMeasurableSup : HasMeasurableSup M :=
  ⟨fun c => measurableConst.sup measurableId, fun c => measurableId.sup measurableConst⟩
#align has_measurable_sup₂.to_has_measurable_sup HasMeasurableSup₂.toHasMeasurableSup

include m

end MeasurableSup₂

end Sup

section Inf

variable [HasInf M]

section MeasurableInf

variable [HasMeasurableInf M]

@[measurability]
theorem Measurable.constInf (hf : Measurable f) (c : M) : Measurable fun x => c ⊓ f x :=
  (measurableConstInf c).comp hf
#align measurable.const_inf Measurable.constInf

@[measurability]
theorem AeMeasurable.constInf (hf : AeMeasurable f μ) (c : M) : AeMeasurable (fun x => c ⊓ f x) μ :=
  (HasMeasurableInf.measurableConstInf c).compAeMeasurable hf
#align ae_measurable.const_inf AeMeasurable.constInf

@[measurability]
theorem Measurable.infConst (hf : Measurable f) (c : M) : Measurable fun x => f x ⊓ c :=
  (measurableInfConst c).comp hf
#align measurable.inf_const Measurable.infConst

@[measurability]
theorem AeMeasurable.infConst (hf : AeMeasurable f μ) (c : M) : AeMeasurable (fun x => f x ⊓ c) μ :=
  (measurableInfConst c).compAeMeasurable hf
#align ae_measurable.inf_const AeMeasurable.infConst

end MeasurableInf

section MeasurableInf₂

variable [HasMeasurableInf₂ M]

@[measurability]
theorem Measurable.inf' (hf : Measurable f) (hg : Measurable g) : Measurable (f ⊓ g) :=
  measurableInf.comp (hf.prod_mk hg)
#align measurable.inf' Measurable.inf'

@[measurability]
theorem Measurable.inf (hf : Measurable f) (hg : Measurable g) : Measurable fun a => f a ⊓ g a :=
  measurableInf.comp (hf.prod_mk hg)
#align measurable.inf Measurable.inf

@[measurability]
theorem AeMeasurable.inf' (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (f ⊓ g) μ :=
  measurableInf.compAeMeasurable (hf.prod_mk hg)
#align ae_measurable.inf' AeMeasurable.inf'

@[measurability]
theorem AeMeasurable.inf (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
    AeMeasurable (fun a => f a ⊓ g a) μ :=
  measurableInf.compAeMeasurable (hf.prod_mk hg)
#align ae_measurable.inf AeMeasurable.inf

omit m

instance (priority := 100) HasMeasurableInf₂.toHasMeasurableInf : HasMeasurableInf M :=
  ⟨fun c => measurableConst.inf measurableId, fun c => measurableId.inf measurableConst⟩
#align has_measurable_inf₂.to_has_measurable_inf HasMeasurableInf₂.toHasMeasurableInf

include m

end MeasurableInf₂

end Inf

section SemilatticeSup

open Finset

variable {δ : Type _} [MeasurableSpace δ] [SemilatticeSup α] [HasMeasurableSup₂ α]

@[measurability]
theorem Finset.measurableSup' {ι : Type _} {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀ n ∈ s, Measurable (f n)) : Measurable (s.sup' hs f) :=
  Finset.sup'_induction hs _ (fun f hf g hg => hf.sup hg) fun n hn => hf n hn
#align finset.measurable_sup' Finset.measurableSup'

@[measurability]
theorem Finset.measurableRangeSup' {f : ℕ → δ → α} {n : ℕ} (hf : ∀ k ≤ n, Measurable (f k)) :
    Measurable ((range (n + 1)).sup' nonempty_range_succ f) := by
  simp_rw [← Nat.lt_succ_iff] at hf
  refine' Finset.measurableSup' _ _
  simpa [Finset.mem_range]
#align finset.measurable_range_sup' Finset.measurableRangeSup'

@[measurability]
theorem Finset.measurableRangeSup'' {f : ℕ → δ → α} {n : ℕ} (hf : ∀ k ≤ n, Measurable (f k)) :
    Measurable fun x => (range (n + 1)).sup' nonempty_range_succ fun k => f k x := by
  convert Finset.measurableRangeSup' hf
  ext x
  simp
#align finset.measurable_range_sup'' Finset.measurableRangeSup''

end SemilatticeSup

