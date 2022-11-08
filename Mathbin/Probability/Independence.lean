/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.Algebra.BigOperators.Intervals
import Mathbin.MeasureTheory.Constructions.Pi

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → measurable_space Ω` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `measurable_space.comap f m`.

## Main statements

* `Indep_sets.Indep`: if π-systems are independent as sets of sets, then the
  measurable space structures they generate are independent.
* `indep_sets.indep`: variant with two π-systems.
* `measure_zero_or_one_of_measurable_set_limsup_at_top`: Kolmogorov's 0-1 law. Any set which is
  measurable with respect to the tail σ-algebra `limsup s at_top` of an independent sequence of
  σ-algebras `s` has probability 0 or 1.

## Implementation notes

We provide one main definition of independence:
* `Indep_sets`: independence of a family of sets of sets `pi : ι → set (set Ω)`.
Three other independence notions are defined using `Indep_sets`:
* `Indep`: independence of a family of measurable space structures `m : ι → measurable_space Ω`,
* `Indep_set`: independence of a family of sets `s : ι → set Ω`,
* `Indep_fun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), measurable_space (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without a capital letter, for example `indep_fun` is the version of `Indep_fun`
for two functions.

The definition of independence for `Indep_sets` uses finite sets (`finset`). An alternative and
equivalent way of defining independence would have been to use countable sets.
TODO: prove that equivalence.

Most of the definitions and lemma in this file list all variables instead of using the `variables`
keyword at the beginning of a section, for example
`lemma indep.symm {Ω} {m₁ m₂ : measurable_space Ω} [measurable_space Ω] {μ : measure Ω} ...` .
This is intentional, to be able to control the order of the `measurable_space` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`[measurable_space Ω]`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
Part A, Chapter 4.
-/


open MeasureTheory MeasurableSpace

open BigOperators MeasureTheory Ennreal

namespace ProbabilityTheory

variable {Ω ι : Type _}

section Definitions

/-- A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def IndepSets [MeasurableSpace Ω] (π : ι → Set (Set Ω)) (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) :
    Prop :=
  ∀ (s : Finset ι) {f : ι → Set Ω} (H : ∀ i, i ∈ s → f i ∈ π i), μ (⋂ i ∈ s, f i) = ∏ i in s, μ (f i)

/- warning: probability_theory.indep_sets clashes with probability_theory.Indep_sets -> ProbabilityTheory.IndepSets
warning: probability_theory.indep_sets -> ProbabilityTheory.IndepSets is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u_1}} [_inst_1 : MeasurableSpace.{u_1} Ω], (Set.{u_1} (Set.{u_1} Ω)) -> (Set.{u_1} (Set.{u_1} Ω)) -> (autoParam'.{succ u_1} (MeasureTheory.Measure.{u_1} Ω _inst_1) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 118 (OfNat.mk.{0} Nat 118 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 108 (OfNat.mk.{0} Nat 108 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 117 (OfNat.mk.{0} Nat 117 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 109 (OfNat.mk.{0} Nat 109 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 95 (OfNat.mk.{0} Nat 95 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 109 (OfNat.mk.{0} Nat 109 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 115 (OfNat.mk.{0} Nat 115 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 117 (OfNat.mk.{0} Nat 117 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 114 (OfNat.mk.{0} Nat 114 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 95 (OfNat.mk.{0} Nat 95 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 104 (OfNat.mk.{0} Nat 104 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 114 (OfNat.mk.{0} Nat 114 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 121 (OfNat.mk.{0} Nat 121 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) Name.anonymous))) -> Prop
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align probability_theory.indep_sets ProbabilityTheory.IndepSetsₓ'. -/
/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def IndepSets [MeasurableSpace Ω] (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) :
    Prop :=
  ∀ t1 t2 : Set Ω, t1 ∈ s1 → t2 ∈ s2 → μ (t1 ∩ t2) = μ t1 * μ t2

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → measurable_space Ω` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def IndepCat (m : ι → MeasurableSpace Ω) [MeasurableSpace Ω]
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  IndepSets (fun x => { s | measurable_set[m x] s }) μ

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def Indep (m₁ m₂ : MeasurableSpace Ω) [MeasurableSpace Ω]
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  IndepSets { s | measurable_set[m₁] s } { s | measurable_set[m₂] s } μ

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def IndepSet [MeasurableSpace Ω] (s : ι → Set Ω) (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  IndepCat (fun i => generateFrom {s i}) μ

/- warning: probability_theory.indep_set clashes with probability_theory.Indep_set -> ProbabilityTheory.IndepSet
warning: probability_theory.indep_set -> ProbabilityTheory.IndepSet is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u_1}} [_inst_1 : MeasurableSpace.{u_1} Ω], (Set.{u_1} Ω) -> (Set.{u_1} Ω) -> (autoParam'.{succ u_1} (MeasureTheory.Measure.{u_1} Ω _inst_1) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 118 (OfNat.mk.{0} Nat 118 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 108 (OfNat.mk.{0} Nat 108 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 117 (OfNat.mk.{0} Nat 117 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 109 (OfNat.mk.{0} Nat 109 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 95 (OfNat.mk.{0} Nat 95 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 109 (OfNat.mk.{0} Nat 109 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 115 (OfNat.mk.{0} Nat 115 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 117 (OfNat.mk.{0} Nat 117 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 114 (OfNat.mk.{0} Nat 114 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 95 (OfNat.mk.{0} Nat 95 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 104 (OfNat.mk.{0} Nat 104 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 114 (OfNat.mk.{0} Nat 114 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 121 (OfNat.mk.{0} Nat 121 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) Name.anonymous))) -> Prop
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align probability_theory.indep_set ProbabilityTheory.IndepSetₓ'. -/
/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def IndepSet [MeasurableSpace Ω] (s t : Set Ω) (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  Indep (generateFrom {s}) (generateFrom {t}) μ

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def IndepFun [MeasurableSpace Ω] {β : ι → Type _} (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, Ω → β x)
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  IndepCat (fun x => MeasurableSpace.comap (f x) (m x)) μ

/- warning: probability_theory.indep_fun clashes with probability_theory.Indep_fun -> ProbabilityTheory.IndepFun
Case conversion may be inaccurate. Consider using '#align probability_theory.indep_fun ProbabilityTheory.IndepFunₓ'. -/
#print ProbabilityTheory.IndepFun /-
/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def IndepFun {β γ} [MeasurableSpace Ω] [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] (f : Ω → β) (g : Ω → γ)
    (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) : Prop :=
  Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) μ
-/

end Definitions

section Indep

@[symm]
theorem IndepSets.symm {s₁ s₂ : Set (Set Ω)} [MeasurableSpace Ω] {μ : Measure Ω} (h : IndepSets s₁ s₂ μ) :
    IndepSets s₂ s₁ μ := by
  intro t1 t2 ht1 ht2
  rw [Set.inter_comm, mul_comm]
  exact h t2 t1 ht2 ht1

@[symm]
theorem Indep.symm {m₁ m₂ : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω} (h : Indep m₁ m₂ μ) :
    Indep m₂ m₁ μ :=
  IndepSets.symm h

theorem indepBotRight (m' : MeasurableSpace Ω) {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] :
    Indep m' ⊥ μ := by
  intro s t hs ht
  rw [Set.mem_set_of_eq, MeasurableSpace.measurable_set_bot_iff] at ht
  cases ht
  · rw [ht, Set.inter_empty, measure_empty, mul_zero]
    
  · rw [ht, Set.inter_univ, measure_univ, mul_one]
    

theorem indepBotLeft (m' : MeasurableSpace Ω) {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] :
    Indep ⊥ m' μ :=
  (indepBotRight m').symm

theorem indepSetEmptyRight {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (s : Set Ω) :
    IndepSet s ∅ μ := by
  simp only [indep_set, generate_from_singleton_empty]
  exact indep_bot_right _

theorem indepSetEmptyLeft {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (s : Set Ω) :
    IndepSet ∅ s μ :=
  (indepSetEmptyRight s).symm

theorem indepSetsOfIndepSetsOfLeLeft {s₁ s₂ s₃ : Set (Set Ω)} [MeasurableSpace Ω] {μ : Measure Ω}
    (h_indep : IndepSets s₁ s₂ μ) (h31 : s₃ ⊆ s₁) : IndepSets s₃ s₂ μ := fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 (Set.mem_of_subset_of_mem h31 ht1) ht2

theorem indepSetsOfIndepSetsOfLeRight {s₁ s₂ s₃ : Set (Set Ω)} [MeasurableSpace Ω] {μ : Measure Ω}
    (h_indep : IndepSets s₁ s₂ μ) (h32 : s₃ ⊆ s₂) : IndepSets s₁ s₃ μ := fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 ht1 (Set.mem_of_subset_of_mem h32 ht2)

theorem indepOfIndepOfLeLeft {m₁ m₂ m₃ : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    (h_indep : Indep m₁ m₂ μ) (h31 : m₃ ≤ m₁) : Indep m₃ m₂ μ := fun t1 t2 ht1 ht2 => h_indep t1 t2 (h31 _ ht1) ht2

theorem indepOfIndepOfLeRight {m₁ m₂ m₃ : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω}
    (h_indep : Indep m₁ m₂ μ) (h32 : m₃ ≤ m₂) : Indep m₁ m₃ μ := fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (h32 _ ht2)

theorem IndepSets.union [MeasurableSpace Ω] {s₁ s₂ s' : Set (Set Ω)} {μ : Measure Ω} (h₁ : IndepSets s₁ s' μ)
    (h₂ : IndepSets s₂ s' μ) : IndepSets (s₁ ∪ s₂) s' μ := by
  intro t1 t2 ht1 ht2
  cases' (Set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂
  · exact h₁ t1 t2 ht1₁ ht2
    
  · exact h₂ t1 t2 ht1₂ ht2
    

@[simp]
theorem IndepSets.union_iff [MeasurableSpace Ω] {s₁ s₂ s' : Set (Set Ω)} {μ : Measure Ω} :
    IndepSets (s₁ ∪ s₂) s' μ ↔ IndepSets s₁ s' μ ∧ IndepSets s₂ s' μ :=
  ⟨fun h =>
    ⟨indepSetsOfIndepSetsOfLeLeft h (Set.subset_union_left s₁ s₂),
      indepSetsOfIndepSetsOfLeLeft h (Set.subset_union_right s₁ s₂)⟩,
    fun h => IndepSets.union h.left h.right⟩

/- warning: probability_theory.indep_sets.Union clashes with probability_theory.indep_sets.union -> ProbabilityTheory.IndepSets.union
warning: probability_theory.indep_sets.Union -> ProbabilityTheory.IndepSets.union is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u_1}} {ι : Type.{u_2}} [_inst_1 : MeasurableSpace.{u_1} Ω] {s : ι -> (Set.{u_1} (Set.{u_1} Ω))} {s' : Set.{u_1} (Set.{u_1} Ω)} {μ : MeasureTheory.Measure.{u_1} Ω _inst_1}, (forall (n : ι), ProbabilityTheory.IndepSets.{u_1} Ω _inst_1 (s n) s' μ) -> (ProbabilityTheory.IndepSets.{u_1} Ω _inst_1 (Set.UnionCat.{u_1 succ u_2} (Set.{u_1} Ω) ι (fun (n : ι) => s n)) s' μ)
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align probability_theory.indep_sets.Union ProbabilityTheory.IndepSets.unionₓ'. -/
theorem IndepSets.union [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {μ : Measure Ω}
    (hyp : ∀ n, IndepSets (s n) s' μ) : IndepSets (⋃ n, s n) s' μ := by
  intro t1 t2 ht1 ht2
  rw [Set.mem_Union] at ht1
  cases' ht1 with n ht1
  exact hyp n t1 t2 ht1 ht2

theorem IndepSets.bUnion [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {μ : Measure Ω} {u : Set ι}
    (hyp : ∀ n ∈ u, IndepSets (s n) s' μ) : IndepSets (⋃ n ∈ u, s n) s' μ := by
  intro t1 t2 ht1 ht2
  simp_rw [Set.mem_Union] at ht1
  rcases ht1 with ⟨n, hpn, ht1⟩
  exact hyp n hpn t1 t2 ht1 ht2

theorem IndepSets.inter [MeasurableSpace Ω] {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω)) {μ : Measure Ω}
    (h₁ : IndepSets s₁ s' μ) : IndepSets (s₁ ∩ s₂) s' μ := fun t1 t2 ht1 ht2 =>
  h₁ t1 t2 ((Set.mem_inter_iff _ _ _).mp ht1).left ht2

/- warning: probability_theory.indep_sets.Inter clashes with probability_theory.indep_sets.inter -> ProbabilityTheory.IndepSets.inter
warning: probability_theory.indep_sets.Inter -> ProbabilityTheory.IndepSets.inter is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u_1}} {ι : Type.{u_2}} [_inst_1 : MeasurableSpace.{u_1} Ω] {s : ι -> (Set.{u_1} (Set.{u_1} Ω))} {s' : Set.{u_1} (Set.{u_1} Ω)} {μ : MeasureTheory.Measure.{u_1} Ω _inst_1}, (Exists.{succ u_2} ι (fun (n : ι) => ProbabilityTheory.IndepSets.{u_1} Ω _inst_1 (s n) s' μ)) -> (ProbabilityTheory.IndepSets.{u_1} Ω _inst_1 (Set.InterCat.{u_1 succ u_2} (Set.{u_1} Ω) ι (fun (n : ι) => s n)) s' μ)
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align probability_theory.indep_sets.Inter ProbabilityTheory.IndepSets.interₓ'. -/
theorem IndepSets.inter [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {μ : Measure Ω}
    (h : ∃ n, IndepSets (s n) s' μ) : IndepSets (⋂ n, s n) s' μ := by
  intro t1 t2 ht1 ht2
  cases' h with n h
  exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2

theorem IndepSets.bInter [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {μ : Measure Ω} {u : Set ι}
    (h : ∃ n ∈ u, IndepSets (s n) s' μ) : IndepSets (⋂ n ∈ u, s n) s' μ := by
  intro t1 t2 ht1 ht2
  rcases h with ⟨n, hn, h⟩
  exact h t1 t2 (Set.bInter_subset_of_mem hn ht1) ht2

theorem indep_sets_singleton_iff [MeasurableSpace Ω] {s t : Set Ω} {μ : Measure Ω} :
    IndepSets {s} {t} μ ↔ μ (s ∩ t) = μ s * μ t :=
  ⟨fun h => h s t rfl rfl, fun h s1 t1 hs1 ht1 => by rwa [set.mem_singleton_iff.mp hs1, set.mem_singleton_iff.mp ht1]⟩

end Indep

/-! ### Deducing `indep` from `Indep` -/


section FromIndepToIndep

theorem IndepSets.indepSets {s : ι → Set (Set Ω)} [MeasurableSpace Ω] {μ : Measure Ω} (h_indep : IndepSets s μ)
    {i j : ι} (hij : i ≠ j) : IndepSets (s i) (s j) μ := by
  classical
  intro t₁ t₂ ht₁ ht₂
  have hf_m : ∀ x : ι, x ∈ {i, j} → ite (x = i) t₁ t₂ ∈ s x := by
    intro x hx
    cases' finset.mem_insert.mp hx with hx hx
    · simp [hx, ht₁]
      
    · simp [finset.mem_singleton.mp hx, hij.symm, ht₂]
      
  have h1 : t₁ = ite (i = i) t₁ t₂ := by simp only [if_true, eq_self_iff_true]
  have h2 : t₂ = ite (j = i) t₁ t₂ := by simp only [hij.symm, if_false]
  have h_inter : (⋂ (t : ι) (H : t ∈ ({i, j} : Finset ι)), ite (t = i) t₁ t₂) = ite (i = i) t₁ t₂ ∩ ite (j = i) t₁ t₂ :=
    by simp only [Finset.set_bInter_singleton, Finset.set_bInter_insert]
  have h_prod :
    (∏ t : ι in ({i, j} : Finset ι), μ (ite (t = i) t₁ t₂)) = μ (ite (i = i) t₁ t₂) * μ (ite (j = i) t₁ t₂) := by
    simp only [hij, Finset.prod_singleton, Finset.prod_insert, not_false_iff, Finset.mem_singleton]
  rw [h1]
  nth_rw 1 [h2]
  nth_rw 3 [h2]
  rw [← h_inter, ← h_prod, h_indep {i, j} hf_m]

theorem IndepCat.indep {m : ι → MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measure Ω} (h_indep : IndepCat m μ)
    {i j : ι} (hij : i ≠ j) : Indep (m i) (m j) μ := by
  change indep_sets ((fun x => measurable_set[m x]) i) ((fun x => measurable_set[m x]) j) μ
  exact Indep_sets.indep_sets h_indep hij

theorem IndepFun.indepFun {m₀ : MeasurableSpace Ω} {μ : Measure Ω} {β : ι → Type _} {m : ∀ x, MeasurableSpace (β x)}
    {f : ∀ i, Ω → β i} (hf_Indep : IndepFun m f μ) {i j : ι} (hij : i ≠ j) : IndepFun (f i) (f j) μ :=
  hf_Indep.indep hij

end FromIndepToIndep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

/-! ### Independence of measurable space structures implies independence of generating π-systems -/


theorem IndepCat.indepSets [MeasurableSpace Ω] {μ : Measure Ω} {m : ι → MeasurableSpace Ω} {s : ι → Set (Set Ω)}
    (hms : ∀ n, m n = generateFrom (s n)) (h_indep : IndepCat m μ) : IndepSets s μ := fun S f hfs =>
  (h_indep S) fun x hxS => ((hms x).symm ▸ measurableSetGenerateFrom (hfs x hxS) : measurable_set[m x] (f x))

theorem Indep.indepSets [MeasurableSpace Ω] {μ : Measure Ω} {s1 s2 : Set (Set Ω)}
    (h_indep : Indep (generateFrom s1) (generateFrom s2) μ) : IndepSets s1 s2 μ := fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 (measurableSetGenerateFrom ht1) (measurableSetGenerateFrom ht2)

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

/-! ### Independence of generating π-systems implies independence of measurable space structures -/


private theorem indep_sets.indep_aux {m2 : MeasurableSpace Ω} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {p1 p2 : Set (Set Ω)} (h2 : m2 ≤ m) (hp2 : IsPiSystem p2) (hpm2 : m2 = generateFrom p2)
    (hyp : IndepSets p1 p2 μ) {t1 t2 : Set Ω} (ht1 : t1 ∈ p1) (ht2m : measurable_set[m2] t2) :
    μ (t1 ∩ t2) = μ t1 * μ t2 := by
  let μ_inter := μ.restrict t1
  let ν := μ t1 • μ
  have h_univ : μ_inter Set.Univ = ν Set.Univ := by
    rw [measure.restrict_apply_univ, measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  haveI : is_finite_measure μ_inter := @restrict.is_finite_measure Ω _ t1 μ ⟨measure_lt_top μ t1⟩
  rw [Set.inter_comm, ← measure.restrict_apply (h2 t2 ht2m)]
  refine' ext_on_measurable_space_of_generate_finite m p2 (fun t ht => _) h2 hpm2 hp2 h_univ ht2m
  have ht2 : measurable_set[m] t := by
    refine' h2 _ _
    rw [hpm2]
    exact measurable_set_generate_from ht
  rw [measure.restrict_apply ht2, measure.smul_apply, Set.inter_comm]
  exact hyp t1 t ht1 ht

theorem IndepSets.indep {m1 m2 : MeasurableSpace Ω} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p1 p2 : Set (Set Ω)} (h1 : m1 ≤ m) (h2 : m2 ≤ m) (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2)
    (hpm1 : m1 = generateFrom p1) (hpm2 : m2 = generateFrom p2) (hyp : IndepSets p1 p2 μ) : Indep m1 m2 μ := by
  intro t1 t2 ht1 ht2
  let μ_inter := μ.restrict t2
  let ν := μ t2 • μ
  have h_univ : μ_inter Set.Univ = ν Set.Univ := by
    rw [measure.restrict_apply_univ, measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  haveI : is_finite_measure μ_inter := @restrict.is_finite_measure Ω _ t2 μ ⟨measure_lt_top μ t2⟩
  rw [mul_comm, ← measure.restrict_apply (h1 t1 ht1)]
  refine' ext_on_measurable_space_of_generate_finite m p1 (fun t ht => _) h1 hpm1 hp1 h_univ ht1
  have ht1 : measurable_set[m] t := by
    refine' h1 _ _
    rw [hpm1]
    exact measurable_set_generate_from ht
  rw [measure.restrict_apply ht1, measure.smul_apply, smul_eq_mul, mul_comm]
  exact indep_sets.indep_aux h2 hp2 hpm2 hyp ht ht2

theorem IndepSets.indep' {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {p1 p2 : Set (Set Ω)}
    (hp1m : ∀ s ∈ p1, MeasurableSet s) (hp2m : ∀ s ∈ p2, MeasurableSet s) (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2)
    (hyp : IndepSets p1 p2 μ) : Indep (generateFrom p1) (generateFrom p2) μ :=
  hyp.indep (generate_from_le hp1m) (generate_from_le hp2m) hp1 hp2 rfl rfl

variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

theorem indepSetsPiUnionInterOfDisjoint [IsProbabilityMeasure μ] {s : ι → Set (Set Ω)} {S T : Set ι}
    (h_indep : IndepSets s μ) (hST : Disjoint S T) : IndepSets (PiUnionInter s S) (PiUnionInter s T) μ := by
  rintro t1 t2 ⟨p1, hp1, f1, ht1_m, ht1_eq⟩ ⟨p2, hp2, f2, ht2_m, ht2_eq⟩
  classical
  let g i := ite (i ∈ p1) (f1 i) Set.Univ ∩ ite (i ∈ p2) (f2 i) Set.Univ
  have h_P_inter : μ (t1 ∩ t2) = ∏ n in p1 ∪ p2, μ (g n) := by
    have hgm : ∀ i ∈ p1 ∪ p2, g i ∈ s i := by
      intro i hi_mem_union
      rw [Finset.mem_union] at hi_mem_union
      cases' hi_mem_union with hi1 hi2
      · have hi2 : i ∉ p2 := fun hip2 => set.disjoint_left.mp hST (hp1 hi1) (hp2 hip2)
        simp_rw [g, if_pos hi1, if_neg hi2, Set.inter_univ]
        exact ht1_m i hi1
        
      · have hi1 : i ∉ p1 := fun hip1 => set.disjoint_right.mp hST (hp2 hi2) (hp1 hip1)
        simp_rw [g, if_neg hi1, if_pos hi2, Set.univ_inter]
        exact ht2_m i hi2
        
    have h_p1_inter_p2 :
      ((⋂ x ∈ p1, f1 x) ∩ ⋂ x ∈ p2, f2 x) =
        ⋂ i ∈ p1 ∪ p2, ite (i ∈ p1) (f1 i) Set.Univ ∩ ite (i ∈ p2) (f2 i) Set.Univ :=
      by
      ext1 x
      simp only [Set.mem_ite_univ_right, Set.mem_inter_iff, Set.mem_Inter, Finset.mem_union]
      exact
        ⟨fun h i _ => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i hi => (h i (Or.inl hi)).1 hi, fun i hi => (h i (Or.inr hi)).2 hi⟩⟩
    rw [ht1_eq, ht2_eq, h_p1_inter_p2, ← h_indep _ hgm]
  have h_μg : ∀ n, μ (g n) = ite (n ∈ p1) (μ (f1 n)) 1 * ite (n ∈ p2) (μ (f2 n)) 1 := by
    intro n
    simp_rw [g]
    split_ifs
    · exact absurd rfl (set.disjoint_iff_forall_ne.mp hST _ (hp1 h) _ (hp2 h_1))
      
    all_goals simp only [measure_univ, one_mul, mul_one, Set.inter_univ, Set.univ_inter]
  simp_rw [h_P_inter, h_μg, Finset.prod_mul_distrib, Finset.prod_ite_mem (p1 ∪ p2) p1 fun x => μ (f1 x),
    Finset.union_inter_cancel_left, Finset.prod_ite_mem (p1 ∪ p2) p2 fun x => μ (f2 x), Finset.union_inter_cancel_right,
    ht1_eq, ← h_indep p1 ht1_m, ht2_eq, ← h_indep p2 ht2_m]

theorem IndepSet.indepGenerateFromOfDisjoint [IsProbabilityMeasure μ] {s : ι → Set Ω} (hsm : ∀ n, MeasurableSet (s n))
    (hs : IndepSet s μ) (S T : Set ι) (hST : Disjoint S T) :
    Indep (generateFrom { t | ∃ n ∈ S, s n = t }) (generateFrom { t | ∃ k ∈ T, s k = t }) μ := by
  rw [← generate_from_pi_Union_Inter_singleton_left, ← generate_from_pi_Union_Inter_singleton_left]
  refine'
    indep_sets.indep' (fun t ht => generate_from_pi_Union_Inter_le _ _ _ _ (measurable_set_generate_from ht))
      (fun t ht => generate_from_pi_Union_Inter_le _ _ _ _ (measurable_set_generate_from ht)) _ _ _
  · exact fun k => generate_from_le fun t ht => (Set.mem_singleton_iff.1 ht).symm ▸ hsm k
    
  · exact fun k => generate_from_le fun t ht => (Set.mem_singleton_iff.1 ht).symm ▸ hsm k
    
  · exact is_pi_system_pi_Union_Inter _ (fun k => IsPiSystem.singleton _) _
    
  · exact is_pi_system_pi_Union_Inter _ (fun k => IsPiSystem.singleton _) _
    
  · classical
    exact indep_sets_pi_Union_Inter_of_disjoint (Indep.Indep_sets (fun n => rfl) hs) hST
    

theorem indepSuprOfDisjoint [IsProbabilityMeasure μ] {m : ι → MeasurableSpace Ω} (h_le : ∀ i, m i ≤ m0)
    (h_indep : IndepCat m μ) {S T : Set ι} (hST : Disjoint S T) : Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) μ := by
  refine'
    indep_sets.indep (supr₂_le fun i _ => h_le i) (supr₂_le fun i _ => h_le i) _ _
      (generate_from_pi_Union_Inter_measurable_set m S).symm (generate_from_pi_Union_Inter_measurable_set m T).symm _
  · exact is_pi_system_pi_Union_Inter _ (fun n => @is_pi_system_measurable_set Ω (m n)) _
    
  · exact is_pi_system_pi_Union_Inter _ (fun n => @is_pi_system_measurable_set Ω (m n)) _
    
  · classical
    exact indep_sets_pi_Union_Inter_of_disjoint h_indep hST
    

theorem indepSuprOfDirectedLe {Ω} {m : ι → MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h_indep : ∀ i, Indep (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
    (hm : Directed (· ≤ ·) m) : Indep (⨆ i, m i) m' μ := by
  let p : ι → Set (Set Ω) := fun n => { t | measurable_set[m n] t }
  have hp : ∀ n, IsPiSystem (p n) := fun n => @is_pi_system_measurable_set Ω (m n)
  have h_gen_n : ∀ n, m n = generate_from (p n) := fun n => (@generate_from_measurable_set Ω (m n)).symm
  have hp_supr_pi : IsPiSystem (⋃ n, p n) := is_pi_system_Union_of_directed_le p hp hm
  let p' := { t : Set Ω | measurable_set[m'] t }
  have hp'_pi : IsPiSystem p' := @is_pi_system_measurable_set Ω m'
  have h_gen' : m' = generate_from p' := (@generate_from_measurable_set Ω m').symm
  -- the π-systems defined are independent
  have h_pi_system_indep : indep_sets (⋃ n, p n) p' μ := by
    refine' indep_sets.Union _
    simp_rw [h_gen_n, h_gen'] at h_indep
    exact fun n => (h_indep n).IndepSets
  -- now go from π-systems to σ-algebras
  refine' indep_sets.indep (supr_le h_le) h_le' hp_supr_pi hp'_pi _ h_gen' h_pi_system_indep
  exact (generate_from_Union_measurable_set _).symm

theorem IndepSet.indepGenerateFromLt [Preorder ι] [IsProbabilityMeasure μ] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : IndepSet s μ) (i : ι) :
    Indep (generateFrom {s i}) (generateFrom { t | ∃ j < i, s j = t }) μ := by
  convert
    hs.indep_generate_from_of_disjoint hsm {i} { j | j < i } fun x ⟨hx₁, hx₂⟩ =>
      (Set.mem_set_of.1 hx₂).Ne <| Set.mem_singleton_iff.1 hx₁
  simp only [Set.mem_singleton_iff, exists_prop, exists_eq_left, Set.set_of_eq_eq_singleton']

theorem IndepSet.indepGenerateFromLe [LinearOrder ι] [IsProbabilityMeasure μ] {s : ι → Set Ω}
    (hsm : ∀ n, MeasurableSet (s n)) (hs : IndepSet s μ) (i : ι) {k : ι} (hk : i < k) :
    Indep (generateFrom {s k}) (generateFrom { t | ∃ j ≤ i, s j = t }) μ := by
  convert
    hs.indep_generate_from_of_disjoint hsm {k} { j | j ≤ i } fun x ⟨hx₁, hx₂⟩ =>
      not_lt.2 (Set.mem_set_of.2 hx₂) <| (Set.mem_singleton_iff.1 hx₁).symm ▸ hk
  simp only [Set.mem_singleton_iff, exists_prop, exists_eq_left, Set.set_of_eq_eq_singleton']

theorem IndepSet.indepGenerateFromLeNat [IsProbabilityMeasure μ] {s : ℕ → Set Ω} (hsm : ∀ n, MeasurableSet (s n))
    (hs : IndepSet s μ) (n : ℕ) : Indep (generateFrom {s (n + 1)}) (generateFrom { t | ∃ k ≤ n, s k = t }) μ :=
  hs.indepGenerateFromLe hsm _ n.lt_succ_self

theorem indepSuprOfMonotone [SemilatticeSup ι] {Ω} {m : ι → MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h_indep : ∀ i, Indep (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
    (hm : Monotone m) : Indep (⨆ i, m i) m' μ :=
  indepSuprOfDirectedLe h_indep h_le h_le' (Monotone.directed_le hm)

theorem indepSuprOfAntitone [SemilatticeInf ι] {Ω} {m : ι → MeasurableSpace Ω} {m' m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h_indep : ∀ i, Indep (m i) m' μ) (h_le : ∀ i, m i ≤ m0) (h_le' : m' ≤ m0)
    (hm : Antitone m) : Indep (⨆ i, m i) m' μ :=
  indepSuprOfDirectedLe h_indep h_le h_le' (directed_of_inf hm)

theorem IndepSets.piUnionInterOfNotMem {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι} (hp_ind : IndepSets π μ)
    (haS : a ∉ S) : IndepSets (PiUnionInter π S) (π a) μ := by
  rintro t1 t2 ⟨s, hs_mem, ft1, hft1_mem, ht1_eq⟩ ht2_mem_pia
  rw [Finset.coe_subset] at hs_mem
  classical
  let f n := ite (n = a) t2 (ite (n ∈ s) (ft1 n) Set.Univ)
  have h_f_mem : ∀ n ∈ insert a s, f n ∈ π n := by
    intro n hn_mem_insert
    simp_rw [f]
    cases' finset.mem_insert.mp hn_mem_insert with hn_mem hn_mem
    · simp [hn_mem, ht2_mem_pia]
      
    · have hn_ne_a : n ≠ a := by
        rintro rfl
        exact haS (hs_mem hn_mem)
      simp [hn_ne_a, hn_mem, hft1_mem n hn_mem]
      
  have h_f_mem_pi : ∀ n ∈ s, f n ∈ π n := fun x hxS => h_f_mem x (by simp [hxS])
  have h_t1 : t1 = ⋂ n ∈ s, f n := by
    suffices h_forall : ∀ n ∈ s, f n = ft1 n
    · rw [ht1_eq]
      congr with (n x)
      congr with (hns y)
      simp only [(h_forall n hns).symm]
      
    intro n hnS
    have hn_ne_a : n ≠ a := by
      rintro rfl
      exact haS (hs_mem hnS)
    simp_rw [f, if_pos hnS, if_neg hn_ne_a]
  have h_μ_t1 : μ t1 = ∏ n in s, μ (f n) := by rw [h_t1, ← hp_ind s h_f_mem_pi]
  have h_t2 : t2 = f a := by
    simp_rw [f]
    simp
  have h_μ_inter : μ (t1 ∩ t2) = ∏ n in insert a s, μ (f n) := by
    have h_t1_inter_t2 : t1 ∩ t2 = ⋂ n ∈ insert a s, f n := by rw [h_t1, h_t2, Finset.set_bInter_insert, Set.inter_comm]
    rw [h_t1_inter_t2, ← hp_ind (insert a s) h_f_mem]
  have has : a ∉ s := fun has_mem => haS (hs_mem Membership)
  rw [h_μ_inter, Finset.prod_insert has, h_t2, mul_comm, h_μ_t1]

/- warning: probability_theory.Indep_sets.Indep clashes with probability_theory.indep_sets.indep -> ProbabilityTheory.IndepSets.indep
warning: probability_theory.Indep_sets.Indep -> ProbabilityTheory.IndepSets.indep is a dubious translation:
lean 3 declaration is
  forall {Ω : Type.{u_1}} {ι : Type.{u_2}} {m0 : MeasurableSpace.{u_1} Ω} {μ : MeasureTheory.Measure.{u_1} Ω m0} [_inst_1 : MeasureTheory.IsProbabilityMeasure.{u_1} Ω m0 μ] (m : ι -> (MeasurableSpace.{u_1} Ω)), (forall (i : ι), LE.le.{u_1} (MeasurableSpace.{u_1} Ω) (MeasurableSpace.hasLe.{u_1} Ω) (m i) m0) -> (forall (π : ι -> (Set.{u_1} (Set.{u_1} Ω))), (forall (n : ι), IsPiSystem.{u_1} Ω (π n)) -> (forall (i : ι), Eq.{succ u_1} (MeasurableSpace.{u_1} Ω) (m i) (MeasurableSpace.generateFrom.{u_1} Ω (π i))) -> (ProbabilityTheory.IndepSets.{u_1 u_2} Ω ι m0 π μ) -> (ProbabilityTheory.IndepCat.{u_1 u_2} Ω ι m m0 μ))
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align probability_theory.Indep_sets.Indep ProbabilityTheory.IndepSets.indepₓ'. -/
/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem IndepSets.indep [IsProbabilityMeasure μ] (m : ι → MeasurableSpace Ω) (h_le : ∀ i, m i ≤ m0)
    (π : ι → Set (Set Ω)) (h_pi : ∀ n, IsPiSystem (π n)) (h_generate : ∀ i, m i = generateFrom (π i))
    (h_ind : IndepSets π μ) : IndepCat m μ := by
  classical
  refine' Finset.induction _ _
  · simp only [measure_univ, imp_true_iff, Set.Inter_false, Set.Inter_univ, Finset.prod_empty, eq_self_iff_true]
    
  intro a S ha_notin_S h_rec f hf_m
  have hf_m_S : ∀ x ∈ S, measurable_set[m x] (f x) := fun x hx => hf_m x (by simp [hx])
  rw [Finset.set_bInter_insert, Finset.prod_insert ha_notin_S, ← h_rec hf_m_S]
  let p := PiUnionInter π S
  set m_p := generate_from p with hS_eq_generate
  have h_indep : indep m_p (m a) μ := by
    have hp : IsPiSystem p := is_pi_system_pi_Union_Inter π h_pi S
    have h_le' : ∀ i, generate_from (π i) ≤ m0 := fun i => (h_generate i).symm.trans_le (h_le i)
    have hm_p : m_p ≤ m0 := generate_from_pi_Union_Inter_le π h_le' S
    exact
      indep_sets.indep hm_p (h_le a) hp (h_pi a) hS_eq_generate (h_generate a)
        (h_ind.pi_Union_Inter_of_not_mem ha_notin_S)
  refine' h_indep.symm (f a) (⋂ n ∈ S, f n) (hf_m a (Finset.mem_insert_self a S)) _
  have h_le_p : ∀ i ∈ S, m i ≤ m_p := by
    intro n hn
    rw [hS_eq_generate, h_generate n]
    exact le_generate_from_pi_Union_Inter S hn
  have h_S_f : ∀ i ∈ S, measurable_set[m_p] (f i) := fun i hi => (h_le_p i hi) (f i) (hf_m_S i hi)
  exact S.measurable_set_bInter h_S_f

end FromPiSystemsToMeasurableSpaces

section IndepSet

/-! ### Independence of measurable sets

We prove the following equivalences on `indep_set`, for measurable sets `s, t`.
* `indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `indep_set s t μ ↔ indep_sets {s} {t} μ`.
-/


variable {s t : Set Ω} (S T : Set (Set Ω))

theorem indep_set_iff_indep_sets_singleton {m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) [IsProbabilityMeasure μ] :
    IndepSet s t μ ↔ IndepSets {s} {t} μ :=
  ⟨Indep.indepSets, fun h =>
    IndepSets.indep (generate_from_le fun u hu => by rwa [set.mem_singleton_iff.mp hu])
      (generate_from_le fun u hu => by rwa [set.mem_singleton_iff.mp hu]) (IsPiSystem.singleton s)
      (IsPiSystem.singleton t) rfl rfl h⟩

theorem indep_set_iff_measure_inter_eq_mul {m0 : MeasurableSpace Ω} (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) [IsProbabilityMeasure μ] :
    IndepSet s t μ ↔ μ (s ∩ t) = μ s * μ t :=
  (indep_set_iff_indep_sets_singleton hs_meas ht_meas μ).trans indep_sets_singleton_iff

theorem IndepSets.indepSetOfMem {m0 : MeasurableSpace Ω} (hs : s ∈ S) (ht : t ∈ T) (hs_meas : MeasurableSet s)
    (ht_meas : MeasurableSet t) (μ : Measure Ω := by exact MeasureTheory.MeasureSpace.volume) [IsProbabilityMeasure μ]
    (h_indep : IndepSets S T μ) : IndepSet s t μ :=
  (indep_set_iff_measure_inter_eq_mul hs_meas ht_meas μ).mpr (h_indep s t hs ht)

theorem Indep.indepSetOfMeasurableSet {m₁ m₂ m0 : MeasurableSpace Ω} {μ : Measure Ω} (h_indep : Indep m₁ m₂ μ)
    {s t : Set Ω} (hs : measurable_set[m₁] s) (ht : measurable_set[m₂] t) : IndepSet s t μ := by
  refine' fun s' t' hs' ht' => h_indep s' t' _ _
  · refine' generate_from_induction (fun u => measurable_set[m₁] u) {s} _ _ _ _ hs'
    · simp only [hs, Set.mem_singleton_iff, Set.mem_set_of_eq, forall_eq]
      
    · exact @MeasurableSet.empty _ m₁
      
    · exact fun u hu => hu.compl
      
    · exact fun f hf => MeasurableSet.union hf
      
    
  · refine' generate_from_induction (fun u => measurable_set[m₂] u) {t} _ _ _ _ ht'
    · simp only [ht, Set.mem_singleton_iff, Set.mem_set_of_eq, forall_eq]
      
    · exact @MeasurableSet.empty _ m₂
      
    · exact fun u hu => hu.compl
      
    · exact fun f hf => MeasurableSet.union hf
      
    

theorem indep_iff_forall_indep_set (m₁ m₂ : MeasurableSpace Ω) {m0 : MeasurableSpace Ω} (μ : Measure Ω) :
    Indep m₁ m₂ μ ↔ ∀ s t, measurable_set[m₁] s → measurable_set[m₂] t → IndepSet s t μ :=
  ⟨fun h => fun s t hs ht => h.indepSetOfMeasurableSet hs ht, fun h s t hs ht =>
    h s t hs ht s t (measurableSetGenerateFrom (Set.mem_singleton s)) (measurableSetGenerateFrom (Set.mem_singleton t))⟩

end IndepSet

section IndepFun

/-! ### Independence of random variables

-/


variable {β β' γ γ' : Type _} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}

theorem indep_fun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} :
    IndepFun f g μ ↔ ∀ s t, MeasurableSet s → MeasurableSet t → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
  constructor <;> intro h
  · refine' fun s t hs ht => h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact h s t hs ht
    

theorem Indep_fun_iff_measure_inter_preimage_eq_mul {ι : Type _} {β : ι → Type _} (m : ∀ x, MeasurableSpace (β x))
    (f : ∀ i, Ω → β i) :
    IndepFun m f μ ↔
      ∀ (S : Finset ι) {sets : ∀ i : ι, Set (β i)} (H : ∀ i, i ∈ S → measurable_set[m i] (sets i)),
        μ (⋂ i ∈ S, f i ⁻¹' sets i) = ∏ i in S, μ (f i ⁻¹' sets i) :=
  by
  refine' ⟨fun h S sets h_meas => h _ fun i hi_mem => ⟨sets i, h_meas i hi_mem, rfl⟩, _⟩
  intro h S setsΩ h_meas
  classical
  let setsβ : ∀ i : ι, Set (β i) := fun i => dite (i ∈ S) (fun hi_mem => (h_meas i hi_mem).some) fun _ => Set.Univ
  have h_measβ : ∀ i ∈ S, measurable_set[m i] (setsβ i) := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).some_spec.1
  have h_preim : ∀ i ∈ S, setsΩ i = f i ⁻¹' setsβ i := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).some_spec.2.symm
  have h_left_eq : μ (⋂ i ∈ S, setsΩ i) = μ (⋂ i ∈ S, f i ⁻¹' setsβ i) := by
    congr with (i x)
    simp only [Set.mem_Inter]
    constructor <;> intro h hi_mem <;> specialize h hi_mem
    · rwa [h_preim i hi_mem] at h
      
    · rwa [h_preim i hi_mem]
      
  have h_right_eq : (∏ i in S, μ (setsΩ i)) = ∏ i in S, μ (f i ⁻¹' setsβ i) := by
    refine' Finset.prod_congr rfl fun i hi_mem => _
    rw [h_preim i hi_mem]
  rw [h_left_eq, h_right_eq]
  exact h S h_measβ

theorem indep_fun_iff_indep_set_preimage {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} [IsProbabilityMeasure μ]
    (hf : Measurable f) (hg : Measurable g) :
    IndepFun f g μ ↔ ∀ s t, MeasurableSet s → MeasurableSet t → IndepSet (f ⁻¹' s) (g ⁻¹' t) μ := by
  refine' indep_fun_iff_measure_inter_preimage_eq_mul.trans _
  constructor <;> intro h s t hs ht <;> specialize h s t hs ht
  · rwa [indep_set_iff_measure_inter_eq_mul (hf hs) (hg ht) μ]
    
  · rwa [← indep_set_iff_measure_inter_eq_mul (hf hs) (hg ht) μ]
    

@[symm]
theorem IndepFun.symm {mβ : MeasurableSpace β} {f g : Ω → β} (hfg : IndepFun f g μ) : IndepFun g f μ :=
  hfg.symm

theorem IndepFun.aeEq {mβ : MeasurableSpace β} {f g f' g' : Ω → β} (hfg : IndepFun f g μ) (hf : f =ᵐ[μ] f')
    (hg : g =ᵐ[μ] g') : IndepFun f' g' μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  have h1 : f ⁻¹' A =ᵐ[μ] f' ⁻¹' A := hf.fun_comp A
  have h2 : g ⁻¹' B =ᵐ[μ] g' ⁻¹' B := hg.fun_comp B
  rw [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]
  exact hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩

theorem IndepFun.comp {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} {mγ : MeasurableSpace γ}
    {mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'} (hfg : IndepFun f g μ) (hφ : Measurable φ)
    (hψ : Measurable ψ) : IndepFun (φ ∘ f) (ψ ∘ g) μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  apply hfg
  · exact ⟨φ ⁻¹' A, hφ hA, set.preimage_comp.symm⟩
    
  · exact ⟨ψ ⁻¹' B, hψ hB, set.preimage_comp.symm⟩
    

/-- If `f` is a family of mutually independent random variables (`Indep_fun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
theorem IndepFun.indepFunFinset [IsProbabilityMeasure μ] {ι : Type _} [DecidableEq ι] {β : ι → Type _}
    {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i} (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : IndepFun m f μ) (hf_meas : ∀ i, Measurable (f i)) :
    IndepFun (fun a (i : S) => f i a) (fun a (i : T) => f i a) μ := by
  -- We introduce π-systems, build from the π-system of boxes which generates `measurable_space.pi`.
  let πSβ := Set.Pi (Set.Univ : Set S) '' Set.Pi (Set.Univ : Set S) fun i => { s : Set (β i) | measurable_set[m i] s }
  let πS := { s : Set Ω | ∃ t ∈ πSβ, (fun a (i : S) => f i a) ⁻¹' t = s }
  have hπS_pi : IsPiSystem πS := is_pi_system_pi.comap fun a i => f i a
  have hπS_gen : (measurable_space.pi.comap fun a (i : S) => f i a) = generate_from πS := by
    rw [generate_from_pi.symm, comap_generate_from]
    · congr with s
      simp only [Set.mem_image, Set.mem_set_of_eq, exists_prop]
      
    · infer_instance
      
  let πTβ := Set.Pi (Set.Univ : Set T) '' Set.Pi (Set.Univ : Set T) fun i => { s : Set (β i) | measurable_set[m i] s }
  let πT := { s : Set Ω | ∃ t ∈ πTβ, (fun a (i : T) => f i a) ⁻¹' t = s }
  have hπT_pi : IsPiSystem πT := is_pi_system_pi.comap fun a i => f i a
  have hπT_gen : (measurable_space.pi.comap fun a (i : T) => f i a) = generate_from πT := by
    rw [generate_from_pi.symm, comap_generate_from]
    · congr with s
      simp only [Set.mem_image, Set.mem_set_of_eq, exists_prop]
      
    · infer_instance
      
  -- To prove independence, we prove independence of the generating π-systems.
  refine'
    indep_sets.indep (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i))
      (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i)) hπS_pi hπT_pi hπS_gen hπT_gen _
  rintro _ _ ⟨s, ⟨sets_s, hs1, hs2⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2⟩, rfl⟩
  simp only [Set.mem_univ_pi, Set.mem_set_of_eq] at hs1 ht1
  rw [← hs2, ← ht2]
  let sets_s' : ∀ i : ι, Set (β i) := fun i => dite (i ∈ S) (fun hi => sets_s ⟨i, hi⟩) fun _ => Set.Univ
  have h_sets_s'_eq : ∀ {i} (hi : i ∈ S), sets_s' i = sets_s ⟨i, hi⟩ := by
    intro i hi
    simp_rw [sets_s', dif_pos hi]
  have h_sets_s'_univ : ∀ {i} (hi : i ∈ T), sets_s' i = Set.Univ := by
    intro i hi
    simp_rw [sets_s', dif_neg (finset.disjoint_right.mp hST hi)]
  let sets_t' : ∀ i : ι, Set (β i) := fun i => dite (i ∈ T) (fun hi => sets_t ⟨i, hi⟩) fun _ => Set.Univ
  have h_sets_t'_univ : ∀ {i} (hi : i ∈ S), sets_t' i = Set.Univ := by
    intro i hi
    simp_rw [sets_t', dif_neg (finset.disjoint_left.mp hST hi)]
  have h_meas_s' : ∀ i ∈ S, MeasurableSet (sets_s' i) := by
    intro i hi
    rw [h_sets_s'_eq hi]
    exact hs1 _
  have h_meas_t' : ∀ i ∈ T, MeasurableSet (sets_t' i) := by
    intro i hi
    simp_rw [sets_t', dif_pos hi]
    exact ht1 _
  have h_eq_inter_S : (fun (ω : Ω) (i : ↥S) => f (↑i) ω) ⁻¹' Set.Pi Set.Univ sets_s = ⋂ i ∈ S, f i ⁻¹' sets_s' i := by
    ext1 x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Inter]
    constructor <;> intro h
    · intro i hi
      rw [h_sets_s'_eq hi]
      exact h ⟨i, hi⟩
      
    · rintro ⟨i, hi⟩
      specialize h i hi
      rw [h_sets_s'_eq hi] at h
      exact h
      
  have h_eq_inter_T : (fun (ω : Ω) (i : ↥T) => f (↑i) ω) ⁻¹' Set.Pi Set.Univ sets_t = ⋂ i ∈ T, f i ⁻¹' sets_t' i := by
    ext1 x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_Inter]
    constructor <;> intro h
    · intro i hi
      simp_rw [sets_t', dif_pos hi]
      exact h ⟨i, hi⟩
      
    · rintro ⟨i, hi⟩
      specialize h i hi
      simp_rw [sets_t', dif_pos hi] at h
      exact h
      
  rw [Indep_fun_iff_measure_inter_preimage_eq_mul] at hf_Indep
  rw [h_eq_inter_S, h_eq_inter_T, hf_Indep S h_meas_s', hf_Indep T h_meas_t']
  have h_Inter_inter :
    ((⋂ i ∈ S, f i ⁻¹' sets_s' i) ∩ ⋂ i ∈ T, f i ⁻¹' sets_t' i) = ⋂ i ∈ S ∪ T, f i ⁻¹' (sets_s' i ∩ sets_t' i) := by
    ext1 x
    simp only [Set.mem_inter_iff, Set.mem_Inter, Set.mem_preimage, Finset.mem_union]
    constructor <;> intro h
    · intro i hi
      cases hi
      · rw [h_sets_t'_univ hi]
        exact ⟨h.1 i hi, Set.mem_univ _⟩
        
      · rw [h_sets_s'_univ hi]
        exact ⟨Set.mem_univ _, h.2 i hi⟩
        
      
    · exact ⟨fun i hi => (h i (Or.inl hi)).1, fun i hi => (h i (Or.inr hi)).2⟩
      
  rw [h_Inter_inter, hf_Indep (S ∪ T)]
  swap
  · intro i hi_mem
    rw [Finset.mem_union] at hi_mem
    cases hi_mem
    · rw [h_sets_t'_univ hi_mem, Set.inter_univ]
      exact h_meas_s' i hi_mem
      
    · rw [h_sets_s'_univ hi_mem, Set.univ_inter]
      exact h_meas_t' i hi_mem
      
    
  rw [Finset.prod_union hST]
  congr 1
  · refine' Finset.prod_congr rfl fun i hi => _
    rw [h_sets_t'_univ hi, Set.inter_univ]
    
  · refine' Finset.prod_congr rfl fun i hi => _
    rw [h_sets_s'_univ hi, Set.univ_inter]
    

theorem IndepFun.indepFunProd [IsProbabilityMeasure μ] {ι : Type _} {β : ι → Type _} {m : ∀ i, MeasurableSpace (β i)}
    {f : ∀ i, Ω → β i} (hf_Indep : IndepFun m f μ) (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k)
    (hjk : j ≠ k) : IndepFun (fun a => (f i a, f j a)) (f k) μ := by
  classical
  have h_right :
    f k =
      (fun p : ∀ j : ({k} : Finset ι), β j => p ⟨k, Finset.mem_singleton_self k⟩) ∘ fun a (j : ({k} : Finset ι)) =>
        f j a :=
    rfl
  have h_meas_right : Measurable fun p : ∀ j : ({k} : Finset ι), β j => p ⟨k, Finset.mem_singleton_self k⟩ :=
    measurablePiApply ⟨k, Finset.mem_singleton_self k⟩
  let s : Finset ι := {i, j}
  have h_left :
    (fun ω => (f i ω, f j ω)) =
      (fun p : ∀ l : s, β l =>
          (p ⟨i, Finset.mem_insert_self i _⟩, p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)) ∘
        fun a (j : s) => f j a :=
    by
    ext1 a
    simp only [Prod.mk.inj_iff]
    constructor <;> rfl
  have h_meas_left :
    Measurable fun p : ∀ l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩, p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) :=
    Measurable.prod (measurablePiApply ⟨i, Finset.mem_insert_self i {j}⟩)
      (measurablePiApply ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self j)⟩)
  rw [h_left, h_right]
  refine' (hf_Indep.indep_fun_finset s {k} _ hf_meas).comp h_meas_left h_meas_right
  intro x hx
  simp only [Finset.inf_eq_inter, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hx
  simp only [Finset.bot_eq_empty, Finset.not_mem_empty]
  cases' hx.1 with hx_eq hx_eq <;> rw [hx_eq] at hx
  · exact hik hx.2
    
  · exact hjk hx.2
    

@[to_additive]
theorem IndepFun.mul [IsProbabilityMeasure μ] {ι : Type _} {β : Type _} {m : MeasurableSpace β} [Mul β]
    [HasMeasurableMul₂ β] {f : ι → Ω → β} (hf_Indep : IndepFun (fun _ => m) f μ) (hf_meas : ∀ i, Measurable (f i))
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) : IndepFun (f i * f j) (f k) μ := by
  have : indep_fun (fun ω => (f i ω, f j ω)) (f k) μ := hf_Indep.indep_fun_prod hf_meas i j k hik hjk
  change indep_fun ((fun p : β × β => p.fst * p.snd) ∘ fun ω => (f i ω, f j ω)) (id ∘ f k) μ
  exact indep_fun.comp this (measurable_fst.mul measurableSnd) measurableId

@[to_additive]
theorem IndepFun.indepFunFinsetProdOfNotMem [IsProbabilityMeasure μ] {ι : Type _} {β : Type _} {m : MeasurableSpace β}
    [CommMonoid β] [HasMeasurableMul₂ β] {f : ι → Ω → β} (hf_Indep : IndepFun (fun _ => m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) {s : Finset ι} {i : ι} (hi : i ∉ s) : IndepFun (∏ j in s, f j) (f i) μ := by
  classical
  have h_right :
    f i =
      (fun p : ∀ j : ({i} : Finset ι), β => p ⟨i, Finset.mem_singleton_self i⟩) ∘ fun a (j : ({i} : Finset ι)) =>
        f j a :=
    rfl
  have h_meas_right : Measurable fun p : ∀ j : ({i} : Finset ι), β => p ⟨i, Finset.mem_singleton_self i⟩ :=
    measurablePiApply ⟨i, Finset.mem_singleton_self i⟩
  have h_left : (∏ j in s, f j) = (fun p : ∀ j : s, β => ∏ j, p j) ∘ fun a (j : s) => f j a := by
    ext1 a
    simp only [Function.comp_app]
    have : (∏ j : ↥s, f (↑j) a) = (∏ j : ↥s, f ↑j) a := by rw [Finset.prod_apply]
    rw [this, Finset.prod_coe_sort]
  have h_meas_left : Measurable fun p : ∀ j : s, β => ∏ j, p j :=
    finset.univ.measurable_prod fun (j : ↥s) (H : j ∈ Finset.univ) => measurablePiApply j
  rw [h_left, h_right]
  exact
    (hf_Indep.indep_fun_finset s {i} (finset.disjoint_singleton_left.mpr hi).symm hf_meas).comp h_meas_left h_meas_right

@[to_additive]
theorem IndepFun.indepFunProdRangeSucc [IsProbabilityMeasure μ] {β : Type _} {m : MeasurableSpace β} [CommMonoid β]
    [HasMeasurableMul₂ β] {f : ℕ → Ω → β} (hf_Indep : IndepFun (fun _ => m) f μ) (hf_meas : ∀ i, Measurable (f i))
    (n : ℕ) : IndepFun (∏ j in Finset.range n, f j) (f n) μ :=
  hf_Indep.indepFunFinsetProdOfNotMem hf_meas Finset.not_mem_range_self

theorem IndepSet.indepFunIndicator [Zero β] [One β] {m : MeasurableSpace β} {s : ι → Set Ω} (hs : IndepSet s μ) :
    IndepFun (fun n => m) (fun n => (s n).indicator fun ω => 1) μ := by
  classical
  rw [Indep_fun_iff_measure_inter_preimage_eq_mul]
  rintro S π hπ
  simp_rw [Set.indicator_const_preimage_eq_union]
  refine' @hs S (fun i => ite (1 ∈ π i) (s i) ∅ ∪ ite ((0 : β) ∈ π i) (s iᶜ) ∅) fun i hi => _
  have hsi : measurable_set[generate_from {s i}] (s i) := measurable_set_generate_from (Set.mem_singleton _)
  refine'
    MeasurableSet.union (MeasurableSet.ite' (fun _ => hsi) fun _ => _)
      (MeasurableSet.ite' (fun _ => hsi.compl) fun _ => _)
  · exact @MeasurableSet.empty _ (generate_from {s i})
    
  · exact @MeasurableSet.empty _ (generate_from {s i})
    

end IndepFun

/-! ### Kolmogorov's 0-1 law

Let `s : ι → measurable_space Ω` be an independent sequence of sub-σ-algebras. Then any set which
is measurable with respect to the tail σ-algebra `limsup s at_top` has probability 0 or 1.
-/


section ZeroOneLaw

variable {m m0 : MeasurableSpace Ω} {μ : Measure Ω}

theorem measure_eq_zero_or_one_or_top_of_indep_set_self {t : Set Ω} (h_indep : IndepSet t t μ) :
    μ t = 0 ∨ μ t = 1 ∨ μ t = ∞ := by
  specialize
    h_indep t t (measurable_set_generate_from (Set.mem_singleton t))
      (measurable_set_generate_from (Set.mem_singleton t))
  by_cases h0:μ t = 0
  · exact Or.inl h0
    
  by_cases h_top:μ t = ∞
  · exact Or.inr (Or.inr h_top)
    
  rw [← one_mul (μ (t ∩ t)), Set.inter_self, Ennreal.mul_eq_mul_right h0 h_top] at h_indep
  exact Or.inr (Or.inl h_indep.symm)

theorem measure_eq_zero_or_one_of_indep_set_self [IsFiniteMeasure μ] {t : Set Ω} (h_indep : IndepSet t t μ) :
    μ t = 0 ∨ μ t = 1 := by
  have h_0_1_top := measure_eq_zero_or_one_or_top_of_indep_set_self h_indep
  simpa [measure_ne_top μ] using h_0_1_top

variable [IsProbabilityMeasure μ] {s : ι → MeasurableSpace Ω}

open Filter

theorem indepBsuprCompl (h_le : ∀ n, s n ≤ m0) (h_indep : IndepCat s μ) (t : Set ι) :
    Indep (⨆ n ∈ t, s n) (⨆ n ∈ tᶜ, s n) μ :=
  indepSuprOfDisjoint h_le h_indep disjointComplRight

section Abstract

variable {α : Type _} {p : Set ι → Prop} {f : Filter ι} {ns : α → Set ι}

/-! We prove a version of Kolmogorov's 0-1 law for the σ-algebra `limsup s f` where `f` is a filter
for which we can define the following two functions:
* `p : set ι → Prop` such that for a set `t`, `p t → tᶜ ∈ f`,
* `ns : α → set ι` a directed sequence of sets which all verify `p` and such that
  `⋃ a, ns a = set.univ`.

For the example of `f = at_top`, we can take `p = bdd_above` and `ns : ι → set ι := λ i, set.Iic i`.
-/


/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:62:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem indepBsuprLimsup (h_le : ∀ n, s n ≤ m0) (h_indep : IndepCat s μ) (hf : ∀ t, p t → tᶜ ∈ f) {t : Set ι}
    (ht : p t) : Indep (⨆ n ∈ t, s n) (limsup s f) μ := by
  refine' indep_of_indep_of_le_right (indep_bsupr_compl h_le h_indep t) _
  refine'
    Limsup_le_of_le
      (by
        run_tac
          is_bounded_default)
      _
  simp only [Set.mem_compl_iff, eventually_map]
  exact eventually_of_mem (hf t ht) le_supr₂

theorem indepSuprDirectedLimsup (h_le : ∀ n, s n ≤ m0) (h_indep : IndepCat s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) : Indep (⨆ a, ⨆ n ∈ ns a, s n) (limsup s f) μ := by
  refine' indep_supr_of_directed_le _ _ _ _
  · exact fun a => indep_bsupr_limsup h_le h_indep hf (hnsp a)
    
  · exact fun a => supr₂_le fun n hn => h_le n
    
  · exact limsup_le_supr.trans (supr_le h_le)
    
  · intro a b
    obtain ⟨c, hc⟩ := hns a b
    refine' ⟨c, _, _⟩ <;> refine' supr_mono fun n => supr_mono' fun hn => ⟨_, le_rfl⟩
    · exact hc.1 hn
      
    · exact hc.2 hn
      
    

theorem indepSuprLimsup (h_le : ∀ n, s n ≤ m0) (h_indep : IndepCat s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (⨆ n, s n) (limsup s f) μ := by
  suffices (⨆ a, ⨆ n ∈ ns a, s n) = ⨆ n, s n by
    rw [← this]
    exact indep_supr_directed_limsup h_le h_indep hf hns hnsp
  rw [supr_comm]
  refine' supr_congr fun n => _
  have : (⨆ (i : α) (H : n ∈ ns i), s n) = ⨆ h : ∃ i, n ∈ ns i, s n := by rw [supr_exists]
  haveI : Nonempty (∃ i : α, n ∈ ns i) := ⟨hns_univ n⟩
  rw [this, supr_const]

theorem indepLimsupSelf (h_le : ∀ n, s n ≤ m0) (h_indep : IndepCat s μ) (hf : ∀ t, p t → tᶜ ∈ f)
    (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a) :
    Indep (limsup s f) (limsup s f) μ :=
  indepOfIndepOfLeLeft (indepSuprLimsup h_le h_indep hf hns hnsp hns_univ) limsup_le_supr

theorem measure_zero_or_one_of_measurable_set_limsup (h_le : ∀ n, s n ≤ m0) (h_indep : IndepCat s μ)
    (hf : ∀ t, p t → tᶜ ∈ f) (hns : Directed (· ≤ ·) ns) (hnsp : ∀ a, p (ns a)) (hns_univ : ∀ n, ∃ a, n ∈ ns a)
    {t : Set Ω} (ht_tail : measurable_set[limsup s f] t) : μ t = 0 ∨ μ t = 1 :=
  measure_eq_zero_or_one_of_indep_set_self
    ((indepLimsupSelf h_le h_indep hf hns hnsp hns_univ).indepSetOfMeasurableSet ht_tail ht_tail)

end Abstract

section AtTop

variable [SemilatticeSup ι] [NoMaxOrder ι] [Nonempty ι]

theorem indepLimsupAtTopSelf (h_le : ∀ n, s n ≤ m0) (h_indep : IndepCat s μ) :
    Indep (limsup s atTop) (limsup s atTop) μ := by
  let ns : ι → Set ι := Set.IicCat
  have hnsp : ∀ i, BddAbove (ns i) := fun i => bdd_above_Iic
  refine' indep_limsup_self h_le h_indep _ _ hnsp _
  · simp only [mem_at_top_sets, ge_iff_le, Set.mem_compl_iff, BddAbove, UpperBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, a < b := exists_gt a
    refine' ⟨b, fun c hc hct => _⟩
    suffices : ∀ i ∈ t, i < c
    exact lt_irrefl c (this c hct)
    exact fun i hi => (ha hi).trans_lt (hb.trans_le hc)
    
  · exact Monotone.directed_le fun i j hij k hki => le_trans hki hij
    
  · exact fun n => ⟨n, le_rfl⟩
    

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1.
The tail σ-algebra `limsup s at_top` is the same as `⋂ n, ⋃ i ≥ n, s i`. -/
theorem measure_zero_or_one_of_measurable_set_limsup_at_top (h_le : ∀ n, s n ≤ m0) (h_indep : IndepCat s μ) {t : Set Ω}
    (ht_tail : measurable_set[limsup s atTop] t) : μ t = 0 ∨ μ t = 1 :=
  measure_eq_zero_or_one_of_indep_set_self ((indepLimsupAtTopSelf h_le h_indep).indepSetOfMeasurableSet ht_tail ht_tail)

end AtTop

section AtBot

variable [SemilatticeInf ι] [NoMinOrder ι] [Nonempty ι]

theorem indepLimsupAtBotSelf (h_le : ∀ n, s n ≤ m0) (h_indep : IndepCat s μ) :
    Indep (limsup s atBot) (limsup s atBot) μ := by
  let ns : ι → Set ι := Set.IciCat
  have hnsp : ∀ i, BddBelow (ns i) := fun i => bdd_below_Ici
  refine' indep_limsup_self h_le h_indep _ _ hnsp _
  · simp only [mem_at_bot_sets, ge_iff_le, Set.mem_compl_iff, BddBelow, LowerBounds, Set.Nonempty]
    rintro t ⟨a, ha⟩
    obtain ⟨b, hb⟩ : ∃ b, b < a := exists_lt a
    refine' ⟨b, fun c hc hct => _⟩
    suffices : ∀ i ∈ t, c < i
    exact lt_irrefl c (this c hct)
    exact fun i hi => hc.trans_lt (hb.trans_le (ha hi))
    
  · exact directed_of_inf fun i j hij k hki => hij.trans hki
    
  · exact fun n => ⟨n, le_rfl⟩
    

/-- **Kolmogorov's 0-1 law** : any event in the tail σ-algebra of an independent sequence of
sub-σ-algebras has probability 0 or 1. -/
theorem measure_zero_or_one_of_measurable_set_limsup_at_bot (h_le : ∀ n, s n ≤ m0) (h_indep : IndepCat s μ) {t : Set Ω}
    (ht_tail : measurable_set[limsup s atBot] t) : μ t = 0 ∨ μ t = 1 :=
  measure_eq_zero_or_one_of_indep_set_self ((indepLimsupAtBotSelf h_le h_indep).indepSetOfMeasurableSet ht_tail ht_tail)

end AtBot

end ZeroOneLaw

end ProbabilityTheory

