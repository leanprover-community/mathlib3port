/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathbin.Algebra.BigOperators.Intervals
import Mathbin.MeasureTheory.Measure.MeasureSpace
import Mathbin.MeasureTheory.PiSystem

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → set (set α)` is independent with respect to a measure `μ` if for
  any finite set of indices `s = {i_1, ..., i_n}`, for any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`,
  `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. It will be used for families of π-systems.
* A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
  measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
  define is independent. I.e., `m : ι → measurable_space α` is independent with respect to a
  measure `μ` if for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
  `f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i)`.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
  measurable space structures they generate: a set `s` generates the measurable space structure with
  measurable sets `∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
  space structures they generate: a function `f` for which we have a measurable space `m` on the
  codomain generates `measurable_space.comap f m`.

## Main statements

* TODO: `Indep_of_Indep_sets`: if π-systems are independent as sets of sets, then the
measurable space structures they generate are independent.
* `indep_of_indep_sets`: variant with two π-systems.

## Implementation notes

We provide one main definition of independence:
* `Indep_sets`: independence of a family of sets of sets `pi : ι → set (set α)`.
Three other independence notions are defined using `Indep_sets`:
* `Indep`: independence of a family of measurable space structures `m : ι → measurable_space α`,
* `Indep_set`: independence of a family of sets `s : ι → set α`,
* `Indep_fun`: independence of a family of functions. For measurable spaces
  `m : Π (i : ι), measurable_space (β i)`, we consider functions `f : Π (i : ι), α → β i`.

Additionally, we provide four corresponding statements for two measurable space structures (resp.
sets of sets, sets, functions) instead of a family. These properties are denoted by the same names
as for a family, but without a capital letter, for example `indep_fun` is the version of `Indep_fun`
for two functions.

The definition of independence for `Indep_sets` uses finite sets (`finset`). An alternative and
equivalent way of defining independence would have been to use countable sets.
TODO: prove that equivalence.

Most of the definitions and lemma in this file list all variables instead of using the `variables`
keyword at the beginning of a section, for example
`lemma indep.symm {α} {m₁ m₂ : measurable_space α} [measurable_space α] {μ : measure α} ...` .
This is intentional, to be able to control the order of the `measurable_space` variables. Indeed
when defining `μ` in the example above, the measurable space used is the last one defined, here
`[measurable_space α]`, and not `m₁` or `m₂`.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
Part A, Chapter 4.
-/


open MeasureTheory MeasurableSpace

open BigOperators Classical MeasureTheory

namespace ProbabilityTheory

section Definitions

/-- A family of sets of sets `π : ι → set (set α)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def IndepSets {α ι} [MeasurableSpace α] (π : ι → Set (Set α))
    (μ : Measureₓ α := by
      run_tac
        volume_tac) :
    Prop :=
  ∀ s : Finset ι {f : ι → Set α} H : ∀ i, i ∈ s → f i ∈ π i, μ (⋂ i ∈ s, f i) = ∏ i in s, μ (f i)

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def IndepSetsₓ {α} [MeasurableSpace α] (s1 s2 : Set (Set α))
    (μ : Measureₓ α := by
      run_tac
        volume_tac) :
    Prop :=
  ∀ t1 t2 : Set α, t1 ∈ s1 → t2 ∈ s2 → μ (t1 ∩ t2) = μ t1 * μ t2

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → measurable_space α` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def Indep {α ι} (m : ι → MeasurableSpace α) [MeasurableSpace α]
    (μ : Measureₓ α := by
      run_tac
        volume_tac) :
    Prop :=
  IndepSets (fun x => { s | measurable_set[m x] s }) μ

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def Indepₓ {α} (m₁ m₂ : MeasurableSpace α) [MeasurableSpace α]
    (μ : Measureₓ α := by
      run_tac
        volume_tac) :
    Prop :=
  IndepSetsₓ { s | measurable_set[m₁] s } { s | measurable_set[m₂] s } μ

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def IndepSet {α ι} [MeasurableSpace α] (s : ι → Set α)
    (μ : Measureₓ α := by
      run_tac
        volume_tac) :
    Prop :=
  Indep (fun i => generateFrom {s i}) μ

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def IndepSetₓ {α} [MeasurableSpace α] (s t : Set α)
    (μ : Measureₓ α := by
      run_tac
        volume_tac) :
    Prop :=
  Indepₓ (generateFrom {s}) (generateFrom {t}) μ

/-- A family of functions defined on the same space `α` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `α` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def IndepFun {α ι} [MeasurableSpace α] {β : ι → Type _} (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, α → β x)
    (μ : Measureₓ α := by
      run_tac
        volume_tac) :
    Prop :=
  Indep (fun x => MeasurableSpace.comap (f x) (m x)) μ

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def IndepFunₓ {α β γ} [MeasurableSpace α] [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] (f : α → β) (g : α → γ)
    (μ : Measureₓ α := by
      run_tac
        volume_tac) :
    Prop :=
  Indepₓ (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) μ

end Definitions

section Indep

theorem IndepSetsₓ.symm {α} {s₁ s₂ : Set (Set α)} [MeasurableSpace α] {μ : Measureₓ α} (h : IndepSetsₓ s₁ s₂ μ) :
    IndepSetsₓ s₂ s₁ μ := by
  intro t1 t2 ht1 ht2
  rw [Set.inter_comm, mul_comm]
  exact h t2 t1 ht2 ht1

theorem Indepₓ.symm {α} {m₁ m₂ : MeasurableSpace α} [MeasurableSpace α] {μ : Measureₓ α} (h : Indepₓ m₁ m₂ μ) :
    Indepₓ m₂ m₁ μ :=
  IndepSetsₓ.symm h

theorem indep_sets_of_indep_sets_of_le_left {α} {s₁ s₂ s₃ : Set (Set α)} [MeasurableSpace α] {μ : Measureₓ α}
    (h_indep : IndepSetsₓ s₁ s₂ μ) (h31 : s₃ ⊆ s₁) : IndepSetsₓ s₃ s₂ μ := fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 (Set.mem_of_subset_of_mem h31 ht1) ht2

theorem indep_sets_of_indep_sets_of_le_right {α} {s₁ s₂ s₃ : Set (Set α)} [MeasurableSpace α] {μ : Measureₓ α}
    (h_indep : IndepSetsₓ s₁ s₂ μ) (h32 : s₃ ⊆ s₂) : IndepSetsₓ s₁ s₃ μ := fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 ht1 (Set.mem_of_subset_of_mem h32 ht2)

theorem indep_of_indep_of_le_left {α} {m₁ m₂ m₃ : MeasurableSpace α} [MeasurableSpace α] {μ : Measureₓ α}
    (h_indep : Indepₓ m₁ m₂ μ) (h31 : m₃ ≤ m₁) : Indepₓ m₃ m₂ μ := fun t1 t2 ht1 ht2 => h_indep t1 t2 (h31 _ ht1) ht2

theorem indep_of_indep_of_le_right {α} {m₁ m₂ m₃ : MeasurableSpace α} [MeasurableSpace α] {μ : Measureₓ α}
    (h_indep : Indepₓ m₁ m₂ μ) (h32 : m₃ ≤ m₂) : Indepₓ m₁ m₃ μ := fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (h32 _ ht2)

theorem IndepSetsₓ.union {α} [MeasurableSpace α] {s₁ s₂ s' : Set (Set α)} {μ : Measureₓ α} (h₁ : IndepSetsₓ s₁ s' μ)
    (h₂ : IndepSetsₓ s₂ s' μ) : IndepSetsₓ (s₁ ∪ s₂) s' μ := by
  intro t1 t2 ht1 ht2
  cases' (Set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂
  · exact h₁ t1 t2 ht1₁ ht2
    
  · exact h₂ t1 t2 ht1₂ ht2
    

@[simp]
theorem IndepSetsₓ.union_iff {α} [MeasurableSpace α] {s₁ s₂ s' : Set (Set α)} {μ : Measureₓ α} :
    IndepSetsₓ (s₁ ∪ s₂) s' μ ↔ IndepSetsₓ s₁ s' μ ∧ IndepSetsₓ s₂ s' μ :=
  ⟨fun h =>
    ⟨indep_sets_of_indep_sets_of_le_left h (Set.subset_union_left s₁ s₂),
      indep_sets_of_indep_sets_of_le_left h (Set.subset_union_right s₁ s₂)⟩,
    fun h => IndepSetsₓ.union h.left h.right⟩

theorem IndepSetsₓ.Union {α ι} [MeasurableSpace α] {s : ι → Set (Set α)} {s' : Set (Set α)} {μ : Measureₓ α}
    (hyp : ∀ n, IndepSetsₓ (s n) s' μ) : IndepSetsₓ (⋃ n, s n) s' μ := by
  intro t1 t2 ht1 ht2
  rw [Set.mem_Union] at ht1
  cases' ht1 with n ht1
  exact hyp n t1 t2 ht1 ht2

theorem IndepSetsₓ.inter {α} [MeasurableSpace α] {s₁ s' : Set (Set α)} (s₂ : Set (Set α)) {μ : Measureₓ α}
    (h₁ : IndepSetsₓ s₁ s' μ) : IndepSetsₓ (s₁ ∩ s₂) s' μ := fun t1 t2 ht1 ht2 =>
  h₁ t1 t2 ((Set.mem_inter_iff _ _ _).mp ht1).left ht2

theorem IndepSetsₓ.Inter {α ι} [MeasurableSpace α] {s : ι → Set (Set α)} {s' : Set (Set α)} {μ : Measureₓ α}
    (h : ∃ n, IndepSetsₓ (s n) s' μ) : IndepSetsₓ (⋂ n, s n) s' μ := by
  intro t1 t2 ht1 ht2
  cases' h with n h
  exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2

theorem indep_sets_singleton_iff {α} [MeasurableSpace α] {s t : Set α} {μ : Measureₓ α} :
    IndepSetsₓ {s} {t} μ ↔ μ (s ∩ t) = μ s * μ t :=
  ⟨fun h => h s t rfl rfl, fun h s1 t1 hs1 ht1 => by
    rwa [set.mem_singleton_iff.mp hs1, set.mem_singleton_iff.mp ht1]⟩

end Indep

/-! ### Deducing `indep` from `Indep` -/


section FromIndepToIndep

theorem IndepSets.indep_sets {α ι} {s : ι → Set (Set α)} [MeasurableSpace α] {μ : Measureₓ α} (h_indep : IndepSets s μ)
    {i j : ι} (hij : i ≠ j) : IndepSetsₓ (s i) (s j) μ := by
  intro t₁ t₂ ht₁ ht₂
  have hf_m : ∀ x : ι, x ∈ {i, j} → ite (x = i) t₁ t₂ ∈ s x := by
    intro x hx
    cases' finset.mem_insert.mp hx with hx hx
    · simp [hx, ht₁]
      
    · simp [finset.mem_singleton.mp hx, hij.symm, ht₂]
      
  have h1 : t₁ = ite (i = i) t₁ t₂ := by
    simp only [if_true, eq_self_iff_true]
  have h2 : t₂ = ite (j = i) t₁ t₂ := by
    simp only [hij.symm, if_false]
  have h_inter : (⋂ (t : ι) (H : t ∈ ({i, j} : Finset ι)), ite (t = i) t₁ t₂) = ite (i = i) t₁ t₂ ∩ ite (j = i) t₁ t₂ :=
    by
    simp only [Finset.set_bInter_singleton, Finset.set_bInter_insert]
  have h_prod :
    (∏ t : ι in ({i, j} : Finset ι), μ (ite (t = i) t₁ t₂)) = μ (ite (i = i) t₁ t₂) * μ (ite (j = i) t₁ t₂) := by
    simp only [hij, Finset.prod_singleton, Finset.prod_insert, not_false_iff, Finset.mem_singleton]
  rw [h1]
  nth_rw 1[h2]
  nth_rw 3[h2]
  rw [← h_inter, ← h_prod, h_indep {i, j} hf_m]

theorem Indep.indep {α ι} {m : ι → MeasurableSpace α} [MeasurableSpace α] {μ : Measureₓ α} (h_indep : Indep m μ)
    {i j : ι} (hij : i ≠ j) : Indepₓ (m i) (m j) μ := by
  change indep_sets ((fun x => measurable_set[m x]) i) ((fun x => measurable_set[m x]) j) μ
  exact Indep_sets.indep_sets h_indep hij

end FromIndepToIndep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

/-! ### Independence of measurable space structures implies independence of generating π-systems -/


theorem Indep.Indep_sets {α ι} [MeasurableSpace α] {μ : Measureₓ α} {m : ι → MeasurableSpace α} {s : ι → Set (Set α)}
    (hms : ∀ n, m n = generateFrom (s n)) (h_indep : Indep m μ) : IndepSets s μ := fun S f hfs =>
  (h_indep S) fun x hxS => ((hms x).symm ▸ measurable_set_generate_from (hfs x hxS) : measurable_set[m x] (f x))

theorem Indepₓ.indep_sets {α} [MeasurableSpace α] {μ : Measureₓ α} {s1 s2 : Set (Set α)}
    (h_indep : Indepₓ (generateFrom s1) (generateFrom s2) μ) : IndepSetsₓ s1 s2 μ := fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 (measurable_set_generate_from ht1) (measurable_set_generate_from ht2)

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

/-! ### Independence of generating π-systems implies independence of measurable space structures -/


private theorem indep_sets.indep_aux {α} {m2 : MeasurableSpace α} {m : MeasurableSpace α} {μ : Measureₓ α}
    [IsProbabilityMeasure μ] {p1 p2 : Set (Set α)} (h2 : m2 ≤ m) (hp2 : IsPiSystem p2) (hpm2 : m2 = generateFrom p2)
    (hyp : IndepSetsₓ p1 p2 μ) {t1 t2 : Set α} (ht1 : t1 ∈ p1) (ht2m : measurable_set[m2] t2) :
    μ (t1 ∩ t2) = μ t1 * μ t2 := by
  let μ_inter := μ.restrict t1
  let ν := μ t1 • μ
  have h_univ : μ_inter Set.Univ = ν Set.Univ := by
    rw [measure.restrict_apply_univ, measure.smul_apply, smul_eq_mul, measure_univ, mul_oneₓ]
  have : is_finite_measure μ_inter := @restrict.is_finite_measure α _ t1 μ ⟨measure_lt_top μ t1⟩
  rw [Set.inter_comm, ← @measure.restrict_apply α _ μ t1 t2 (h2 t2 ht2m)]
  refine' ext_on_measurable_space_of_generate_finite m p2 (fun t ht => _) h2 hpm2 hp2 h_univ ht2m
  have ht2 : measurable_set[m] t := by
    refine' h2 _ _
    rw [hpm2]
    exact measurable_set_generate_from ht
  rw [measure.restrict_apply ht2, measure.smul_apply, Set.inter_comm]
  exact hyp t1 t ht1 ht

theorem IndepSetsₓ.indep {α} {m1 m2 : MeasurableSpace α} {m : MeasurableSpace α} {μ : Measureₓ α}
    [IsProbabilityMeasure μ] {p1 p2 : Set (Set α)} (h1 : m1 ≤ m) (h2 : m2 ≤ m) (hp1 : IsPiSystem p1)
    (hp2 : IsPiSystem p2) (hpm1 : m1 = generateFrom p1) (hpm2 : m2 = generateFrom p2) (hyp : IndepSetsₓ p1 p2 μ) :
    Indepₓ m1 m2 μ := by
  intro t1 t2 ht1 ht2
  let μ_inter := μ.restrict t2
  let ν := μ t2 • μ
  have h_univ : μ_inter Set.Univ = ν Set.Univ := by
    rw [measure.restrict_apply_univ, measure.smul_apply, smul_eq_mul, measure_univ, mul_oneₓ]
  have : is_finite_measure μ_inter := @restrict.is_finite_measure α _ t2 μ ⟨measure_lt_top μ t2⟩
  rw [mul_comm, ← @measure.restrict_apply α _ μ t2 t1 (h1 t1 ht1)]
  refine' ext_on_measurable_space_of_generate_finite m p1 (fun t ht => _) h1 hpm1 hp1 h_univ ht1
  have ht1 : measurable_set[m] t := by
    refine' h1 _ _
    rw [hpm1]
    exact measurable_set_generate_from ht
  rw [measure.restrict_apply ht1, measure.smul_apply, smul_eq_mul, mul_comm]
  exact indep_sets.indep_aux h2 hp2 hpm2 hyp ht ht2

end FromPiSystemsToMeasurableSpaces

section IndepSet

/-! ### Independence of measurable sets

We prove the following equivalences on `indep_set`, for measurable sets `s, t`.
* `indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `indep_set s t μ ↔ indep_sets {s} {t} μ`.
-/


variable {α : Type _} [MeasurableSpace α] {s t : Set α} (S T : Set (Set α))

theorem indep_set_iff_indep_sets_singleton (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (μ : Measureₓ α := by
      run_tac
        volume_tac)
    [IsProbabilityMeasure μ] : IndepSetₓ s t μ ↔ IndepSetsₓ {s} {t} μ :=
  ⟨Indepₓ.indep_sets, fun h =>
    IndepSetsₓ.indep
      (generate_from_le fun u hu => by
        rwa [set.mem_singleton_iff.mp hu])
      (generate_from_le fun u hu => by
        rwa [set.mem_singleton_iff.mp hu])
      (IsPiSystem.singleton s) (IsPiSystem.singleton t) rfl rfl h⟩

theorem indep_set_iff_measure_inter_eq_mul (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (μ : Measureₓ α := by
      run_tac
        volume_tac)
    [IsProbabilityMeasure μ] : IndepSetₓ s t μ ↔ μ (s ∩ t) = μ s * μ t :=
  (indep_set_iff_indep_sets_singleton hs_meas ht_meas μ).trans indep_sets_singleton_iff

theorem IndepSetsₓ.indep_set_of_mem (hs : s ∈ S) (ht : t ∈ T) (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (μ : Measureₓ α := by
      run_tac
        volume_tac)
    [IsProbabilityMeasure μ] (h_indep : IndepSetsₓ S T μ) : IndepSetₓ s t μ :=
  (indep_set_iff_measure_inter_eq_mul hs_meas ht_meas μ).mpr (h_indep s t hs ht)

end IndepSet

section IndepFun

variable {α β β' γ γ' : Type _} {mα : MeasurableSpace α} {μ : Measureₓ α}

theorem IndepFunₓ.ae_eq {mβ : MeasurableSpace β} {f g f' g' : α → β} (hfg : IndepFunₓ f g μ) (hf : f =ᵐ[μ] f')
    (hg : g =ᵐ[μ] g') : IndepFunₓ f' g' μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  have h1 : f ⁻¹' A =ᵐ[μ] f' ⁻¹' A := hf.fun_comp A
  have h2 : g ⁻¹' B =ᵐ[μ] g' ⁻¹' B := hg.fun_comp B
  rw [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]
  exact hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩

theorem IndepFunₓ.comp {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} {mγ : MeasurableSpace γ}
    {mγ' : MeasurableSpace γ'} {f : α → β} {g : α → β'} {φ : β → γ} {ψ : β' → γ'} (hfg : IndepFunₓ f g μ)
    (hφ : Measurable φ) (hψ : Measurable ψ) : IndepFunₓ (φ ∘ f) (ψ ∘ g) μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  apply hfg
  · exact ⟨φ ⁻¹' A, hφ hA, set.preimage_comp.symm⟩
    
  · exact ⟨ψ ⁻¹' B, hψ hB, set.preimage_comp.symm⟩
    

end IndepFun

end ProbabilityTheory

