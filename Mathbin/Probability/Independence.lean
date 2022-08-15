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

open BigOperators Classical MeasureTheory

namespace ProbabilityTheory

section Definitions

/-- A family of sets of sets `π : ι → set (set Ω)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def IndepSets {Ω ι} [MeasurableSpace Ω] (π : ι → Set (Set Ω))
    (μ : Measureₓ Ω := by
      run_tac
        volume_tac) :
    Prop :=
  ∀ (s : Finset ι) {f : ι → Set Ω} (H : ∀ i, i ∈ s → f i ∈ π i), μ (⋂ i ∈ s, f i) = ∏ i in s, μ (f i)

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def IndepSetsₓ {Ω} [MeasurableSpace Ω] (s1 s2 : Set (Set Ω))
    (μ : Measureₓ Ω := by
      run_tac
        volume_tac) :
    Prop :=
  ∀ t1 t2 : Set Ω, t1 ∈ s1 → t2 ∈ s2 → μ (t1 ∩ t2) = μ t1 * μ t2

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → measurable_space Ω` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def Indep {Ω ι} (m : ι → MeasurableSpace Ω) [MeasurableSpace Ω]
    (μ : Measureₓ Ω := by
      run_tac
        volume_tac) :
    Prop :=
  IndepSets (fun x => { s | measurable_set[m x] s }) μ

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def Indepₓ {Ω} (m₁ m₂ : MeasurableSpace Ω) [MeasurableSpace Ω]
    (μ : Measureₓ Ω := by
      run_tac
        volume_tac) :
    Prop :=
  IndepSetsₓ { s | measurable_set[m₁] s } { s | measurable_set[m₂] s } μ

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def IndepSet {Ω ι} [MeasurableSpace Ω] (s : ι → Set Ω)
    (μ : Measureₓ Ω := by
      run_tac
        volume_tac) :
    Prop :=
  Indep (fun i => generateFrom {s i}) μ

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def IndepSetₓ {Ω} [MeasurableSpace Ω] (s t : Set Ω)
    (μ : Measureₓ Ω := by
      run_tac
        volume_tac) :
    Prop :=
  Indepₓ (generateFrom {s}) (generateFrom {t}) μ

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `Ω` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def IndepFun {Ω ι} [MeasurableSpace Ω] {β : ι → Type _} (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, Ω → β x)
    (μ : Measureₓ Ω := by
      run_tac
        volume_tac) :
    Prop :=
  Indep (fun x => MeasurableSpace.comap (f x) (m x)) μ

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def IndepFunₓ {Ω β γ} [MeasurableSpace Ω] [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] (f : Ω → β) (g : Ω → γ)
    (μ : Measureₓ Ω := by
      run_tac
        volume_tac) :
    Prop :=
  Indepₓ (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) μ

end Definitions

section Indep

theorem IndepSetsₓ.symm {Ω} {s₁ s₂ : Set (Set Ω)} [MeasurableSpace Ω] {μ : Measureₓ Ω} (h : IndepSetsₓ s₁ s₂ μ) :
    IndepSetsₓ s₂ s₁ μ := by
  intro t1 t2 ht1 ht2
  rw [Set.inter_comm, mul_comm]
  exact h t2 t1 ht2 ht1

theorem Indepₓ.symm {Ω} {m₁ m₂ : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measureₓ Ω} (h : Indepₓ m₁ m₂ μ) :
    Indepₓ m₂ m₁ μ :=
  IndepSetsₓ.symm h

theorem indep_sets_of_indep_sets_of_le_left {Ω} {s₁ s₂ s₃ : Set (Set Ω)} [MeasurableSpace Ω] {μ : Measureₓ Ω}
    (h_indep : IndepSetsₓ s₁ s₂ μ) (h31 : s₃ ⊆ s₁) : IndepSetsₓ s₃ s₂ μ := fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 (Set.mem_of_subset_of_mem h31 ht1) ht2

theorem indep_sets_of_indep_sets_of_le_right {Ω} {s₁ s₂ s₃ : Set (Set Ω)} [MeasurableSpace Ω] {μ : Measureₓ Ω}
    (h_indep : IndepSetsₓ s₁ s₂ μ) (h32 : s₃ ⊆ s₂) : IndepSetsₓ s₁ s₃ μ := fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 ht1 (Set.mem_of_subset_of_mem h32 ht2)

theorem indep_of_indep_of_le_left {Ω} {m₁ m₂ m₃ : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measureₓ Ω}
    (h_indep : Indepₓ m₁ m₂ μ) (h31 : m₃ ≤ m₁) : Indepₓ m₃ m₂ μ := fun t1 t2 ht1 ht2 => h_indep t1 t2 (h31 _ ht1) ht2

theorem indep_of_indep_of_le_right {Ω} {m₁ m₂ m₃ : MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measureₓ Ω}
    (h_indep : Indepₓ m₁ m₂ μ) (h32 : m₃ ≤ m₂) : Indepₓ m₁ m₃ μ := fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (h32 _ ht2)

theorem IndepSetsₓ.union {Ω} [MeasurableSpace Ω] {s₁ s₂ s' : Set (Set Ω)} {μ : Measureₓ Ω} (h₁ : IndepSetsₓ s₁ s' μ)
    (h₂ : IndepSetsₓ s₂ s' μ) : IndepSetsₓ (s₁ ∪ s₂) s' μ := by
  intro t1 t2 ht1 ht2
  cases' (Set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂
  · exact h₁ t1 t2 ht1₁ ht2
    
  · exact h₂ t1 t2 ht1₂ ht2
    

@[simp]
theorem IndepSetsₓ.union_iff {Ω} [MeasurableSpace Ω] {s₁ s₂ s' : Set (Set Ω)} {μ : Measureₓ Ω} :
    IndepSetsₓ (s₁ ∪ s₂) s' μ ↔ IndepSetsₓ s₁ s' μ ∧ IndepSetsₓ s₂ s' μ :=
  ⟨fun h =>
    ⟨indep_sets_of_indep_sets_of_le_left h (Set.subset_union_left s₁ s₂),
      indep_sets_of_indep_sets_of_le_left h (Set.subset_union_right s₁ s₂)⟩,
    fun h => IndepSetsₓ.union h.left h.right⟩

theorem IndepSetsₓ.Union {Ω ι} [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {μ : Measureₓ Ω}
    (hyp : ∀ n, IndepSetsₓ (s n) s' μ) : IndepSetsₓ (⋃ n, s n) s' μ := by
  intro t1 t2 ht1 ht2
  rw [Set.mem_Union] at ht1
  cases' ht1 with n ht1
  exact hyp n t1 t2 ht1 ht2

theorem IndepSetsₓ.inter {Ω} [MeasurableSpace Ω] {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω)) {μ : Measureₓ Ω}
    (h₁ : IndepSetsₓ s₁ s' μ) : IndepSetsₓ (s₁ ∩ s₂) s' μ := fun t1 t2 ht1 ht2 =>
  h₁ t1 t2 ((Set.mem_inter_iff _ _ _).mp ht1).left ht2

theorem IndepSetsₓ.Inter {Ω ι} [MeasurableSpace Ω] {s : ι → Set (Set Ω)} {s' : Set (Set Ω)} {μ : Measureₓ Ω}
    (h : ∃ n, IndepSetsₓ (s n) s' μ) : IndepSetsₓ (⋂ n, s n) s' μ := by
  intro t1 t2 ht1 ht2
  cases' h with n h
  exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2

theorem indep_sets_singleton_iff {Ω} [MeasurableSpace Ω] {s t : Set Ω} {μ : Measureₓ Ω} :
    IndepSetsₓ {s} {t} μ ↔ μ (s ∩ t) = μ s * μ t :=
  ⟨fun h => h s t rfl rfl, fun h s1 t1 hs1 ht1 => by
    rwa [set.mem_singleton_iff.mp hs1, set.mem_singleton_iff.mp ht1]⟩

end Indep

/-! ### Deducing `indep` from `Indep` -/


section FromIndepToIndep

theorem IndepSets.indep_sets {Ω ι} {s : ι → Set (Set Ω)} [MeasurableSpace Ω] {μ : Measureₓ Ω} (h_indep : IndepSets s μ)
    {i j : ι} (hij : i ≠ j) : IndepSetsₓ (s i) (s j) μ := by
  intro t₁ t₂ ht₁ ht₂
  have hf_m : ∀ x : ι, x ∈ {i, j} → ite (x = i) t₁ t₂ ∈ s x := by
    intro x hx
    cases' finset.mem_insert.mp hx with hx hx
    · simp [← hx, ← ht₁]
      
    · simp [← finset.mem_singleton.mp hx, ← hij.symm, ← ht₂]
      
  have h1 : t₁ = ite (i = i) t₁ t₂ := by
    simp only [← if_true, ← eq_self_iff_true]
  have h2 : t₂ = ite (j = i) t₁ t₂ := by
    simp only [← hij.symm, ← if_false]
  have h_inter : (⋂ (t : ι) (H : t ∈ ({i, j} : Finset ι)), ite (t = i) t₁ t₂) = ite (i = i) t₁ t₂ ∩ ite (j = i) t₁ t₂ :=
    by
    simp only [← Finset.set_bInter_singleton, ← Finset.set_bInter_insert]
  have h_prod :
    (∏ t : ι in ({i, j} : Finset ι), μ (ite (t = i) t₁ t₂)) = μ (ite (i = i) t₁ t₂) * μ (ite (j = i) t₁ t₂) := by
    simp only [← hij, ← Finset.prod_singleton, ← Finset.prod_insert, ← not_false_iff, ← Finset.mem_singleton]
  rw [h1]
  nth_rw 1[h2]
  nth_rw 3[h2]
  rw [← h_inter, ← h_prod, h_indep {i, j} hf_m]

theorem Indep.indep {Ω ι} {m : ι → MeasurableSpace Ω} [MeasurableSpace Ω] {μ : Measureₓ Ω} (h_indep : Indep m μ)
    {i j : ι} (hij : i ≠ j) : Indepₓ (m i) (m j) μ := by
  change indep_sets ((fun x => measurable_set[m x]) i) ((fun x => measurable_set[m x]) j) μ
  exact Indep_sets.indep_sets h_indep hij

theorem IndepFun.indep_fun {Ω ι : Type _} {m₀ : MeasurableSpace Ω} {μ : Measureₓ Ω} {β : ι → Type _}
    {m : ∀ x, MeasurableSpace (β x)} {f : ∀ i, Ω → β i} (hf_Indep : IndepFun m f μ) {i j : ι} (hij : i ≠ j) :
    IndepFunₓ (f i) (f j) μ :=
  hf_Indep.indep hij

end FromIndepToIndep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

/-! ### Independence of measurable space structures implies independence of generating π-systems -/


theorem Indep.Indep_sets {Ω ι} [MeasurableSpace Ω] {μ : Measureₓ Ω} {m : ι → MeasurableSpace Ω} {s : ι → Set (Set Ω)}
    (hms : ∀ n, m n = generateFrom (s n)) (h_indep : Indep m μ) : IndepSets s μ := fun S f hfs =>
  (h_indep S) fun x hxS => ((hms x).symm ▸ measurable_set_generate_from (hfs x hxS) : measurable_set[m x] (f x))

theorem Indepₓ.indep_sets {Ω} [MeasurableSpace Ω] {μ : Measureₓ Ω} {s1 s2 : Set (Set Ω)}
    (h_indep : Indepₓ (generateFrom s1) (generateFrom s2) μ) : IndepSetsₓ s1 s2 μ := fun t1 t2 ht1 ht2 =>
  h_indep t1 t2 (measurable_set_generate_from ht1) (measurable_set_generate_from ht2)

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

/-! ### Independence of generating π-systems implies independence of measurable space structures -/


private theorem indep_sets.indep_aux {Ω} {m2 : MeasurableSpace Ω} {m : MeasurableSpace Ω} {μ : Measureₓ Ω}
    [IsProbabilityMeasure μ] {p1 p2 : Set (Set Ω)} (h2 : m2 ≤ m) (hp2 : IsPiSystem p2) (hpm2 : m2 = generateFrom p2)
    (hyp : IndepSetsₓ p1 p2 μ) {t1 t2 : Set Ω} (ht1 : t1 ∈ p1) (ht2m : measurable_set[m2] t2) :
    μ (t1 ∩ t2) = μ t1 * μ t2 := by
  let μ_inter := μ.restrict t1
  let ν := μ t1 • μ
  have h_univ : μ_inter Set.Univ = ν Set.Univ := by
    rw [measure.restrict_apply_univ, measure.smul_apply, smul_eq_mul, measure_univ, mul_oneₓ]
  haveI : is_finite_measure μ_inter := @restrict.is_finite_measure Ω _ t1 μ ⟨measure_lt_top μ t1⟩
  rw [Set.inter_comm, ← @measure.restrict_apply Ω _ μ t1 t2 (h2 t2 ht2m)]
  refine' ext_on_measurable_space_of_generate_finite m p2 (fun t ht => _) h2 hpm2 hp2 h_univ ht2m
  have ht2 : measurable_set[m] t := by
    refine' h2 _ _
    rw [hpm2]
    exact measurable_set_generate_from ht
  rw [measure.restrict_apply ht2, measure.smul_apply, Set.inter_comm]
  exact hyp t1 t ht1 ht

theorem IndepSetsₓ.indep {Ω} {m1 m2 : MeasurableSpace Ω} {m : MeasurableSpace Ω} {μ : Measureₓ Ω}
    [IsProbabilityMeasure μ] {p1 p2 : Set (Set Ω)} (h1 : m1 ≤ m) (h2 : m2 ≤ m) (hp1 : IsPiSystem p1)
    (hp2 : IsPiSystem p2) (hpm1 : m1 = generateFrom p1) (hpm2 : m2 = generateFrom p2) (hyp : IndepSetsₓ p1 p2 μ) :
    Indepₓ m1 m2 μ := by
  intro t1 t2 ht1 ht2
  let μ_inter := μ.restrict t2
  let ν := μ t2 • μ
  have h_univ : μ_inter Set.Univ = ν Set.Univ := by
    rw [measure.restrict_apply_univ, measure.smul_apply, smul_eq_mul, measure_univ, mul_oneₓ]
  haveI : is_finite_measure μ_inter := @restrict.is_finite_measure Ω _ t2 μ ⟨measure_lt_top μ t2⟩
  rw [mul_comm, ← @measure.restrict_apply Ω _ μ t2 t1 (h1 t1 ht1)]
  refine' ext_on_measurable_space_of_generate_finite m p1 (fun t ht => _) h1 hpm1 hp1 h_univ ht1
  have ht1 : measurable_set[m] t := by
    refine' h1 _ _
    rw [hpm1]
    exact measurable_set_generate_from ht
  rw [measure.restrict_apply ht1, measure.smul_apply, smul_eq_mul, mul_comm]
  exact indep_sets.indep_aux h2 hp2 hpm2 hyp ht ht2

variable {Ω ι : Type _} {m0 : MeasurableSpace Ω} {μ : Measureₓ Ω}

theorem IndepSets.pi_Union_Inter_singleton {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι} (hp_ind : IndepSets π μ)
    (haS : a ∉ S) : IndepSetsₓ (PiUnionInter π {S}) (π a) μ := by
  rintro t1 t2 ⟨s, hs_mem, ft1, hft1_mem, ht1_eq⟩ ht2_mem_pia
  rw [Set.mem_singleton_iff] at hs_mem
  subst hs_mem
  let f := fun n => ite (n = a) t2 (ite (n ∈ s) (ft1 n) Set.Univ)
  have h_f_mem : ∀, ∀ n ∈ insert a s, ∀, f n ∈ π n := by
    intro n hn_mem_insert
    simp_rw [f]
    cases' finset.mem_insert.mp hn_mem_insert with hn_mem hn_mem
    · simp [← hn_mem, ← ht2_mem_pia]
      
    · have hn_ne_a : n ≠ a := by
        rintro rfl
        exact haS hn_mem
      simp [← hn_ne_a, ← hn_mem, ← hft1_mem n hn_mem]
      
  have h_f_mem_pi : ∀, ∀ n ∈ s, ∀, f n ∈ π n := fun x hxS =>
    h_f_mem x
      (by
        simp [← hxS])
  have h_t1 : t1 = ⋂ n ∈ s, f n := by
    suffices h_forall : ∀, ∀ n ∈ s, ∀, f n = ft1 n
    · rw [ht1_eq]
      congr with n x
      congr with hns y
      simp only [← (h_forall n hns).symm]
      
    intro n hnS
    have hn_ne_a : n ≠ a := by
      rintro rfl
      exact haS hnS
    simp_rw [f, if_pos hnS, if_neg hn_ne_a]
  have h_μ_t1 : μ t1 = ∏ n in s, μ (f n) := by
    rw [h_t1, ← hp_ind s h_f_mem_pi]
  have h_t2 : t2 = f a := by
    simp_rw [f]
    simp
  have h_μ_inter : μ (t1 ∩ t2) = ∏ n in insert a s, μ (f n) := by
    have h_t1_inter_t2 : t1 ∩ t2 = ⋂ n ∈ insert a s, f n := by
      rw [h_t1, h_t2, Finset.set_bInter_insert, Set.inter_comm]
    rw [h_t1_inter_t2, ← hp_ind (insert a s) h_f_mem]
  rw [h_μ_inter, Finset.prod_insert haS, h_t2, mul_comm, h_μ_t1]

/-- Auxiliary lemma for `Indep_sets.Indep`. -/
theorem IndepSets.Indep_aux [IsProbabilityMeasure μ] (m : ι → MeasurableSpace Ω) (h_le : ∀ i, m i ≤ m0)
    (π : ι → Set (Set Ω)) (h_pi : ∀ n, IsPiSystem (π n)) (hp_univ : ∀ i, Set.Univ ∈ π i)
    (h_generate : ∀ i, m i = generateFrom (π i)) (h_ind : IndepSets π μ) : Indep m μ := by
  refine'
    Finset.induction
      (by
        simp [← measure_univ])
      _
  intro a S ha_notin_S h_rec f hf_m
  have hf_m_S : ∀, ∀ x ∈ S, ∀, measurable_set[m x] (f x) := fun x hx =>
    hf_m x
      (by
        simp [← hx])
  rw [Finset.set_bInter_insert, Finset.prod_insert ha_notin_S, ← h_rec hf_m_S]
  let p := PiUnionInter π {S}
  set m_p := generate_from p with hS_eq_generate
  have h_indep : indep m_p (m a) μ := by
    have hp : IsPiSystem p := is_pi_system_pi_Union_Inter π h_pi {S} (sup_closed_singleton S)
    have h_le' : ∀ i, generate_from (π i) ≤ m0 := fun i => (h_generate i).symm.trans_le (h_le i)
    have hm_p : m_p ≤ m0 := generate_from_pi_Union_Inter_le π h_le' {S}
    exact
      indep_sets.indep hm_p (h_le a) hp (h_pi a) hS_eq_generate (h_generate a)
        (h_ind.pi_Union_Inter_singleton ha_notin_S)
  refine' h_indep.symm (f a) (⋂ n ∈ S, f n) (hf_m a (Finset.mem_insert_self a S)) _
  have h_le_p : ∀, ∀ i ∈ S, ∀, m i ≤ m_p := by
    intro n hn
    rw [hS_eq_generate, h_generate n]
    exact le_generate_from_pi_Union_Inter {S} hp_univ (Set.mem_singleton _) hn
  have h_S_f : ∀, ∀ i ∈ S, ∀, measurable_set[m_p] (f i) := fun i hi => (h_le_p i hi) (f i) (hf_m_S i hi)
  exact S.measurable_set_bInter h_S_f

/-- The measurable space structures generated by independent pi-systems are independent. -/
theorem IndepSets.Indep [IsProbabilityMeasure μ] (m : ι → MeasurableSpace Ω) (h_le : ∀ i, m i ≤ m0)
    (π : ι → Set (Set Ω)) (h_pi : ∀ n, IsPiSystem (π n)) (h_generate : ∀ i, m i = generateFrom (π i))
    (h_ind : IndepSets π μ) : Indep m μ := by
  -- We want to apply `Indep_sets.Indep_aux`, but `π i` does not contain `univ`, hence we replace
  -- `π` with a new augmented pi-system `π'`, and prove all hypotheses for that pi-system.
  let π' := fun i => insert Set.Univ (π i)
  have h_subset : ∀ i, π i ⊆ π' i := fun i => Set.subset_insert _ _
  have h_pi' : ∀ n, IsPiSystem (π' n) := fun n => (h_pi n).insert_univ
  have h_univ' : ∀ i, Set.Univ ∈ π' i := fun i => Set.mem_insert _ _
  have h_gen' : ∀ i, m i = generate_from (π' i) := by
    intro i
    rw [h_generate i, generate_from_insert_univ (π i)]
  have h_ind' : Indep_sets π' μ := by
    intro S f hfπ'
    let S' := Finset.filter (fun i => f i ≠ Set.Univ) S
    have h_mem : ∀, ∀ i ∈ S', ∀, f i ∈ π i := by
      intro i hi
      simp_rw [S', Finset.mem_filter] at hi
      cases hfπ' i hi.1
      · exact absurd h hi.2
        
      · exact h
        
    have h_left : (⋂ i ∈ S, f i) = ⋂ i ∈ S', f i := by
      ext1 x
      simp only [← Set.mem_Inter, ← Finset.mem_filter, ← Ne.def, ← and_imp]
      constructor
      · exact fun h i hiS hif => h i hiS
        
      · intro h i hiS
        by_cases' hfi_univ : f i = Set.Univ
        · rw [hfi_univ]
          exact Set.mem_univ _
          
        · exact h i hiS hfi_univ
          
        
    have h_right : (∏ i in S, μ (f i)) = ∏ i in S', μ (f i) := by
      rw [← Finset.prod_filter_mul_prod_filter_not S fun i => f i ≠ Set.Univ]
      simp only [← Ne.def, ← Finset.filter_congr_decidable, ← not_not]
      suffices (∏ x in Finset.filter (fun x => f x = Set.Univ) S, μ (f x)) = 1 by
        rw [this, mul_oneₓ]
      calc
        (∏ x in Finset.filter (fun x => f x = Set.Univ) S, μ (f x)) =
            ∏ x in Finset.filter (fun x => f x = Set.Univ) S, μ Set.Univ :=
          Finset.prod_congr rfl fun x hx => by
            rw [Finset.mem_filter] at hx
            rw [hx.2]
        _ = ∏ x in Finset.filter (fun x => f x = Set.Univ) S, 1 := Finset.prod_congr rfl fun _ _ => measure_univ
        _ = 1 := Finset.prod_const_one
        
    rw [h_left, h_right]
    exact h_ind S' h_mem
  exact Indep_sets.Indep_aux m h_le π' h_pi' h_univ' h_gen' h_ind'

end FromPiSystemsToMeasurableSpaces

section IndepSet

/-! ### Independence of measurable sets

We prove the following equivalences on `indep_set`, for measurable sets `s, t`.
* `indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `indep_set s t μ ↔ indep_sets {s} {t} μ`.
-/


variable {Ω : Type _} [MeasurableSpace Ω] {s t : Set Ω} (S T : Set (Set Ω))

theorem indep_set_iff_indep_sets_singleton (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (μ : Measureₓ Ω := by
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
    (μ : Measureₓ Ω := by
      run_tac
        volume_tac)
    [IsProbabilityMeasure μ] : IndepSetₓ s t μ ↔ μ (s ∩ t) = μ s * μ t :=
  (indep_set_iff_indep_sets_singleton hs_meas ht_meas μ).trans indep_sets_singleton_iff

theorem IndepSetsₓ.indep_set_of_mem (hs : s ∈ S) (ht : t ∈ T) (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
    (μ : Measureₓ Ω := by
      run_tac
        volume_tac)
    [IsProbabilityMeasure μ] (h_indep : IndepSetsₓ S T μ) : IndepSetₓ s t μ :=
  (indep_set_iff_measure_inter_eq_mul hs_meas ht_meas μ).mpr (h_indep s t hs ht)

end IndepSet

section IndepFun

/-! ### Independence of random variables

-/


variable {Ω β β' γ γ' : Type _} {mΩ : MeasurableSpace Ω} {μ : Measureₓ Ω} {f : Ω → β} {g : Ω → β'}

theorem indep_fun_iff_measure_inter_preimage_eq_mul {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} :
    IndepFunₓ f g μ ↔ ∀ s t, MeasurableSet s → MeasurableSet t → μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
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
  let setsβ : ∀ i : ι, Set (β i) := fun i => dite (i ∈ S) (fun hi_mem => (h_meas i hi_mem).some) fun _ => Set.Univ
  have h_measβ : ∀, ∀ i ∈ S, ∀, measurable_set[m i] (setsβ i) := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).some_spec.1
  have h_preim : ∀, ∀ i ∈ S, ∀, setsΩ i = f i ⁻¹' setsβ i := by
    intro i hi_mem
    simp_rw [setsβ, dif_pos hi_mem]
    exact (h_meas i hi_mem).some_spec.2.symm
  have h_left_eq : μ (⋂ i ∈ S, setsΩ i) = μ (⋂ i ∈ S, f i ⁻¹' setsβ i) := by
    congr with i x
    simp only [← Set.mem_Inter]
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
    IndepFunₓ f g μ ↔ ∀ s t, MeasurableSet s → MeasurableSet t → IndepSetₓ (f ⁻¹' s) (g ⁻¹' t) μ := by
  refine' indep_fun_iff_measure_inter_preimage_eq_mul.trans _
  constructor <;> intro h s t hs ht <;> specialize h s t hs ht
  · rwa [indep_set_iff_measure_inter_eq_mul (hf hs) (hg ht) μ]
    
  · rwa [← indep_set_iff_measure_inter_eq_mul (hf hs) (hg ht) μ]
    

theorem IndepFunₓ.ae_eq {mβ : MeasurableSpace β} {f g f' g' : Ω → β} (hfg : IndepFunₓ f g μ) (hf : f =ᵐ[μ] f')
    (hg : g =ᵐ[μ] g') : IndepFunₓ f' g' μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  have h1 : f ⁻¹' A =ᵐ[μ] f' ⁻¹' A := hf.fun_comp A
  have h2 : g ⁻¹' B =ᵐ[μ] g' ⁻¹' B := hg.fun_comp B
  rw [← measure_congr h1, ← measure_congr h2, ← measure_congr (h1.inter h2)]
  exact hfg _ _ ⟨_, hA, rfl⟩ ⟨_, hB, rfl⟩

theorem IndepFunₓ.comp {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'} {mγ : MeasurableSpace γ}
    {mγ' : MeasurableSpace γ'} {φ : β → γ} {ψ : β' → γ'} (hfg : IndepFunₓ f g μ) (hφ : Measurable φ)
    (hψ : Measurable ψ) : IndepFunₓ (φ ∘ f) (ψ ∘ g) μ := by
  rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  apply hfg
  · exact ⟨φ ⁻¹' A, hφ hA, set.preimage_comp.symm⟩
    
  · exact ⟨ψ ⁻¹' B, hψ hB, set.preimage_comp.symm⟩
    

/-- If `f` is a family of mutually independent random variables (`Indep_fun m f μ`) and `S, T` are
two disjoint finite index sets, then the tuple formed by `f i` for `i ∈ S` is independent of the
tuple `(f i)_i` for `i ∈ T`. -/
theorem IndepFun.indep_fun_finset [IsProbabilityMeasure μ] {ι : Type _} {β : ι → Type _}
    {m : ∀ i, MeasurableSpace (β i)} {f : ∀ i, Ω → β i} (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : IndepFun m f μ) (hf_meas : ∀ i, Measurable (f i)) :
    IndepFunₓ (fun a (i : S) => f i a) (fun a (i : T) => f i a) μ := by
  -- We introduce π-systems, build from the π-system of boxes which generates `measurable_space.pi`.
  let πSβ := Set.Pi (Set.Univ : Set S) '' Set.Pi (Set.Univ : Set S) fun i => { s : Set (β i) | measurable_set[m i] s }
  let πS := { s : Set Ω | ∃ t ∈ πSβ, (fun a (i : S) => f i a) ⁻¹' t = s }
  have hπS_pi : IsPiSystem πS := is_pi_system_pi.comap fun a i => f i a
  have hπS_gen : (measurable_space.pi.comap fun a (i : S) => f i a) = generate_from πS := by
    rw [generate_from_pi.symm, comap_generate_from]
    · congr with s
      simp only [← Set.mem_image, ← Set.mem_set_of_eq, ← exists_prop]
      
    · exact Finset.fintypeCoeSort S
      
  let πTβ := Set.Pi (Set.Univ : Set T) '' Set.Pi (Set.Univ : Set T) fun i => { s : Set (β i) | measurable_set[m i] s }
  let πT := { s : Set Ω | ∃ t ∈ πTβ, (fun a (i : T) => f i a) ⁻¹' t = s }
  have hπT_pi : IsPiSystem πT := is_pi_system_pi.comap fun a i => f i a
  have hπT_gen : (measurable_space.pi.comap fun a (i : T) => f i a) = generate_from πT := by
    rw [generate_from_pi.symm, comap_generate_from]
    · congr with s
      simp only [← Set.mem_image, ← Set.mem_set_of_eq, ← exists_prop]
      
    · exact Finset.fintypeCoeSort T
      
  -- To prove independence, we prove independence of the generating π-systems.
  refine'
    indep_sets.indep (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i))
      (Measurable.comap_le (measurable_pi_iff.mpr fun i => hf_meas i)) hπS_pi hπT_pi hπS_gen hπT_gen _
  rintro _ _ ⟨s, ⟨sets_s, hs1, hs2⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2⟩, rfl⟩
  simp only [← Set.mem_univ_pi, ← Set.mem_set_of_eq] at hs1 ht1
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
  have h_meas_s' : ∀, ∀ i ∈ S, ∀, MeasurableSet (sets_s' i) := by
    intro i hi
    rw [h_sets_s'_eq hi]
    exact hs1 _
  have h_meas_t' : ∀, ∀ i ∈ T, ∀, MeasurableSet (sets_t' i) := by
    intro i hi
    simp_rw [sets_t', dif_pos hi]
    exact ht1 _
  have h_eq_inter_S : (fun (ω : Ω) (i : ↥S) => f (↑i) ω) ⁻¹' Set.Pi Set.Univ sets_s = ⋂ i ∈ S, f i ⁻¹' sets_s' i := by
    ext1 x
    simp only [← Set.mem_preimage, ← Set.mem_univ_pi, ← Set.mem_Inter]
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
    simp only [← Set.mem_preimage, ← Set.mem_univ_pi, ← Set.mem_Inter]
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
    simp only [← Set.mem_inter_eq, ← Set.mem_Inter, ← Set.mem_preimage, ← Finset.mem_union]
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
    

theorem IndepFun.indep_fun_prod [IsProbabilityMeasure μ] {ι : Type _} {β : ι → Type _} {m : ∀ i, MeasurableSpace (β i)}
    {f : ∀ i, Ω → β i} (hf_Indep : IndepFun m f μ) (hf_meas : ∀ i, Measurable (f i)) (i j k : ι) (hik : i ≠ k)
    (hjk : j ≠ k) : IndepFunₓ (fun a => (f i a, f j a)) (f k) μ := by
  classical
  have h_right :
    f k =
      (fun p : ∀ j : ({k} : Finset ι), β j => p ⟨k, Finset.mem_singleton_self k⟩) ∘ fun a (j : ({k} : Finset ι)) =>
        f j a :=
    rfl
  have h_meas_right : Measurable fun p : ∀ j : ({k} : Finset ι), β j => p ⟨k, Finset.mem_singleton_self k⟩ :=
    measurable_pi_apply ⟨k, Finset.mem_singleton_self k⟩
  let s : Finset ι := {i, j}
  have h_left :
    (fun ω => (f i ω, f j ω)) =
      (fun p : ∀ l : s, β l =>
          (p ⟨i, Finset.mem_insert_self i _⟩, p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)) ∘
        fun a (j : s) => f j a :=
    by
    ext1 a
    simp only [← Prod.mk.inj_iff]
    constructor <;> rfl
  have h_meas_left :
    Measurable fun p : ∀ l : s, β l =>
      (p ⟨i, Finset.mem_insert_self i _⟩, p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) :=
    Measurable.prod (measurable_pi_apply ⟨i, Finset.mem_insert_self i {j}⟩)
      (measurable_pi_apply ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self j)⟩)
  rw [h_left, h_right]
  refine' (hf_Indep.indep_fun_finset s {k} _ hf_meas).comp h_meas_left h_meas_right
  intro x hx
  simp only [← Finset.inf_eq_inter, ← Finset.mem_inter, ← Finset.mem_insert, ← Finset.mem_singleton] at hx
  simp only [← Finset.bot_eq_empty, ← Finset.not_mem_empty]
  cases' hx.1 with hx_eq hx_eq <;> rw [hx_eq] at hx
  · exact hik hx.2
    
  · exact hjk hx.2
    

@[to_additive]
theorem IndepFun.mul [IsProbabilityMeasure μ] {ι : Type _} {β : Type _} {m : MeasurableSpace β} [Mul β]
    [HasMeasurableMul₂ β] {f : ι → Ω → β} (hf_Indep : IndepFun (fun _ => m) f μ) (hf_meas : ∀ i, Measurable (f i))
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) : IndepFunₓ (f i * f j) (f k) μ := by
  have : indep_fun (fun ω => (f i ω, f j ω)) (f k) μ := hf_Indep.indep_fun_prod hf_meas i j k hik hjk
  change indep_fun ((fun p : β × β => p.fst * p.snd) ∘ fun ω => (f i ω, f j ω)) (id ∘ f k) μ
  exact indep_fun.comp this (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
theorem IndepFun.indep_fun_finset_prod_of_not_mem [IsProbabilityMeasure μ] {ι : Type _} {β : Type _}
    {m : MeasurableSpace β} [CommMonoidₓ β] [HasMeasurableMul₂ β] {f : ι → Ω → β} (hf_Indep : IndepFun (fun _ => m) f μ)
    (hf_meas : ∀ i, Measurable (f i)) {s : Finset ι} {i : ι} (hi : i ∉ s) : IndepFunₓ (∏ j in s, f j) (f i) μ := by
  classical
  have h_right :
    f i =
      (fun p : ∀ j : ({i} : Finset ι), β => p ⟨i, Finset.mem_singleton_self i⟩) ∘ fun a (j : ({i} : Finset ι)) =>
        f j a :=
    rfl
  have h_meas_right : Measurable fun p : ∀ j : ({i} : Finset ι), β => p ⟨i, Finset.mem_singleton_self i⟩ :=
    measurable_pi_apply ⟨i, Finset.mem_singleton_self i⟩
  have h_left : (∏ j in s, f j) = (fun p : ∀ j : s, β => ∏ j, p j) ∘ fun a (j : s) => f j a := by
    ext1 a
    simp only [← Function.comp_app]
    have : (∏ j : ↥s, f (↑j) a) = (∏ j : ↥s, f ↑j) a := by
      rw [Finset.prod_apply]
    rw [this, Finset.prod_coe_sort]
  have h_meas_left : Measurable fun p : ∀ j : s, β => ∏ j, p j :=
    finset.univ.measurable_prod fun (j : ↥s) (H : j ∈ Finset.univ) => measurable_pi_apply j
  rw [h_left, h_right]
  exact
    (hf_Indep.indep_fun_finset s {i} (finset.disjoint_singleton_left.mpr hi).symm hf_meas).comp h_meas_left h_meas_right

@[to_additive]
theorem IndepFun.indep_fun_prod_range_succ [IsProbabilityMeasure μ] {β : Type _} {m : MeasurableSpace β} [CommMonoidₓ β]
    [HasMeasurableMul₂ β] {f : ℕ → Ω → β} (hf_Indep : IndepFun (fun _ => m) f μ) (hf_meas : ∀ i, Measurable (f i))
    (n : ℕ) : IndepFunₓ (∏ j in Finset.range n, f j) (f n) μ :=
  hf_Indep.indep_fun_finset_prod_of_not_mem hf_meas Finset.not_mem_range_self

end IndepFun

end ProbabilityTheory

