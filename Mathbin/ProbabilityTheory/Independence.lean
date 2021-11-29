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

open_locale BigOperators Classical

namespace ProbabilityTheory

section Definitions

/-- A family of sets of sets `π : ι → set (set α)` is independent with respect to a measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `.
It will be used for families of pi_systems. -/
def Indep_sets {α ι} [MeasurableSpace α] (π : ι → Set (Set α))
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  ∀ s : Finset ι {f : ι → Set α} H : ∀ i, i ∈ s → f i ∈ π i, μ (⋂(i : _)(_ : i ∈ s), f i) = ∏i in s, μ (f i)

/-- Two sets of sets `s₁, s₂` are independent with respect to a measure `μ` if for any sets
`t₁ ∈ p₁, t₂ ∈ s₂`, then `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep_sets {α} [MeasurableSpace α] (s1 s2 : Set (Set α))
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  ∀ t1 t2 : Set α, t1 ∈ s1 → t2 ∈ s2 → μ (t1 ∩ t2) = μ t1*μ t2

/-- A family of measurable space structures (i.e. of σ-algebras) is independent with respect to a
measure `μ` (typically defined on a finer σ-algebra) if the family of sets of measurable sets they
define is independent. `m : ι → measurable_space α` is independent with respect to measure `μ` if
for any finite set of indices `s = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, then `μ (⋂ i in s, f i) = ∏ i in s, μ (f i) `. -/
def Indep {α ι} (m : ι → MeasurableSpace α) [MeasurableSpace α]
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  Indep_sets (fun x => (m x).MeasurableSet') μ

/-- Two measurable space structures (or σ-algebras) `m₁, m₂` are independent with respect to a
measure `μ` (defined on a third σ-algebra) if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`,
`μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep {α} (m₁ m₂ : MeasurableSpace α) [MeasurableSpace α]
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  indep_sets m₁.measurable_set' m₂.measurable_set' μ

/-- A family of sets is independent if the family of measurable space structures they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def Indep_set {α ι} [MeasurableSpace α] (s : ι → Set α)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  Indep (fun i => generate_from {s i}) μ

/-- Two sets are independent if the two measurable space structures they generate are independent.
For a set `s`, the generated measurable space structure has measurable sets `∅, s, sᶜ, univ`. -/
def indep_set {α} [MeasurableSpace α] (s t : Set α)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  indep (generate_from {s}) (generate_from {t}) μ

/-- A family of functions defined on the same space `α` and taking values in possibly different
spaces, each with a measurable space structure, is independent if the family of measurable space
structures they generate on `α` is independent. For a function `g` with codomain having measurable
space structure `m`, the generated measurable space structure is `measurable_space.comap g m`. -/
def Indep_fun {α ι} [MeasurableSpace α] {β : ι → Type _} (m : ∀ x : ι, MeasurableSpace (β x)) (f : ∀ x : ι, α → β x)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  Indep (fun x => MeasurableSpace.comap (f x) (m x)) μ

/-- Two functions are independent if the two measurable space structures they generate are
independent. For a function `f` with codomain having measurable space structure `m`, the generated
measurable space structure is `measurable_space.comap f m`. -/
def indep_fun {α β γ} [MeasurableSpace α] [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ] (f : α → β) (g : α → γ)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac) :
  Prop :=
  indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) μ

end Definitions

section Indep

theorem indep_sets.symm {α} {s₁ s₂ : Set (Set α)} [MeasurableSpace α] {μ : Measureₓ α} (h : indep_sets s₁ s₂ μ) :
  indep_sets s₂ s₁ μ :=
  by 
    intro t1 t2 ht1 ht2 
    rw [Set.inter_comm, mul_commₓ]
    exact h t2 t1 ht2 ht1

theorem indep.symm {α} {m₁ m₂ : MeasurableSpace α} [MeasurableSpace α] {μ : Measureₓ α} (h : indep m₁ m₂ μ) :
  indep m₂ m₁ μ :=
  indep_sets.symm h

theorem indep_sets_of_indep_sets_of_le_left {α} {s₁ s₂ s₃ : Set (Set α)} [MeasurableSpace α] {μ : Measureₓ α}
  (h_indep : indep_sets s₁ s₂ μ) (h31 : s₃ ⊆ s₁) : indep_sets s₃ s₂ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (Set.mem_of_subset_of_mem h31 ht1) ht2

theorem indep_sets_of_indep_sets_of_le_right {α} {s₁ s₂ s₃ : Set (Set α)} [MeasurableSpace α] {μ : Measureₓ α}
  (h_indep : indep_sets s₁ s₂ μ) (h32 : s₃ ⊆ s₂) : indep_sets s₁ s₃ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (Set.mem_of_subset_of_mem h32 ht2)

theorem indep_of_indep_of_le_left {α} {m₁ m₂ m₃ : MeasurableSpace α} [MeasurableSpace α] {μ : Measureₓ α}
  (h_indep : indep m₁ m₂ μ) (h31 : m₃ ≤ m₁) : indep m₃ m₂ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (h31 _ ht1) ht2

theorem indep_of_indep_of_le_right {α} {m₁ m₂ m₃ : MeasurableSpace α} [MeasurableSpace α] {μ : Measureₓ α}
  (h_indep : indep m₁ m₂ μ) (h32 : m₃ ≤ m₂) : indep m₁ m₃ μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 ht1 (h32 _ ht2)

theorem indep_sets.union {α} [MeasurableSpace α] {s₁ s₂ s' : Set (Set α)} {μ : Measureₓ α} (h₁ : indep_sets s₁ s' μ)
  (h₂ : indep_sets s₂ s' μ) : indep_sets (s₁ ∪ s₂) s' μ :=
  by 
    intro t1 t2 ht1 ht2 
    cases' (Set.mem_union _ _ _).mp ht1 with ht1₁ ht1₂
    ·
      exact h₁ t1 t2 ht1₁ ht2
    ·
      exact h₂ t1 t2 ht1₂ ht2

@[simp]
theorem indep_sets.union_iff {α} [MeasurableSpace α] {s₁ s₂ s' : Set (Set α)} {μ : Measureₓ α} :
  indep_sets (s₁ ∪ s₂) s' μ ↔ indep_sets s₁ s' μ ∧ indep_sets s₂ s' μ :=
  ⟨fun h =>
      ⟨indep_sets_of_indep_sets_of_le_left h (Set.subset_union_left s₁ s₂),
        indep_sets_of_indep_sets_of_le_left h (Set.subset_union_right s₁ s₂)⟩,
    fun h => indep_sets.union h.left h.right⟩

theorem indep_sets.Union {α ι} [MeasurableSpace α] {s : ι → Set (Set α)} {s' : Set (Set α)} {μ : Measureₓ α}
  (hyp : ∀ n, indep_sets (s n) s' μ) : indep_sets (⋃n, s n) s' μ :=
  by 
    intro t1 t2 ht1 ht2 
    rw [Set.mem_Union] at ht1 
    cases' ht1 with n ht1 
    exact hyp n t1 t2 ht1 ht2

theorem indep_sets.inter {α} [MeasurableSpace α] {s₁ s' : Set (Set α)} (s₂ : Set (Set α)) {μ : Measureₓ α}
  (h₁ : indep_sets s₁ s' μ) : indep_sets (s₁ ∩ s₂) s' μ :=
  fun t1 t2 ht1 ht2 => h₁ t1 t2 ((Set.mem_inter_iff _ _ _).mp ht1).left ht2

theorem indep_sets.Inter {α ι} [MeasurableSpace α] {s : ι → Set (Set α)} {s' : Set (Set α)} {μ : Measureₓ α}
  (h : ∃ n, indep_sets (s n) s' μ) : indep_sets (⋂n, s n) s' μ :=
  by 
    intro t1 t2 ht1 ht2 
    cases' h with n h 
    exact h t1 t2 (set.mem_Inter.mp ht1 n) ht2

theorem indep_sets_singleton_iff {α} [MeasurableSpace α] {s t : Set α} {μ : Measureₓ α} :
  indep_sets {s} {t} μ ↔ μ (s ∩ t) = μ s*μ t :=
  ⟨fun h => h s t rfl rfl,
    fun h s1 t1 hs1 ht1 =>
      by 
        rwa [set.mem_singleton_iff.mp hs1, set.mem_singleton_iff.mp ht1]⟩

end Indep

/-! ### Deducing `indep` from `Indep` -/


section FromIndepToIndep

-- error in ProbabilityTheory.Independence: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem Indep_sets.indep_sets
{α ι}
{s : ι → set (set α)}
[measurable_space α]
{μ : measure α}
(h_indep : Indep_sets s μ)
{i j : ι}
(hij : «expr ≠ »(i, j)) : indep_sets (s i) (s j) μ :=
begin
  intros [ident t₁, ident t₂, ident ht₁, ident ht₂],
  have [ident hf_m] [":", expr ∀ x : ι, «expr ∈ »(x, {i, j}) → «expr ∈ »(ite «expr = »(x, i) t₁ t₂, s x)] [],
  { intros [ident x, ident hx],
    cases [expr finset.mem_insert.mp hx] ["with", ident hx, ident hx],
    { simp [] [] [] ["[", expr hx, ",", expr ht₁, "]"] [] [] },
    { simp [] [] [] ["[", expr finset.mem_singleton.mp hx, ",", expr hij.symm, ",", expr ht₂, "]"] [] [] } },
  have [ident h1] [":", expr «expr = »(t₁, ite «expr = »(i, i) t₁ t₂)] [],
  by simp [] [] ["only"] ["[", expr if_true, ",", expr eq_self_iff_true, "]"] [] [],
  have [ident h2] [":", expr «expr = »(t₂, ite «expr = »(j, i) t₁ t₂)] [],
  by simp [] [] ["only"] ["[", expr hij.symm, ",", expr if_false, "]"] [] [],
  have [ident h_inter] [":", expr «expr = »(«expr⋂ , »((t : ι)
     (H : «expr ∈ »(t, ({i, j} : finset ι))), ite «expr = »(t, i) t₁ t₂), «expr ∩ »(ite «expr = »(i, i) t₁ t₂, ite «expr = »(j, i) t₁ t₂))] [],
  by simp [] [] ["only"] ["[", expr finset.set_bInter_singleton, ",", expr finset.set_bInter_insert, "]"] [] [],
  have [ident h_prod] [":", expr «expr = »(«expr∏ in , »((t : ι), ({i, j} : finset ι), μ (ite «expr = »(t, i) t₁ t₂)), «expr * »(μ (ite «expr = »(i, i) t₁ t₂), μ (ite «expr = »(j, i) t₁ t₂)))] [],
  by simp [] [] ["only"] ["[", expr hij, ",", expr finset.prod_singleton, ",", expr finset.prod_insert, ",", expr not_false_iff, ",", expr finset.mem_singleton, "]"] [] [],
  rw [expr h1] [],
  nth_rewrite [1] [expr h2] [],
  nth_rewrite [3] [expr h2] [],
  rw ["[", "<-", expr h_inter, ",", "<-", expr h_prod, ",", expr h_indep {i, j} hf_m, "]"] []
end

theorem Indep.indep {α ι} {m : ι → MeasurableSpace α} [MeasurableSpace α] {μ : Measureₓ α} (h_indep : Indep m μ)
  {i j : ι} (hij : i ≠ j) : indep (m i) (m j) μ :=
  by 
    change indep_sets ((fun x => (m x).MeasurableSet') i) ((fun x => (m x).MeasurableSet') j) μ 
    exact Indep_sets.indep_sets h_indep hij

end FromIndepToIndep

/-!
## π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/


section FromMeasurableSpacesToSetsOfSets

/-! ### Independence of measurable space structures implies independence of generating π-systems -/


theorem Indep.Indep_sets {α ι} [MeasurableSpace α] {μ : Measureₓ α} {m : ι → MeasurableSpace α} {s : ι → Set (Set α)}
  (hms : ∀ n, m n = MeasurableSpace.generateFrom (s n)) (h_indep : Indep m μ) : Indep_sets s μ :=
  by 
    refine' fun S f hfs => h_indep S fun x hxS => _ 
    simpRw [hms x]
    exact measurable_set_generate_from (hfs x hxS)

theorem indep.indep_sets {α} [MeasurableSpace α] {μ : Measureₓ α} {s1 s2 : Set (Set α)}
  (h_indep : indep (generate_from s1) (generate_from s2) μ) : indep_sets s1 s2 μ :=
  fun t1 t2 ht1 ht2 => h_indep t1 t2 (measurable_set_generate_from ht1) (measurable_set_generate_from ht2)

end FromMeasurableSpacesToSetsOfSets

section FromPiSystemsToMeasurableSpaces

/-! ### Independence of generating π-systems implies independence of measurable space structures -/


-- error in ProbabilityTheory.Independence: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private
theorem indep_sets.indep_aux
{α}
{m2 : measurable_space α}
{m : measurable_space α}
{μ : measure α}
[is_probability_measure μ]
{p1 p2 : set (set α)}
(h2 : «expr ≤ »(m2, m))
(hp2 : is_pi_system p2)
(hpm2 : «expr = »(m2, generate_from p2))
(hyp : indep_sets p1 p2 μ)
{t1 t2 : set α}
(ht1 : «expr ∈ »(t1, p1))
(ht2m : m2.measurable_set' t2) : «expr = »(μ «expr ∩ »(t1, t2), «expr * »(μ t1, μ t2)) :=
begin
  let [ident μ_inter] [] [":=", expr μ.restrict t1],
  let [ident ν] [] [":=", expr «expr • »(μ t1, μ)],
  have [ident h_univ] [":", expr «expr = »(μ_inter set.univ, ν set.univ)] [],
  by rw ["[", expr measure.restrict_apply_univ, ",", expr measure.smul_apply, ",", expr measure_univ, ",", expr mul_one, "]"] [],
  haveI [] [":", expr is_finite_measure μ_inter] [":=", expr @restrict.is_finite_measure α _ t1 μ ⟨measure_lt_top μ t1⟩],
  rw ["[", expr set.inter_comm, ",", "<-", expr @measure.restrict_apply α _ μ t1 t2 (h2 t2 ht2m), "]"] [],
  refine [expr ext_on_measurable_space_of_generate_finite m p2 (λ t ht, _) h2 hpm2 hp2 h_univ ht2m],
  have [ident ht2] [":", expr m.measurable_set' t] [],
  { refine [expr h2 _ _],
    rw [expr hpm2] [],
    exact [expr measurable_set_generate_from ht] },
  rw ["[", expr measure.restrict_apply ht2, ",", expr measure.smul_apply, ",", expr set.inter_comm, "]"] [],
  exact [expr hyp t1 t ht1 ht]
end

-- error in ProbabilityTheory.Independence: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem indep_sets.indep
{α}
{m1 m2 : measurable_space α}
{m : measurable_space α}
{μ : measure α}
[is_probability_measure μ]
{p1 p2 : set (set α)}
(h1 : «expr ≤ »(m1, m))
(h2 : «expr ≤ »(m2, m))
(hp1 : is_pi_system p1)
(hp2 : is_pi_system p2)
(hpm1 : «expr = »(m1, generate_from p1))
(hpm2 : «expr = »(m2, generate_from p2))
(hyp : indep_sets p1 p2 μ) : indep m1 m2 μ :=
begin
  intros [ident t1, ident t2, ident ht1, ident ht2],
  let [ident μ_inter] [] [":=", expr μ.restrict t2],
  let [ident ν] [] [":=", expr «expr • »(μ t2, μ)],
  have [ident h_univ] [":", expr «expr = »(μ_inter set.univ, ν set.univ)] [],
  by rw ["[", expr measure.restrict_apply_univ, ",", expr measure.smul_apply, ",", expr measure_univ, ",", expr mul_one, "]"] [],
  haveI [] [":", expr is_finite_measure μ_inter] [":=", expr @restrict.is_finite_measure α _ t2 μ ⟨measure_lt_top μ t2⟩],
  rw ["[", expr mul_comm, ",", "<-", expr @measure.restrict_apply α _ μ t2 t1 (h1 t1 ht1), "]"] [],
  refine [expr ext_on_measurable_space_of_generate_finite m p1 (λ t ht, _) h1 hpm1 hp1 h_univ ht1],
  have [ident ht1] [":", expr m.measurable_set' t] [],
  { refine [expr h1 _ _],
    rw [expr hpm1] [],
    exact [expr measurable_set_generate_from ht] },
  rw ["[", expr measure.restrict_apply ht1, ",", expr measure.smul_apply, ",", expr mul_comm, "]"] [],
  exact [expr indep_sets.indep_aux h2 hp2 hpm2 hyp ht ht2]
end

end FromPiSystemsToMeasurableSpaces

section IndepSet

/-! ### Independence of measurable sets

We prove the following equivalences on `indep_set`, for measurable sets `s, t`.
* `indep_set s t μ ↔ μ (s ∩ t) = μ s * μ t`,
* `indep_set s t μ ↔ indep_sets {s} {t} μ`.
-/


variable {α : Type _} [MeasurableSpace α] {s t : Set α} (S T : Set (Set α))

theorem indep_set_iff_indep_sets_singleton (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac)
  [is_probability_measure μ] : indep_set s t μ ↔ indep_sets {s} {t} μ :=
  ⟨indep.indep_sets,
    fun h =>
      indep_sets.indep
        (generate_from_le
          fun u hu =>
            by 
              rwa [set.mem_singleton_iff.mp hu])
        (generate_from_le
          fun u hu =>
            by 
              rwa [set.mem_singleton_iff.mp hu])
        (IsPiSystem.singleton s) (IsPiSystem.singleton t) rfl rfl h⟩

theorem indep_set_iff_measure_inter_eq_mul (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac)
  [is_probability_measure μ] : indep_set s t μ ↔ μ (s ∩ t) = μ s*μ t :=
  (indep_set_iff_indep_sets_singleton hs_meas ht_meas μ).trans indep_sets_singleton_iff

theorem indep_sets.indep_set_of_mem (hs : s ∈ S) (ht : t ∈ T) (hs_meas : MeasurableSet s) (ht_meas : MeasurableSet t)
  (μ : Measureₓ α :=  by 
    runTac 
      volume_tac)
  [is_probability_measure μ] (h_indep : indep_sets S T μ) : indep_set s t μ :=
  (indep_set_iff_measure_inter_eq_mul hs_meas ht_meas μ).mpr (h_indep s t hs ht)

end IndepSet

end ProbabilityTheory

