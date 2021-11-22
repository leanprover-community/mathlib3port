import Mathbin.Order.Filter.Basic 
import Mathbin.Data.Set.Countable

/-!
# Filters with countable intersection property

In this file we define `countable_Inter_filter` to be the class of filters with the following
property: for any countable collection of sets `s ∈ l` their intersection belongs to `l` as well.

Two main examples are the `residual` filter defined in `topology.metric_space.baire` and
the `measure.ae` filter defined in `measure_theory.measure_space`.
-/


open Set Filter

open_locale Filter

variable{ι α : Type _}

/-- A filter `l` has the countable intersection property if for any countable collection
of sets `s ∈ l` their intersection belongs to `l` as well. -/
class CountableInterFilter(l : Filter α) : Prop where 
  countable_sInter_mem_sets' : ∀ {S : Set (Set α)} hSc : countable S hS : ∀ s _ : s ∈ S, s ∈ l, ⋂₀S ∈ l

variable{l : Filter α}[CountableInterFilter l]

theorem countable_sInter_mem_sets {S : Set (Set α)} (hSc : countable S) : ⋂₀S ∈ l ↔ ∀ s _ : s ∈ S, s ∈ l :=
  ⟨fun hS s hs => mem_of_superset hS (sInter_subset_of_mem hs), CountableInterFilter.countable_sInter_mem_sets' hSc⟩

theorem countable_Inter_mem_sets [Encodable ι] {s : ι → Set α} : (⋂i, s i) ∈ l ↔ ∀ i, s i ∈ l :=
  sInter_range s ▸ (countable_sInter_mem_sets (countable_range _)).trans forall_range_iff

theorem countable_bInter_mem {S : Set ι} (hS : countable S) {s : ∀ i _ : i ∈ S, Set α} :
  (⋂(i : _)(_ : i ∈ S), s i ‹_›) ∈ l ↔ ∀ i _ : i ∈ S, s i ‹_› ∈ l :=
  by 
    rw [bInter_eq_Inter]
    haveI  := hS.to_encodable 
    exact countable_Inter_mem_sets.trans Subtype.forall

theorem eventually_countable_forall [Encodable ι] {p : α → ι → Prop} : (∀ᶠx in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠx in l, p x i :=
  by 
    simpa only [Filter.Eventually, set_of_forall] using @countable_Inter_mem_sets _ _ l _ _ fun i => { x | p x i }

theorem eventually_countable_ball {S : Set ι} (hS : countable S) {p : ∀ x : α i _ : i ∈ S, Prop} :
  (∀ᶠx in l, ∀ i _ : i ∈ S, p x i ‹_›) ↔ ∀ i _ : i ∈ S, ∀ᶠx in l, p x i ‹_› :=
  by 
    simpa only [Filter.Eventually, set_of_forall] using @countable_bInter_mem _ _ l _ _ hS fun i hi => { x | p x i hi }

theorem EventuallyLe.countable_Union [Encodable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
  (⋃i, s i) ≤ᶠ[l] ⋃i, t i :=
  (eventually_countable_forall.2 h).mono$ fun x hst hs => mem_Union.2$ (mem_Union.1 hs).imp hst

theorem EventuallyEq.countable_Union [Encodable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
  (⋃i, s i) =ᶠ[l] ⋃i, t i :=
  (EventuallyLe.countable_Union fun i => (h i).le).antisymm (EventuallyLe.countable_Union fun i => (h i).symm.le)

theorem EventuallyLe.countable_bUnion {S : Set ι} (hS : countable S) {s t : ∀ i _ : i ∈ S, Set α}
  (h : ∀ i _ : i ∈ S, s i ‹_› ≤ᶠ[l] t i ‹_›) : (⋃(i : _)(_ : i ∈ S), s i ‹_›) ≤ᶠ[l] ⋃(i : _)(_ : i ∈ S), t i ‹_› :=
  by 
    simp only [bUnion_eq_Union]
    haveI  := hS.to_encodable 
    exact EventuallyLe.countable_Union fun i => h i i.2

theorem EventuallyEq.countable_bUnion {S : Set ι} (hS : countable S) {s t : ∀ i _ : i ∈ S, Set α}
  (h : ∀ i _ : i ∈ S, s i ‹_› =ᶠ[l] t i ‹_›) : (⋃(i : _)(_ : i ∈ S), s i ‹_›) =ᶠ[l] ⋃(i : _)(_ : i ∈ S), t i ‹_› :=
  (EventuallyLe.countable_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLe.countable_bUnion hS fun i hi => (h i hi).symm.le)

theorem EventuallyLe.countable_Inter [Encodable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
  (⋂i, s i) ≤ᶠ[l] ⋂i, t i :=
  (eventually_countable_forall.2 h).mono$ fun x hst hs => mem_Inter.2$ fun i => hst _ (mem_Inter.1 hs i)

theorem EventuallyEq.countable_Inter [Encodable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
  (⋂i, s i) =ᶠ[l] ⋂i, t i :=
  (EventuallyLe.countable_Inter fun i => (h i).le).antisymm (EventuallyLe.countable_Inter fun i => (h i).symm.le)

theorem EventuallyLe.countable_bInter {S : Set ι} (hS : countable S) {s t : ∀ i _ : i ∈ S, Set α}
  (h : ∀ i _ : i ∈ S, s i ‹_› ≤ᶠ[l] t i ‹_›) : (⋂(i : _)(_ : i ∈ S), s i ‹_›) ≤ᶠ[l] ⋂(i : _)(_ : i ∈ S), t i ‹_› :=
  by 
    simp only [bInter_eq_Inter]
    haveI  := hS.to_encodable 
    exact EventuallyLe.countable_Inter fun i => h i i.2

theorem EventuallyEq.countable_bInter {S : Set ι} (hS : countable S) {s t : ∀ i _ : i ∈ S, Set α}
  (h : ∀ i _ : i ∈ S, s i ‹_› =ᶠ[l] t i ‹_›) : (⋂(i : _)(_ : i ∈ S), s i ‹_›) =ᶠ[l] ⋂(i : _)(_ : i ∈ S), t i ‹_› :=
  (EventuallyLe.countable_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLe.countable_bInter hS fun i hi => (h i hi).symm.le)

instance countable_Inter_filter_principal (s : Set α) : CountableInterFilter (𝓟 s) :=
  ⟨fun S hSc hS => subset_sInter hS⟩

instance countable_Inter_filter_bot : CountableInterFilter (⊥ : Filter α) :=
  by 
    rw [←principal_empty]
    apply countable_Inter_filter_principal

instance countable_Inter_filter_top : CountableInterFilter (⊤ : Filter α) :=
  by 
    rw [←principal_univ]
    apply countable_Inter_filter_principal

/-- Infimum of two `countable_Inter_filter`s is a `countable_Inter_filter`. This is useful, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`. -/
instance countable_Inter_filter_inf (l₁ l₂ : Filter α) [CountableInterFilter l₁] [CountableInterFilter l₂] :
  CountableInterFilter (l₁⊓l₂) :=
  by 
    refine' ⟨fun S hSc hS => _⟩
    choose s hs t ht hst using hS 
    replace hs : (⋂(i : _)(_ : i ∈ S), s i ‹_›) ∈ l₁ := (countable_bInter_mem hSc).2 hs 
    replace ht : (⋂(i : _)(_ : i ∈ S), t i ‹_›) ∈ l₂ := (countable_bInter_mem hSc).2 ht 
    refine' mem_of_superset (inter_mem_inf hs ht) (subset_sInter$ fun i hi => _)
    rw [hst i hi]
    apply inter_subset_inter <;> exact Inter_subset_of_subset i (Inter_subset _ _)

-- error in Order.Filter.CountableInter: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- Supremum of two `countable_Inter_filter`s is a `countable_Inter_filter`. -/
instance countable_Inter_filter_sup
(l₁ l₂ : filter α)
[countable_Inter_filter l₁]
[countable_Inter_filter l₂] : countable_Inter_filter «expr ⊔ »(l₁, l₂) :=
begin
  refine [expr ⟨λ S hSc hS, ⟨_, _⟩⟩]; refine [expr (countable_sInter_mem_sets hSc).2 (λ s hs, _)],
  exacts ["[", expr (hS s hs).1, ",", expr (hS s hs).2, "]"]
end

