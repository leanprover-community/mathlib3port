/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.Set.Countable
import Mathbin.Logic.Encodable.Lattice
import Mathbin.Order.ConditionallyCompleteLattice
import Mathbin.Order.Disjointed
import Mathbin.Order.SymmDiff

/-!
# Measurable spaces and measurable functions

This file defines measurable spaces and measurable functions.

A measurable space is a set equipped with a σ-algebra, a collection of
subsets closed under complementation and countable union. A function
between measurable spaces is measurable if the preimage of each
measurable subset is measurable.

σ-algebras on a fixed set `α` form a complete lattice. Here we order
σ-algebras by writing `m₁ ≤ m₂` if every set which is `m₁`-measurable is
also `m₂`-measurable (that is, `m₁` is a subset of `m₂`). In particular, any
collection of subsets of `α` generates a smallest σ-algebra which
contains all of them.

Do not add measurability lemmas (which could be tagged with
@[measurability]) to this file, since the measurability tactic is downstream
from here. Use `measure_theory.measurable_space` instead.

## References

* <https://en.wikipedia.org/wiki/Measurable_space>
* <https://en.wikipedia.org/wiki/Sigma-algebra>
* <https://en.wikipedia.org/wiki/Dynkin_system>

## Tags

measurable space, σ-algebra, measurable function
-/


open Set Encodable Function Equiv

open Classical

variable {α β γ δ δ' : Type _} {ι : Sort _} {s t u : Set α}

/-- A measurable space is a space equipped with a σ-algebra. -/
structure MeasurableSpace (α : Type _) where
  MeasurableSet' : Set α → Prop
  measurableSetEmpty : measurable_set' ∅
  measurableSetCompl : ∀ s, measurable_set' s → measurable_set' (sᶜ)
  measurableSetUnion : ∀ f : ℕ → Set α, (∀ i, measurable_set' (f i)) → measurable_set' (⋃ i, f i)

attribute [class] MeasurableSpace

instance [h : MeasurableSpace α] : MeasurableSpace αᵒᵈ :=
  h

section

/-- `measurable_set s` means that `s` is measurable (in the ambient measure space on `α`) -/
def MeasurableSet [MeasurableSpace α] : Set α → Prop :=
  ‹MeasurableSpace α›.MeasurableSet'

-- mathport name: measurable_set_of
localized [MeasureTheory] notation "measurable_set[" m "]" => @MeasurableSet hole! m

@[simp]
theorem MeasurableSet.empty [MeasurableSpace α] : MeasurableSet (∅ : Set α) :=
  ‹MeasurableSpace α›.measurableSetEmpty

variable {m : MeasurableSpace α}

include m

theorem MeasurableSet.compl : MeasurableSet s → MeasurableSet (sᶜ) :=
  ‹MeasurableSpace α›.measurableSetCompl s

theorem MeasurableSet.ofCompl (h : MeasurableSet (sᶜ)) : MeasurableSet s :=
  compl_compl s ▸ h.compl

@[simp]
theorem MeasurableSet.compl_iff : MeasurableSet (sᶜ) ↔ MeasurableSet s :=
  ⟨MeasurableSet.ofCompl, MeasurableSet.compl⟩

@[simp]
theorem MeasurableSet.univ : MeasurableSet (Univ : Set α) := by simpa using (@MeasurableSet.empty α _).compl

@[nontriviality]
theorem Subsingleton.measurableSet [Subsingleton α] {s : Set α} : MeasurableSet s :=
  Subsingleton.set_cases MeasurableSet.empty MeasurableSet.univ s

theorem MeasurableSet.congr {s t : Set α} (hs : MeasurableSet s) (h : s = t) : MeasurableSet t := by rwa [← h]

theorem MeasurableSet.bUnionDecode₂ [Encodable β] ⦃f : β → Set α⦄ (h : ∀ b, MeasurableSet (f b)) (n : ℕ) :
    MeasurableSet (⋃ b ∈ decode₂ β n, f b) :=
  Encodable.Union_decode₂_cases MeasurableSet.empty h

theorem MeasurableSet.union [Countable ι] ⦃f : ι → Set α⦄ (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  by
  cases nonempty_encodable (PLift ι)
  rw [← Union_plift_down, ← Encodable.Union_decode₂]
  exact ‹MeasurableSpace α›.measurableSetUnion _ (MeasurableSet.bUnionDecode₂ fun _ => h _)

theorem MeasurableSet.bUnion {f : β → Set α} {s : Set β} (hs : s.Countable) (h : ∀ b ∈ s, MeasurableSet (f b)) :
    MeasurableSet (⋃ b ∈ s, f b) := by
  rw [bUnion_eq_Union]
  haveI := hs.to_encodable
  exact MeasurableSet.union (by simpa using h)

theorem Set.Finite.measurableSetBUnion {f : β → Set α} {s : Set β} (hs : s.Finite) (h : ∀ b ∈ s, MeasurableSet (f b)) :
    MeasurableSet (⋃ b ∈ s, f b) :=
  MeasurableSet.bUnion hs.Countable h

theorem Finset.measurableSetBUnion {f : β → Set α} (s : Finset β) (h : ∀ b ∈ s, MeasurableSet (f b)) :
    MeasurableSet (⋃ b ∈ s, f b) :=
  s.finite_to_set.measurableSetBUnion h

theorem MeasurableSet.sUnion {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, MeasurableSet t) :
    MeasurableSet (⋃₀s) := by
  rw [sUnion_eq_bUnion]
  exact MeasurableSet.bUnion hs h

theorem Set.Finite.measurableSetSUnion {s : Set (Set α)} (hs : s.Finite) (h : ∀ t ∈ s, MeasurableSet t) :
    MeasurableSet (⋃₀s) :=
  MeasurableSet.sUnion hs.Countable h

theorem MeasurableSet.inter [Countable ι] {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.compl_iff.1 <| by
    rw [compl_Inter]
    exact MeasurableSet.union fun b => (h b).compl

theorem MeasurableSet.bInter {f : β → Set α} {s : Set β} (hs : s.Countable) (h : ∀ b ∈ s, MeasurableSet (f b)) :
    MeasurableSet (⋂ b ∈ s, f b) :=
  MeasurableSet.compl_iff.1 <| by
    rw [compl_Inter₂]
    exact MeasurableSet.bUnion hs fun b hb => (h b hb).compl

theorem Set.Finite.measurableSetBInter {f : β → Set α} {s : Set β} (hs : s.Finite) (h : ∀ b ∈ s, MeasurableSet (f b)) :
    MeasurableSet (⋂ b ∈ s, f b) :=
  MeasurableSet.bInter hs.Countable h

theorem Finset.measurableSetBInter {f : β → Set α} (s : Finset β) (h : ∀ b ∈ s, MeasurableSet (f b)) :
    MeasurableSet (⋂ b ∈ s, f b) :=
  s.finite_to_set.measurableSetBInter h

theorem MeasurableSet.sInter {s : Set (Set α)} (hs : s.Countable) (h : ∀ t ∈ s, MeasurableSet t) :
    MeasurableSet (⋂₀ s) := by
  rw [sInter_eq_bInter]
  exact MeasurableSet.bInter hs h

theorem Set.Finite.measurableSetSInter {s : Set (Set α)} (hs : s.Finite) (h : ∀ t ∈ s, MeasurableSet t) :
    MeasurableSet (⋂₀ s) :=
  MeasurableSet.sInter hs.Countable h

/- warning: measurable_set.union clashes with measurable_set.Union -> MeasurableSet.union
warning: measurable_set.union -> MeasurableSet.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {m : MeasurableSpace.{u_1} α} {s₁ : Set.{u_1} α} {s₂ : Set.{u_1} α}, (MeasurableSet.{u_1} α m s₁) -> (MeasurableSet.{u_1} α m s₂) -> (MeasurableSet.{u_1} α m (Union.union.{u_1} (Set.{u_1} α) (Set.hasUnion.{u_1} α) s₁ s₂))
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align measurable_set.union MeasurableSet.unionₓ'. -/
@[simp]
theorem MeasurableSet.union {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∪ s₂) :=
  by
  rw [union_eq_Union]
  exact MeasurableSet.union (Bool.forall_bool.2 ⟨h₂, h₁⟩)

/- warning: measurable_set.inter clashes with measurable_set.Inter -> MeasurableSet.inter
warning: measurable_set.inter -> MeasurableSet.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {m : MeasurableSpace.{u_1} α} {s₁ : Set.{u_1} α} {s₂ : Set.{u_1} α}, (MeasurableSet.{u_1} α m s₁) -> (MeasurableSet.{u_1} α m s₂) -> (MeasurableSet.{u_1} α m (Inter.inter.{u_1} (Set.{u_1} α) (Set.hasInter.{u_1} α) s₁ s₂))
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align measurable_set.inter MeasurableSet.interₓ'. -/
@[simp]
theorem MeasurableSet.inter {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∩ s₂) :=
  by
  rw [inter_eq_compl_compl_union_compl]
  exact (h₁.compl.union h₂.compl).compl

@[simp]
theorem MeasurableSet.diff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) : MeasurableSet (s₁ \ s₂) :=
  h₁.inter h₂.compl

@[simp]
theorem MeasurableSet.symmDiff {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (s₁ ∆ s₂) :=
  (h₁.diff h₂).union (h₂.diff h₁)

@[simp]
theorem MeasurableSet.ite {t s₁ s₂ : Set α} (ht : MeasurableSet t) (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) :
    MeasurableSet (t.ite s₁ s₂) :=
  (h₁.inter ht).union (h₂.diff ht)

theorem MeasurableSet.ite' {s t : Set α} {p : Prop} (hs : p → MeasurableSet s) (ht : ¬p → MeasurableSet t) :
    MeasurableSet (ite p s t) := by
  split_ifs
  exacts[hs h, ht h]

@[simp]
theorem MeasurableSet.cond {s₁ s₂ : Set α} (h₁ : MeasurableSet s₁) (h₂ : MeasurableSet s₂) {i : Bool} :
    MeasurableSet (cond i s₁ s₂) := by
  cases i
  exacts[h₂, h₁]

@[simp]
theorem MeasurableSet.disjointed {f : ℕ → Set α} (h : ∀ i, MeasurableSet (f i)) (n) : MeasurableSet (disjointed f n) :=
  disjointedRec (fun t i ht => MeasurableSet.diff ht <| h _) (h n)

@[simp]
theorem MeasurableSet.const (p : Prop) : MeasurableSet { a : α | p } := by
  by_cases p <;> simp [h, MeasurableSet.empty] <;> apply MeasurableSet.univ

/-- Every set has a measurable superset. Declare this as local instance as needed. -/
theorem nonempty_measurable_superset (s : Set α) : Nonempty { t // s ⊆ t ∧ MeasurableSet t } :=
  ⟨⟨Univ, subset_univ s, MeasurableSet.univ⟩⟩

end

open MeasureTheory

@[ext]
theorem MeasurableSpace.ext :
    ∀ {m₁ m₂ : MeasurableSpace α}, (∀ s : Set α, measurable_set[m₁] s ↔ measurable_set[m₂] s) → m₁ = m₂
  | ⟨s₁, _, _, _⟩, ⟨s₂, _, _, _⟩, h => by
    have : s₁ = s₂ := funext fun x => propext <| h x
    subst this

@[ext]
theorem MeasurableSpace.ext_iff {m₁ m₂ : MeasurableSpace α} :
    m₁ = m₂ ↔ ∀ s : Set α, measurable_set[m₁] s ↔ measurable_set[m₂] s :=
  ⟨by
    rintro rfl
    intro s
    rfl, MeasurableSpace.ext⟩

/-- A typeclass mixin for `measurable_space`s such that each singleton is measurable. -/
class MeasurableSingletonClass (α : Type _) [MeasurableSpace α] : Prop where
  measurableSetSingleton : ∀ x, MeasurableSet ({x} : Set α)

export MeasurableSingletonClass (measurableSetSingleton)

attribute [simp] measurable_set_singleton

section MeasurableSingletonClass

variable [MeasurableSpace α] [MeasurableSingletonClass α]

theorem measurableSetEq {a : α} : MeasurableSet { x | x = a } :=
  measurableSetSingleton a

theorem MeasurableSet.insert {s : Set α} (hs : MeasurableSet s) (a : α) : MeasurableSet (insert a s) :=
  (measurableSetSingleton a).union hs

@[simp]
theorem measurable_set_insert {a : α} {s : Set α} : MeasurableSet (insert a s) ↔ MeasurableSet s :=
  ⟨fun h =>
    if ha : a ∈ s then by rwa [← insert_eq_of_mem ha]
    else insert_diff_self_of_not_mem ha ▸ h.diff (measurableSetSingleton _),
    fun h => h.insert a⟩

theorem Set.Subsingleton.measurableSet {s : Set α} (hs : s.Subsingleton) : MeasurableSet s :=
  hs.induction_on MeasurableSet.empty measurableSetSingleton

theorem Set.Finite.measurableSet {s : Set α} (hs : s.Finite) : MeasurableSet s :=
  (Finite.induction_on hs MeasurableSet.empty) fun a s ha hsf hsm => hsm.insert _

protected theorem Finset.measurableSet (s : Finset α) : MeasurableSet (↑s : Set α) :=
  s.finite_to_set.MeasurableSet

theorem Set.Countable.measurableSet {s : Set α} (hs : s.Countable) : MeasurableSet s := by
  rw [← bUnion_of_singleton s]
  exact MeasurableSet.bUnion hs fun b hb => measurable_set_singleton b

end MeasurableSingletonClass

namespace MeasurableSpace

section CompleteLattice

instance : LE (MeasurableSpace α) where le m₁ m₂ := ∀ s, measurable_set[m₁] s → measurable_set[m₂] s

theorem le_def {α} {a b : MeasurableSpace α} : a ≤ b ↔ a.MeasurableSet' ≤ b.MeasurableSet' :=
  Iff.rfl

instance : PartialOrder (MeasurableSpace α) :=
  { MeasurableSpace.hasLe, PartialOrder.lift (@MeasurableSet α) fun m₁ m₂ h => ext fun s => h ▸ Iff.rfl with
    lt := fun m₁ m₂ => m₁ ≤ m₂ ∧ ¬m₂ ≤ m₁ }

/-- The smallest σ-algebra containing a collection `s` of basic sets -/
inductive GenerateMeasurable (s : Set (Set α)) : Set α → Prop
  | basic : ∀ u ∈ s, generate_measurable u
  | Empty : generate_measurable ∅
  | compl : ∀ s, generate_measurable s → generate_measurable (sᶜ)
  | union : ∀ f : ℕ → Set α, (∀ n, generate_measurable (f n)) → generate_measurable (⋃ i, f i)

/-- Construct the smallest measure space containing a collection of basic sets -/
def generateFrom (s : Set (Set α)) : MeasurableSpace α where
  MeasurableSet' := GenerateMeasurable s
  measurableSetEmpty := GenerateMeasurable.empty
  measurableSetCompl := GenerateMeasurable.compl
  measurableSetUnion := GenerateMeasurable.union

theorem measurableSetGenerateFrom {s : Set (Set α)} {t : Set α} (ht : t ∈ s) : @MeasurableSet _ (generateFrom s) t :=
  GenerateMeasurable.basic t ht

@[elab_as_elim]
theorem generateFromInduction (p : Set α → Prop) (C : Set (Set α)) (hC : ∀ t ∈ C, p t) (h_empty : p ∅)
    (h_compl : ∀ t, p t → p (tᶜ)) (h_Union : ∀ f : ℕ → Set α, (∀ n, p (f n)) → p (⋃ i, f i)) {s : Set α}
    (hs : measurable_set[generateFrom C] s) : p s := by
  induction hs
  exacts[hC _ hs_H, h_empty, h_compl _ hs_ih, h_Union hs_f hs_ih]

theorem generate_from_le {s : Set (Set α)} {m : MeasurableSpace α} (h : ∀ t ∈ s, measurable_set[m] t) :
    generateFrom s ≤ m := fun t (ht : GenerateMeasurable s t) =>
  ht.recOn h (measurableSetEmpty m) (fun s _ hs => measurableSetCompl m s hs) fun f _ hf => measurableSetUnion m f hf

theorem generate_from_le_iff {s : Set (Set α)} (m : MeasurableSpace α) :
    generateFrom s ≤ m ↔ s ⊆ { t | measurable_set[m] t } :=
  Iff.intro (fun h u hu => h _ <| measurableSetGenerateFrom hu) fun h => generate_from_le h

@[simp]
theorem generate_from_measurable_set [MeasurableSpace α] : generateFrom { s : Set α | MeasurableSet s } = ‹_› :=
  (le_antisymm (generate_from_le fun _ => id)) fun s => measurableSetGenerateFrom

/-- If `g` is a collection of subsets of `α` such that the `σ`-algebra generated from `g` contains
the same sets as `g`, then `g` was already a `σ`-algebra. -/
protected def mkOfClosure (g : Set (Set α)) (hg : { t | measurable_set[generateFrom g] t } = g) :
    MeasurableSpace α where
  MeasurableSet' s := s ∈ g
  measurableSetEmpty := hg ▸ measurableSetEmpty _
  measurableSetCompl := hg ▸ measurableSetCompl _
  measurableSetUnion := hg ▸ measurableSetUnion _

theorem mk_of_closure_sets {s : Set (Set α)} {hs : { t | measurable_set[generateFrom s] t } = s} :
    MeasurableSpace.mkOfClosure s hs = generateFrom s :=
  MeasurableSpace.ext fun t =>
    show t ∈ s ↔ _ by
      conv_lhs => rw [← hs]
      rfl

/-- We get a Galois insertion between `σ`-algebras on `α` and `set (set α)` by using `generate_from`
  on one side and the collection of measurable sets on the other side. -/
def giGenerateFrom : GaloisInsertion (@generateFrom α) fun m => { t | @MeasurableSet α m t } where
  gc s := generate_from_le_iff
  le_l_u m s := measurableSetGenerateFrom
  choice g hg := MeasurableSpace.mkOfClosure g <| le_antisymm hg <| (generate_from_le_iff _).1 le_rfl
  choice_eq g hg := mk_of_closure_sets

instance : CompleteLattice (MeasurableSpace α) :=
  giGenerateFrom.liftCompleteLattice

instance : Inhabited (MeasurableSpace α) :=
  ⟨⊤⟩

@[mono]
theorem generate_from_mono {s t : Set (Set α)} (h : s ⊆ t) : generateFrom s ≤ generateFrom t :=
  giGenerateFrom.gc.monotone_l h

theorem generate_from_sup_generate_from {s t : Set (Set α)} : generateFrom s ⊔ generateFrom t = generateFrom (s ∪ t) :=
  (@giGenerateFrom α).gc.l_sup.symm

@[simp]
theorem generate_from_insert_univ (S : Set (Set α)) : generateFrom (insert Set.Univ S) = generateFrom S := by
  refine' le_antisymm _ (generate_from_mono (Set.subset_insert _ _))
  rw [generate_from_le_iff]
  intro t ht
  cases ht
  · rw [ht]
    exact MeasurableSet.univ
    
  · exact measurable_set_generate_from ht
    

@[simp]
theorem generate_from_insert_empty (S : Set (Set α)) : generateFrom (insert ∅ S) = generateFrom S := by
  refine' le_antisymm _ (generate_from_mono (Set.subset_insert _ _))
  rw [generate_from_le_iff]
  intro t ht
  cases ht
  · rw [ht]
    exact @MeasurableSet.empty _ (generate_from S)
    
  · exact measurable_set_generate_from ht
    

@[simp]
theorem generate_from_singleton_empty : generateFrom {∅} = (⊥ : MeasurableSpace α) := by
  rw [eq_bot_iff, generate_from_le_iff]
  simp

@[simp]
theorem generate_from_singleton_univ : generateFrom {Set.Univ} = (⊥ : MeasurableSpace α) := by
  rw [eq_bot_iff, generate_from_le_iff]
  simp

theorem measurable_set_bot_iff {s : Set α} : @MeasurableSet α ⊥ s ↔ s = ∅ ∨ s = univ :=
  let b : MeasurableSpace α :=
    { MeasurableSet' := fun s => s = ∅ ∨ s = univ, measurableSetEmpty := Or.inl rfl,
      measurableSetCompl := by simp (config := { contextual := true }) [or_imp],
      measurableSetUnion := fun f hf =>
        Classical.by_cases
          (fun h : ∃ i, f i = univ =>
            let ⟨i, hi⟩ := h
            Or.inr <| eq_univ_of_univ_subset <| hi ▸ le_supr f i)
          fun h : ¬∃ i, f i = univ =>
          Or.inl <|
            eq_empty_of_subset_empty <|
              Union_subset fun i =>
                (hf i).elim (by simp (config := { contextual := true })) fun hi => False.elim <| h ⟨i, hi⟩ }
  have : b = ⊥ :=
    bot_unique fun s hs => hs.elim (fun s => s.symm ▸ @measurableSetEmpty _ ⊥) fun s => s.symm ▸ @MeasurableSet.univ _ ⊥
  this ▸ Iff.rfl

@[simp]
theorem measurableSetTop {s : Set α} : @MeasurableSet _ ⊤ s :=
  trivial

@[simp]
theorem measurable_set_inf {m₁ m₂ : MeasurableSpace α} {s : Set α} :
    @MeasurableSet _ (m₁ ⊓ m₂) s ↔ @MeasurableSet _ m₁ s ∧ @MeasurableSet _ m₂ s :=
  Iff.rfl

@[simp]
theorem measurable_set_Inf {ms : Set (MeasurableSpace α)} {s : Set α} :
    @MeasurableSet _ (inf ms) s ↔ ∀ m ∈ ms, @MeasurableSet _ m s :=
  show s ∈ ⋂₀ _ ↔ _ by simp

@[simp]
theorem measurable_set_infi {ι} {m : ι → MeasurableSpace α} {s : Set α} :
    @MeasurableSet _ (infi m) s ↔ ∀ i, @MeasurableSet _ (m i) s := by rw [infi, measurable_set_Inf, forall_range_iff]

theorem measurable_set_sup {m₁ m₂ : MeasurableSpace α} {s : Set α} :
    measurable_set[m₁ ⊔ m₂] s ↔ GenerateMeasurable (measurable_set[m₁] ∪ measurable_set[m₂]) s :=
  Iff.refl _

theorem measurable_set_Sup {ms : Set (MeasurableSpace α)} {s : Set α} :
    measurable_set[sup ms] s ↔ GenerateMeasurable { s : Set α | ∃ m ∈ ms, measurable_set[m] s } s := by
  change @measurable_set' _ (generate_from <| ⋃₀_) _ ↔ _
  simp [generate_from, ← set_of_exists]

theorem measurable_set_supr {ι} {m : ι → MeasurableSpace α} {s : Set α} :
    @MeasurableSet _ (supr m) s ↔ GenerateMeasurable { s : Set α | ∃ i, measurable_set[m i] s } s := by
  simp only [supr, measurable_set_Sup, exists_range_iff]

theorem measurable_space_supr_eq (m : ι → MeasurableSpace α) :
    (⨆ n, m n) = generateFrom { s | ∃ n, measurable_set[m n] s } := by
  ext s
  rw [measurable_set_supr]
  rfl

theorem generate_from_Union_measurable_set (m : ι → MeasurableSpace α) :
    generateFrom (⋃ n, { t | measurable_set[m n] t }) = ⨆ n, m n :=
  (@giGenerateFrom α).l_supr_u m

end CompleteLattice

end MeasurableSpace

section MeasurableFunctions

open MeasurableSpace

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
def Measurable [MeasurableSpace α] [MeasurableSpace β] (f : α → β) : Prop :=
  ∀ ⦃t : Set β⦄, MeasurableSet t → MeasurableSet (f ⁻¹' t)

-- mathport name: measurable_of
localized [MeasureTheory] notation "measurable[" m "]" => @Measurable hole! hole! m hole!

theorem measurableId {ma : MeasurableSpace α} : Measurable (@id α) := fun t => id

theorem measurableId' {ma : MeasurableSpace α} : Measurable fun a : α => a :=
  measurableId

theorem Measurable.comp {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} {g : β → γ}
    {f : α → β} (hg : Measurable g) (hf : Measurable f) : Measurable (g ∘ f) := fun t ht => hf (hg ht)

@[simp]
theorem measurableConst {ma : MeasurableSpace α} {mb : MeasurableSpace β} {a : α} : Measurable fun b : β => a :=
  fun s hs => MeasurableSet.const (a ∈ s)

theorem Measurable.le {α} {m m0 : MeasurableSpace α} {mb : MeasurableSpace β} (hm : m ≤ m0) {f : α → β}
    (hf : measurable[m] f) : measurable[m0] f := fun s hs => hm _ (hf hs)

end MeasurableFunctions

