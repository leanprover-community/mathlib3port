/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Data.Set.Finite
import Mathbin.Data.Countable.Basic
import Mathbin.Logic.Equiv.List

/-!
# Countable sets
-/


noncomputable section

open Function Set Encodable

open Classical hiding some

open Classical

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

namespace Set

/-- A set is countable if there exists an encoding of the set into the natural numbers.
An encoding is an injection with a partial inverse, which can be viewed as a
constructive analogue of countability. (For the most part, theorems about
`countable` will be classical and `encodable` will be constructive.)
-/
protected def Countable (s : Set α) : Prop :=
  Nonempty (Encodable s)

@[simp]
theorem countable_coe_iff {s : Set α} : Countable s ↔ s.Countable :=
  nonempty_encodable.symm

/-- Prove `set.countable` from a `countable` instance on the subtype. -/
theorem to_countable (s : Set α) [Countable s] : s.Countable :=
  countable_coe_iff.mp ‹_›

/-- Restate `set.countable` as a `countable` instance. -/
alias countable_coe_iff ↔ _root_.countable.to_set countable.to_subtype

protected theorem countable_iff_exists_injective {s : Set α} : s.Countable ↔ ∃ f : s → ℕ, Injective f :=
  countable_coe_iff.symm.trans (countable_iff_exists_injective s)

/-- A set `s : set α` is countable if and only if there exists a function `α → ℕ` injective
on `s`. -/
theorem countable_iff_exists_inj_on {s : Set α} : s.Countable ↔ ∃ f : α → ℕ, InjOn f s :=
  Set.countable_iff_exists_injective.trans exists_inj_on_iff_injective.symm

/-- Convert `set.countable s` to `encodable s` (noncomputable). -/
protected def Countable.toEncodable {s : Set α} : s.Countable → Encodable s :=
  Classical.choice

section Enumerate

/-- Noncomputably enumerate elements in a set. The `default` value is used to extend the domain to
all of `ℕ`. -/
def enumerateCountable {s : Set α} (h : s.Countable) (default : α) : ℕ → α := fun n =>
  match @Encodable.decode s h.toEncodable n with
  | some y => y
  | none => default

theorem subset_range_enumerate {s : Set α} (h : s.Countable) (default : α) : s ⊆ Range (enumerateCountable h default) :=
  fun x hx =>
  ⟨@Encodable.encode s h.toEncodable ⟨x, hx⟩, by
    simp [← enumerate_countable, ← Encodable.encodek]⟩

end Enumerate

theorem Countable.mono {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) : s₂.Countable → s₁.Countable
  | ⟨H⟩ => ⟨@ofInj _ _ H _ (embeddingOfSubset _ _ h).2⟩

theorem countable_range [Countable ι] (f : ι → β) : (Range f).Countable :=
  surjective_onto_range.Countable.to_set

theorem countable_iff_exists_subset_range [Nonempty α] {s : Set α} : s.Countable ↔ ∃ f : ℕ → α, s ⊆ Range f :=
  ⟨fun h => by
    inhabit α
    exact ⟨enumerate_countable h default, subset_range_enumerate _ _⟩, fun ⟨f, hsf⟩ => (countable_range f).mono hsf⟩

/-- A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
protected theorem countable_iff_exists_surjective {s : Set α} (hs : s.Nonempty) :
    s.Countable ↔ ∃ f : ℕ → s, Surjective f :=
  countable_coe_iff.symm.trans <| @countable_iff_exists_surjective s hs.to_subtype

alias Set.countable_iff_exists_surjective ↔ countable.exists_surjective _

theorem countable_univ [Countable α] : (Univ : Set α).Countable :=
  to_countable Univ

/-- If `s : set α` is a nonempty countable set, then there exists a map
`f : ℕ → α` such that `s = range f`. -/
theorem Countable.exists_eq_range {s : Set α} (hc : s.Countable) (hs : s.Nonempty) : ∃ f : ℕ → α, s = Range f := by
  rcases hc.exists_surjective hs with ⟨f, hf⟩
  refine' ⟨coe ∘ f, _⟩
  rw [hf.range_comp, Subtype.range_coe]

@[simp]
theorem countable_empty : (∅ : Set α).Countable :=
  to_countable _

@[simp]
theorem countable_singleton (a : α) : ({a} : Set α).Countable :=
  ⟨ofEquiv _ (Equivₓ.Set.singleton a)⟩

theorem Countable.image {s : Set α} (hs : s.Countable) (f : α → β) : (f '' s).Countable := by
  rw [image_eq_range]
  haveI := hs.to_subtype
  apply countable_range

theorem MapsTo.countable_of_inj_on {s : Set α} {t : Set β} {f : α → β} (hf : MapsTo f s t) (hf' : InjOn f s)
    (ht : t.Countable) : s.Countable :=
  have : Injective (hf.restrict f s t) := (inj_on_iff_injective.1 hf').codRestrict _
  ⟨@Encodable.ofInj _ _ ht.toEncodable _ this⟩

theorem Countable.preimage_of_inj_on {s : Set β} (hs : s.Countable) {f : α → β} (hf : InjOn f (f ⁻¹' s)) :
    (f ⁻¹' s).Countable :=
  (maps_to_preimage f s).countable_of_inj_on hf hs

protected theorem Countable.preimage {s : Set β} (hs : s.Countable) {f : α → β} (hf : Injective f) :
    (f ⁻¹' s).Countable :=
  hs.preimage_of_inj_on (hf.InjOn _)

theorem exists_seq_supr_eq_top_iff_countable [CompleteLattice α] {p : α → Prop} (h : ∃ x, p x) :
    (∃ s : ℕ → α, (∀ n, p (s n)) ∧ (⨆ n, s n) = ⊤) ↔ ∃ S : Set α, S.Countable ∧ (∀, ∀ s ∈ S, ∀, p s) ∧ sup S = ⊤ := by
  constructor
  · rintro ⟨s, hps, hs⟩
    refine' ⟨range s, countable_range s, forall_range_iff.2 hps, _⟩
    rwa [Sup_range]
    
  · rintro ⟨S, hSc, hps, hS⟩
    rcases eq_empty_or_nonempty S with (rfl | hne)
    · rw [Sup_empty] at hS
      haveI := subsingleton_of_bot_eq_top hS
      rcases h with ⟨x, hx⟩
      exact ⟨fun n => x, fun n => hx, Subsingleton.elimₓ _ _⟩
      
    · rcases(Set.countable_iff_exists_surjective hne).1 hSc with ⟨s, hs⟩
      refine' ⟨fun n => s n, fun n => hps _ (s n).coe_prop, _⟩
      rwa [hs.supr_comp, ← Sup_eq_supr']
      
    

theorem exists_seq_cover_iff_countable {p : Set α → Prop} (h : ∃ s, p s) :
    (∃ s : ℕ → Set α, (∀ n, p (s n)) ∧ (⋃ n, s n) = univ) ↔
      ∃ S : Set (Set α), S.Countable ∧ (∀, ∀ s ∈ S, ∀, p s) ∧ ⋃₀S = univ :=
  exists_seq_supr_eq_top_iff_countable h

theorem countable_of_injective_of_countable_image {s : Set α} {f : α → β} (hf : InjOn f s) (hs : (f '' s).Countable) :
    s.Countable :=
  let ⟨g, hg⟩ := countable_iff_exists_inj_on.1 hs
  countable_iff_exists_inj_on.2 ⟨g ∘ f, hg.comp hf (maps_to_image _ _)⟩

theorem countable_Union {t : ι → Set α} [Countable ι] (ht : ∀ i, (t i).Countable) : (⋃ i, t i).Countable := by
  haveI := fun a => (ht a).to_subtype
  rw [Union_eq_range_psigma]
  apply countable_range

@[simp]
theorem countable_Union_iff [Countable ι] {t : ι → Set α} : (⋃ i, t i).Countable ↔ ∀ i, (t i).Countable :=
  ⟨fun h i => h.mono <| subset_Union _ _, countable_Union⟩

theorem Countable.bUnion_iff {s : Set α} {t : ∀, ∀ a ∈ s, ∀, Set β} (hs : s.Countable) :
    (⋃ a ∈ s, t a ‹_›).Countable ↔ ∀, ∀ a ∈ s, ∀, (t a ‹_›).Countable := by
  haveI := hs.to_subtype
  rw [bUnion_eq_Union, countable_Union_iff, SetCoe.forall']

theorem Countable.sUnion_iff {s : Set (Set α)} (hs : s.Countable) :
    (⋃₀s).Countable ↔ ∀, ∀ a ∈ s, ∀, (a : _).Countable := by
  rw [sUnion_eq_bUnion, hs.bUnion_iff]

alias countable.bUnion_iff ↔ _ countable.bUnion

alias countable.sUnion_iff ↔ _ countable.sUnion

@[simp]
theorem countable_union {s t : Set α} : (s ∪ t).Countable ↔ s.Countable ∧ t.Countable := by
  simp [← union_eq_Union, ← And.comm]

theorem Countable.union {s t : Set α} (hs : s.Countable) (ht : t.Countable) : (s ∪ t).Countable :=
  countable_union.2 ⟨hs, ht⟩

@[simp]
theorem countable_insert {s : Set α} {a : α} : (insert a s).Countable ↔ s.Countable := by
  simp only [← insert_eq, ← countable_union, ← countable_singleton, ← true_andₓ]

theorem Countable.insert {s : Set α} (a : α) (h : s.Countable) : (insert a s).Countable :=
  countable_insert.2 h

theorem Finite.countable {s : Set α} : s.Finite → s.Countable
  | ⟨h⟩ => Trunc.nonempty (Fintype.truncEncodable s)

@[nontriviality]
theorem Countable.of_subsingleton [Subsingleton α] (s : Set α) : s.Countable :=
  (Finite.of_subsingleton s).Countable

theorem Subsingleton.countable {s : Set α} (hs : s.Subsingleton) : s.Countable :=
  hs.Finite.Countable

theorem countable_is_top (α : Type _) [PartialOrderₓ α] : { x : α | IsTop x }.Countable :=
  (finite_is_top α).Countable

theorem countable_is_bot (α : Type _) [PartialOrderₓ α] : { x : α | IsBot x }.Countable :=
  (finite_is_bot α).Countable

/-- The set of finite subsets of a countable set is countable. -/
theorem countable_set_of_finite_subset {s : Set α} : s.Countable → { t | Set.Finite t ∧ t ⊆ s }.Countable
  | ⟨h⟩ => by
    skip
    refine' countable.mono _ (countable_range fun t : Finset s => { a | ∃ h : a ∈ s, Subtype.mk a h ∈ t })
    rintro t ⟨⟨ht⟩, ts⟩
    skip
    refine' ⟨finset.univ.map (embedding_of_subset _ _ ts), Set.ext fun a => _⟩
    simpa using @ts a

theorem countable_univ_pi {π : α → Type _} [Finite α] {s : ∀ a, Set (π a)} (hs : ∀ a, (s a).Countable) :
    (Pi Univ s).Countable := by
  haveI := fun a => (hs a).to_subtype
  exact (Countable.of_equiv _ (Equivₓ.Set.univPi s).symm).to_set

theorem countable_pi {π : α → Type _} [Finite α] {s : ∀ a, Set (π a)} (hs : ∀ a, (s a).Countable) :
    { f : ∀ a, π a | ∀ a, f a ∈ s a }.Countable := by
  simpa only [mem_univ_pi] using countable_univ_pi hs

protected theorem Countable.prod {s : Set α} {t : Set β} (hs : s.Countable) (ht : t.Countable) :
    Set.Countable (s ×ˢ t) := by
  haveI : Countable s := hs.to_subtype
  haveI : Countable t := ht.to_subtype
  exact (Countable.of_equiv _ <| (Equivₓ.Set.prod _ _).symm).to_set

theorem Countable.image2 {s : Set α} {t : Set β} (hs : s.Countable) (ht : t.Countable) (f : α → β → γ) :
    (Image2 f s t).Countable := by
  rw [← image_prod]
  exact (hs.prod ht).Image _

end Set

theorem Finset.countable_to_set (s : Finset α) : Set.Countable (↑s : Set α) :=
  s.finite_to_set.Countable

