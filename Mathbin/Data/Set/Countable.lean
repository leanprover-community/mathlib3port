/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Data.Set.Finite
import Mathbin.Logic.Equiv.List

/-!
# Countable sets
-/


noncomputable section

open Function Set Encodable

open Classical hiding some

open Classical

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace Set

/-- A set is countable if there exists an encoding of the set into the natural numbers.
An encoding is an injection with a partial inverse, which can be viewed as a
constructive analogue of countability. (For the most part, theorems about
`countable` will be classical and `encodable` will be constructive.)
-/
def Countable (s : Set α) : Prop :=
  Nonempty (Encodable s)

theorem countable_iff_exists_injective {s : Set α} : Countable s ↔ ∃ f : s → ℕ, Injective f :=
  ⟨fun ⟨h⟩ => ⟨encode, encode_injective⟩, fun ⟨f, h⟩ => ⟨⟨f, partialInv f, partial_inv_left h⟩⟩⟩

/-- A set `s : set α` is countable if and only if there exists a function `α → ℕ` injective
on `s`. -/
theorem countable_iff_exists_inj_on {s : Set α} : Countable s ↔ ∃ f : α → ℕ, InjOn f s :=
  countable_iff_exists_injective.trans
    ⟨fun ⟨f, hf⟩ =>
      ⟨fun a => if h : a ∈ s then f ⟨a, h⟩ else 0, fun a as b bs h =>
        congr_arg Subtype.val <|
          hf <| by
            simpa [as, bs] using h⟩,
      fun ⟨f, hf⟩ => ⟨_, inj_on_iff_injective.1 hf⟩⟩

theorem countable_iff_exists_surjective [ne : Nonempty α] {s : Set α} : Countable s ↔ ∃ f : ℕ → α, s ⊆ Range f :=
  ⟨fun ⟨h⟩ => by
    inhabit α <;>
      exact
        ⟨fun n => ((decode s n).map Subtype.val).iget, fun a as =>
          ⟨encode (⟨a, as⟩ : s), by
            simp [encodek]⟩⟩,
    fun ⟨f, hf⟩ =>
    ⟨⟨fun x => invFun f x.1, fun n => if h : f n ∈ s then some ⟨f n, h⟩ else none, fun ⟨x, hx⟩ => by
        have := inv_fun_eq (hf hx)
        dsimp'  at this⊢
        simp [this, hx]⟩⟩⟩

/-- A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
theorem countable_iff_exists_surjective_to_subtype {s : Set α} (hs : s.Nonempty) :
    Countable s ↔ ∃ f : ℕ → s, Surjective f := by
  have : Inhabited s := ⟨Classical.choice hs.to_subtype⟩
  have : Countable s → ∃ f : ℕ → s, Surjective f := fun ⟨h⟩ =>
    ⟨fun n => (decode s n).iget, fun a =>
      ⟨encode a, by
        simp [encodek]⟩⟩
  have : (∃ f : ℕ → s, Surjective f) → Countable s := fun ⟨f, fsurj⟩ =>
    ⟨⟨invFun f, Option.some ∘ f, by
        intro h <;> simp [(inv_fun_eq (fsurj h) : f (inv_fun f h) = h)]⟩⟩
  constructor <;> assumption

/-- Convert `countable s` to `encodable s` (noncomputable). -/
def Countable.toEncodable {s : Set α} : Countable s → Encodable s :=
  Classical.choice

theorem countable_encodable' (s : Set α) [H : Encodable s] : Countable s :=
  ⟨H⟩

theorem countable_encodable [Encodable α] (s : Set α) : Countable s :=
  ⟨by
    infer_instance⟩

/-- If `s : set α` is a nonempty countable set, then there exists a map
`f : ℕ → α` such that `s = range f`. -/
theorem Countable.exists_surjective {s : Set α} (hc : Countable s) (hs : s.Nonempty) : ∃ f : ℕ → α, s = Range f := by
  let this : Encodable s := countable.to_encodable hc
  let this : Nonempty s := hs.to_subtype
  have : countable (univ : Set s) := countable_encodable _
  rcases countable_iff_exists_surjective.1 this with ⟨g, hg⟩
  have : range g = univ := univ_subset_iff.1 hg
  use coe ∘ g
  simp only [range_comp, this, image_univ, Subtype.range_coe]

@[simp]
theorem countable_empty : Countable (∅ : Set α) :=
  ⟨⟨fun x => x.2.elim, fun n => none, fun x => x.2.elim⟩⟩

@[simp]
theorem countable_singleton (a : α) : Countable ({a} : Set α) :=
  ⟨ofEquiv _ (Equivₓ.Set.singleton a)⟩

theorem Countable.mono {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) : Countable s₂ → Countable s₁
  | ⟨H⟩ => ⟨@ofInj _ _ H _ (embeddingOfSubset _ _ h).2⟩

theorem Countable.image {s : Set α} (hs : Countable s) (f : α → β) : Countable (f '' s) :=
  have : Surjective ((maps_to_image f s).restrict _ _ _) := surjective_maps_to_image_restrict f s
  ⟨@Encodable.ofInj _ _ hs.toEncodable (surjInv this) (injective_surj_inv this)⟩

theorem countable_range [Encodable α] (f : α → β) : Countable (Range f) := by
  rw [← image_univ] <;> exact (countable_encodable _).Image _

theorem MapsTo.countable_of_inj_on {s : Set α} {t : Set β} {f : α → β} (hf : MapsTo f s t) (hf' : InjOn f s)
    (ht : Countable t) : Countable s :=
  have : Injective (hf.restrict f s t) := (inj_on_iff_injective.1 hf').codRestrict _
  ⟨@Encodable.ofInj _ _ ht.toEncodable _ this⟩

theorem Countable.preimage_of_inj_on {s : Set β} (hs : Countable s) {f : α → β} (hf : InjOn f (f ⁻¹' s)) :
    Countable (f ⁻¹' s) :=
  (maps_to_preimage f s).countable_of_inj_on hf hs

protected theorem Countable.preimage {s : Set β} (hs : Countable s) {f : α → β} (hf : Injective f) :
    Countable (f ⁻¹' s) :=
  hs.preimage_of_inj_on (hf.InjOn _)

theorem exists_seq_supr_eq_top_iff_countable [CompleteLattice α] {p : α → Prop} (h : ∃ x, p x) :
    (∃ s : ℕ → α, (∀ n, p (s n)) ∧ (⨆ n, s n) = ⊤) ↔ ∃ S : Set α, Countable S ∧ (∀, ∀ s ∈ S, ∀, p s) ∧ sup S = ⊤ := by
  constructor
  · rintro ⟨s, hps, hs⟩
    refine' ⟨range s, countable_range s, forall_range_iff.2 hps, _⟩
    rwa [Sup_range]
    
  · rintro ⟨S, hSc, hps, hS⟩
    rcases eq_empty_or_nonempty S with (rfl | hne)
    · rw [Sup_empty] at hS
      have := subsingleton_of_bot_eq_top hS
      rcases h with ⟨x, hx⟩
      exact ⟨fun n => x, fun n => hx, Subsingleton.elimₓ _ _⟩
      
    · rcases(countable_iff_exists_surjective_to_subtype hne).1 hSc with ⟨s, hs⟩
      refine' ⟨fun n => s n, fun n => hps _ (s n).coe_prop, _⟩
      rwa [hs.supr_comp, ← Sup_eq_supr']
      
    

theorem exists_seq_cover_iff_countable {p : Set α → Prop} (h : ∃ s, p s) :
    (∃ s : ℕ → Set α, (∀ n, p (s n)) ∧ (⋃ n, s n) = univ) ↔
      ∃ S : Set (Set α), Countable S ∧ (∀, ∀ s ∈ S, ∀, p s) ∧ ⋃₀S = univ :=
  exists_seq_supr_eq_top_iff_countable h

theorem countable_of_injective_of_countable_image {s : Set α} {f : α → β} (hf : InjOn f s) (hs : Countable (f '' s)) :
    Countable s :=
  let ⟨g, hg⟩ := countable_iff_exists_inj_on.1 hs
  countable_iff_exists_inj_on.2 ⟨g ∘ f, hg.comp hf (maps_to_image _ _)⟩

theorem countable_Union {t : α → Set β} [Encodable α] (ht : ∀ a, Countable (t a)) : Countable (⋃ a, t a) := by
  have := fun a => (ht a).toEncodable <;> rw [Union_eq_range_sigma] <;> apply countable_range

theorem Countable.bUnion {s : Set α} {t : ∀, ∀ x ∈ s, ∀, Set β} (hs : Countable s)
    (ht : ∀, ∀ a ∈ s, ∀, Countable (t a ‹_›)) : Countable (⋃ a ∈ s, t a ‹_›) := by
  rw [bUnion_eq_Union]
  have := hs.to_encodable
  exact
    countable_Union
      (by
        simpa using ht)

theorem Countable.sUnion {s : Set (Set α)} (hs : Countable s) (h : ∀, ∀ a ∈ s, ∀, Countable a) : Countable (⋃₀s) := by
  rw [sUnion_eq_bUnion] <;> exact hs.bUnion h

theorem countable_Union_Prop {p : Prop} {t : p → Set β} (ht : ∀ h : p, Countable (t h)) : Countable (⋃ h : p, t h) := by
  by_cases' p <;> simp [h, ht]

theorem Countable.union {s₁ s₂ : Set α} (h₁ : Countable s₁) (h₂ : Countable s₂) : Countable (s₁ ∪ s₂) := by
  rw [union_eq_Union] <;> exact countable_Union (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp]
theorem countable_union {s t : Set α} : Countable (s ∪ t) ↔ Countable s ∧ Countable t :=
  ⟨fun h => ⟨h.mono (subset_union_left s t), h.mono (subset_union_right _ _)⟩, fun h => h.1.union h.2⟩

@[simp]
theorem countable_insert {s : Set α} {a : α} : Countable (insert a s) ↔ Countable s := by
  simp only [insert_eq, countable_union, countable_singleton, true_andₓ]

theorem Countable.insert {s : Set α} (a : α) (h : Countable s) : Countable (insert a s) :=
  countable_insert.2 h

theorem Finite.countable {s : Set α} : s.Finite → Countable s
  | ⟨h⟩ => Trunc.nonempty (Fintype.truncEncodable s)

@[nontriviality]
theorem Countable.of_subsingleton [Subsingleton α] (s : Set α) : Countable s :=
  (Finite.of_subsingleton s).Countable

theorem Subsingleton.countable {s : Set α} (hs : s.Subsingleton) : Countable s :=
  hs.Finite.Countable

theorem countable_is_top (α : Type _) [PartialOrderₓ α] : Countable { x : α | IsTop x } :=
  (finite_is_top α).Countable

theorem countable_is_bot (α : Type _) [PartialOrderₓ α] : Countable { x : α | IsBot x } :=
  (finite_is_bot α).Countable

/-- The set of finite subsets of a countable set is countable. -/
theorem countable_set_of_finite_subset {s : Set α} : Countable s → Countable { t | Set.Finite t ∧ t ⊆ s }
  | ⟨h⟩ => by
    skip
    refine' countable.mono _ (countable_range fun t : Finset s => { a | ∃ h : a ∈ s, Subtype.mk a h ∈ t })
    rintro t ⟨⟨ht⟩, ts⟩
    skip
    refine' ⟨finset.univ.map (embedding_of_subset _ _ ts), Set.ext fun a => _⟩
    suffices a ∈ s ∧ a ∈ t ↔ a ∈ t by
      simpa
    exact ⟨And.right, fun h => ⟨ts h, h⟩⟩

theorem countable_pi {π : α → Type _} [Fintype α] {s : ∀ a, Set (π a)} (hs : ∀ a, Countable (s a)) :
    Countable { f : ∀ a, π a | ∀ a, f a ∈ s a } :=
  Countable.mono
      (show { f : ∀ a, π a | ∀ a, f a ∈ s a } ⊆ Range fun f : ∀ a, s a => fun a => (f a).1 from fun f hf =>
        ⟨fun a => ⟨f a, hf a⟩, funext fun a => rfl⟩) <|
    have : Trunc (Encodable (∀ a : α, s a)) := @Encodable.fintypePi α _ _ _ fun a => (hs a).toEncodable
    (Trunc.induction_on this) fun h => @countable_range _ _ h _

protected theorem Countable.prod {s : Set α} {t : Set β} (hs : Countable s) (ht : Countable t) : Countable (s ×ˢ t) :=
  by
  have : Encodable s := hs.to_encodable
  have : Encodable t := ht.to_encodable
  exact ⟨of_equiv (s × t) (Equivₓ.Set.prod _ _)⟩

theorem Countable.image2 {s : Set α} {t : Set β} (hs : Countable s) (ht : Countable t) (f : α → β → γ) :
    Countable (Image2 f s t) := by
  rw [← image_prod]
  exact (hs.prod ht).Image _

section Enumerate

/-- Enumerate elements in a countable set.-/
def enumerateCountable {s : Set α} (h : Countable s) (default : α) : ℕ → α := fun n =>
  match @Encodable.decode s h.toEncodable n with
  | some y => y
  | none => default

theorem subset_range_enumerate {s : Set α} (h : Countable s) (default : α) : s ⊆ Range (enumerateCountable h default) :=
  fun x hx =>
  ⟨@Encodable.encode s h.toEncodable ⟨x, hx⟩, by
    simp [enumerate_countable, Encodable.encodek]⟩

end Enumerate

end Set

theorem Finset.countable_to_set (s : Finset α) : Set.Countable (↑s : Set α) :=
  s.finite_to_set.Countable

