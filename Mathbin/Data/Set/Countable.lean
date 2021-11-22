import Mathbin.Data.Equiv.List 
import Mathbin.Data.Set.Finite

/-!
# Countable sets
-/


noncomputable theory

open Function Set Encodable

open Classical hiding some

open_locale Classical

universe u v w

variable{α : Type u}{β : Type v}{γ : Type w}

namespace Set

/-- A set is countable if there exists an encoding of the set into the natural numbers.
An encoding is an injection with a partial inverse, which can be viewed as a
constructive analogue of countability. (For the most part, theorems about
`countable` will be classical and `encodable` will be constructive.)
-/
def countable (s : Set α) : Prop :=
  Nonempty (Encodable s)

theorem countable_iff_exists_injective {s : Set α} : countable s ↔ ∃ f : s → ℕ, injective f :=
  ⟨fun ⟨h⟩ =>
      by 
        exactI ⟨encode, encode_injective⟩,
    fun ⟨f, h⟩ => ⟨⟨f, partial_inv f, partial_inv_left h⟩⟩⟩

/-- A set `s : set α` is countable if and only if there exists a function `α → ℕ` injective
on `s`. -/
theorem countable_iff_exists_inj_on {s : Set α} : countable s ↔ ∃ f : α → ℕ, inj_on f s :=
  countable_iff_exists_injective.trans
    ⟨fun ⟨f, hf⟩ =>
        ⟨fun a => if h : a ∈ s then f ⟨a, h⟩ else 0,
          fun a as b bs h =>
            congr_argₓ Subtype.val$
              hf$
                by 
                  simpa [as, bs] using h⟩,
      fun ⟨f, hf⟩ => ⟨_, inj_on_iff_injective.1 hf⟩⟩

theorem countable_iff_exists_surjective [ne : Nonempty α] {s : Set α} : countable s ↔ ∃ f : ℕ → α, s ⊆ range f :=
  ⟨fun ⟨h⟩ =>
      by 
        inhabit α <;>
          exactI
            ⟨fun n => ((decode s n).map Subtype.val).iget,
              fun a as =>
                ⟨encode (⟨a, as⟩ : s),
                  by 
                    simp [encodek]⟩⟩,
    fun ⟨f, hf⟩ =>
      ⟨⟨fun x => inv_fun f x.1, fun n => if h : f n ∈ s then some ⟨f n, h⟩ else none,
          fun ⟨x, hx⟩ =>
            by 
              have  := inv_fun_eq (hf hx)
              dsimp  at this⊢
              simp [this, hx]⟩⟩⟩

/--
A non-empty set is countable iff there exists a surjection from the
natural numbers onto the subtype induced by the set.
-/
theorem countable_iff_exists_surjective_to_subtype {s : Set α} (hs : s.nonempty) :
  countable s ↔ ∃ f : ℕ → s, surjective f :=
  have  : Inhabited s := ⟨Classical.choice hs.to_subtype⟩
  have  : countable s → ∃ f : ℕ → s, surjective f :=
    fun ⟨h⟩ =>
      by 
        exactI
          ⟨fun n => (decode s n).iget,
            fun a =>
              ⟨encode a,
                by 
                  simp [encodek]⟩⟩
  have  : (∃ f : ℕ → s, surjective f) → countable s :=
    fun ⟨f, fsurj⟩ =>
      ⟨⟨inv_fun f, Option.some ∘ f,
          by 
            intro h <;> simp [(inv_fun_eq (fsurj h) : f (inv_fun f h) = h)]⟩⟩
  by 
    split  <;> assumption

/-- Convert `countable s` to `encodable s` (noncomputable). -/
def countable.to_encodable {s : Set α} : countable s → Encodable s :=
  Classical.choice

theorem countable_encodable' (s : Set α) [H : Encodable s] : countable s :=
  ⟨H⟩

theorem countable_encodable [Encodable α] (s : Set α) : countable s :=
  ⟨by 
      infer_instance⟩

/-- If `s : set α` is a nonempty countable set, then there exists a map
`f : ℕ → α` such that `s = range f`. -/
theorem countable.exists_surjective {s : Set α} (hc : countable s) (hs : s.nonempty) : ∃ f : ℕ → α, s = range f :=
  by 
    letI this : Encodable s := countable.to_encodable hc 
    letI this : Nonempty s := hs.to_subtype 
    have  : countable (univ : Set s) := countable_encodable _ 
    rcases countable_iff_exists_surjective.1 this with ⟨g, hg⟩
    have  : range g = univ := univ_subset_iff.1 hg 
    use coeₓ ∘ g 
    simp only [range_comp, this, image_univ, Subtype.range_coe]

@[simp]
theorem countable_empty : countable (∅ : Set α) :=
  ⟨⟨fun x => x.2.elim, fun n => none, fun x => x.2.elim⟩⟩

@[simp]
theorem countable_singleton (a : α) : countable ({a} : Set α) :=
  ⟨of_equiv _ (Equiv.Set.singleton a)⟩

theorem countable.mono {s₁ s₂ : Set α} (h : s₁ ⊆ s₂) : countable s₂ → countable s₁
| ⟨H⟩ => ⟨@of_inj _ _ H _ (embedding_of_subset _ _ h).2⟩

theorem countable.image {s : Set α} (hs : countable s) (f : α → β) : countable (f '' s) :=
  have  : surjective ((maps_to_image f s).restrict _ _ _) := surjective_maps_to_image_restrict f s
  ⟨@Encodable.ofInj _ _ hs.to_encodable (surj_inv this) (injective_surj_inv this)⟩

theorem countable_range [Encodable α] (f : α → β) : countable (range f) :=
  by 
    rw [←image_univ] <;> exact (countable_encodable _).Image _

theorem maps_to.countable_of_inj_on {s : Set α} {t : Set β} {f : α → β} (hf : maps_to f s t) (hf' : inj_on f s)
  (ht : countable t) : countable s :=
  have  : injective (hf.restrict f s t) := (inj_on_iff_injective.1 hf').codRestrict _
  ⟨@Encodable.ofInj _ _ ht.to_encodable _ this⟩

theorem countable.preimage_of_inj_on {s : Set β} (hs : countable s) {f : α → β} (hf : inj_on f (f ⁻¹' s)) :
  countable (f ⁻¹' s) :=
  (maps_to_preimage f s).countable_of_inj_on hf hs

protected theorem countable.preimage {s : Set β} (hs : countable s) {f : α → β} (hf : injective f) :
  countable (f ⁻¹' s) :=
  hs.preimage_of_inj_on (hf.inj_on _)

theorem exists_seq_supr_eq_top_iff_countable [CompleteLattice α] {p : α → Prop} (h : ∃ x, p x) :
  (∃ s : ℕ → α, (∀ n, p (s n)) ∧ (⨆n, s n) = ⊤) ↔ ∃ S : Set α, countable S ∧ (∀ s _ : s ∈ S, p s) ∧ Sup S = ⊤ :=
  by 
    split 
    ·
      rintro ⟨s, hps, hs⟩
      refine' ⟨range s, countable_range s, forall_range_iff.2 hps, _⟩
      rwa [Sup_range]
    ·
      rintro ⟨S, hSc, hps, hS⟩
      rcases eq_empty_or_nonempty S with (rfl | hne)
      ·
        rw [Sup_empty] at hS 
        haveI  := subsingleton_of_bot_eq_top hS 
        rcases h with ⟨x, hx⟩
        exact ⟨fun n => x, fun n => hx, Subsingleton.elimₓ _ _⟩
      ·
        rcases(countable_iff_exists_surjective_to_subtype hne).1 hSc with ⟨s, hs⟩
        refine' ⟨fun n => s n, fun n => hps _ (s n).coe_prop, _⟩
        rwa [hs.supr_comp, ←Sup_eq_supr']

theorem exists_seq_cover_iff_countable {p : Set α → Prop} (h : ∃ s, p s) :
  (∃ s : ℕ → Set α, (∀ n, p (s n)) ∧ (⋃n, s n) = univ) ↔
    ∃ S : Set (Set α), countable S ∧ (∀ s _ : s ∈ S, p s) ∧ ⋃₀S = univ :=
  exists_seq_supr_eq_top_iff_countable h

theorem countable_of_injective_of_countable_image {s : Set α} {f : α → β} (hf : inj_on f s) (hs : countable (f '' s)) :
  countable s :=
  let ⟨g, hg⟩ := countable_iff_exists_inj_on.1 hs 
  countable_iff_exists_inj_on.2 ⟨g ∘ f, hg.comp hf (maps_to_image _ _)⟩

theorem countable_Union {t : α → Set β} [Encodable α] (ht : ∀ a, countable (t a)) : countable (⋃a, t a) :=
  by 
    haveI  := fun a => (ht a).toEncodable <;> rw [Union_eq_range_sigma] <;> apply countable_range

theorem countable.bUnion {s : Set α} {t : ∀ x _ : x ∈ s, Set β} (hs : countable s)
  (ht : ∀ a _ : a ∈ s, countable (t a ‹_›)) : countable (⋃(a : _)(_ : a ∈ s), t a ‹_›) :=
  by 
    rw [bUnion_eq_Union]
    haveI  := hs.to_encodable 
    exact
      countable_Union
        (by 
          simpa using ht)

theorem countable.sUnion {s : Set (Set α)} (hs : countable s) (h : ∀ a _ : a ∈ s, countable a) : countable (⋃₀s) :=
  by 
    rw [sUnion_eq_bUnion] <;> exact hs.bUnion h

theorem countable_Union_Prop {p : Prop} {t : p → Set β} (ht : ∀ h : p, countable (t h)) : countable (⋃h : p, t h) :=
  by 
    byCases' p <;> simp [h, ht]

theorem countable.union {s₁ s₂ : Set α} (h₁ : countable s₁) (h₂ : countable s₂) : countable (s₁ ∪ s₂) :=
  by 
    rw [union_eq_Union] <;> exact countable_Union (Bool.forall_bool.2 ⟨h₂, h₁⟩)

@[simp]
theorem countable_union {s t : Set α} : countable (s ∪ t) ↔ countable s ∧ countable t :=
  ⟨fun h => ⟨h.mono (subset_union_left s t), h.mono (subset_union_right _ _)⟩, fun h => h.1.union h.2⟩

@[simp]
theorem countable_insert {s : Set α} {a : α} : countable (insert a s) ↔ countable s :=
  by 
    simp only [insert_eq, countable_union, countable_singleton, true_andₓ]

theorem countable.insert {s : Set α} (a : α) (h : countable s) : countable (insert a s) :=
  countable_insert.2 h

theorem finite.countable {s : Set α} : finite s → countable s
| ⟨h⟩ =>
  Trunc.nonempty
    (by 
      exactI trunc_encodable_of_fintype s)

theorem subsingleton.countable {s : Set α} (hs : s.subsingleton) : countable s :=
  hs.finite.countable

theorem countable_is_top (α : Type _) [PartialOrderₓ α] : countable { x : α | IsTop x } :=
  (finite_is_top α).Countable

theorem countable_is_bot (α : Type _) [PartialOrderₓ α] : countable { x : α | IsBot x } :=
  (finite_is_bot α).Countable

/-- The set of finite subsets of a countable set is countable. -/
theorem countable_set_of_finite_subset {s : Set α} : countable s → countable { t | finite t ∧ t ⊆ s }
| ⟨h⟩ =>
  by 
    resetI 
    refine' countable.mono _ (countable_range fun t : Finset s => { a | ∃ h : a ∈ s, Subtype.mk a h ∈ t })
    rintro t ⟨⟨ht⟩, ts⟩
    resetI 
    refine' ⟨finset.univ.map (embedding_of_subset _ _ ts), Set.ext$ fun a => _⟩
    suffices  : a ∈ s ∧ a ∈ t ↔ a ∈ t
    ·
      simpa 
    exact ⟨And.right, fun h => ⟨ts h, h⟩⟩

theorem countable_pi {π : α → Type _} [Fintype α] {s : ∀ a, Set (π a)} (hs : ∀ a, countable (s a)) :
  countable { f : ∀ a, π a | ∀ a, f a ∈ s a } :=
  countable.mono
      (show { f : ∀ a, π a | ∀ a, f a ∈ s a } ⊆ range fun f : ∀ a, s a => fun a => (f a).1 from
        fun f hf => ⟨fun a => ⟨f a, hf a⟩, funext$ fun a => rfl⟩)$
    have  : Trunc (Encodable (∀ a : α, s a)) := @Encodable.fintypePi α _ _ _ fun a => (hs a).toEncodable 
    Trunc.induction_on this$ fun h => @countable_range _ _ h _

protected theorem countable.prod {s : Set α} {t : Set β} (hs : countable s) (ht : countable t) :
  countable (Set.Prod s t) :=
  by 
    haveI  : Encodable s := hs.to_encodable 
    haveI  : Encodable t := ht.to_encodable 
    haveI  : Encodable (s × t)
    ·
      infer_instance 
    have  : range (Prod.mapₓ coeₓ coeₓ : s × t → α × β) = Set.Prod s t
    ·
      rw [range_prod_map, Subtype.range_coe, Subtype.range_coe]
    rw [←this]
    exact countable_range _

theorem countable.image2 {s : Set α} {t : Set β} (hs : countable s) (ht : countable t) (f : α → β → γ) :
  countable (image2 f s t) :=
  by 
    rw [←image_prod]
    exact (hs.prod ht).Image _

section Enumerate

/-- Enumerate elements in a countable set.-/
def enumerate_countable {s : Set α} (h : countable s) (default : α) : ℕ → α :=
  fun n =>
    match @Encodable.decode s h.to_encodable n with 
    | some y => y
    | none => default

theorem subset_range_enumerate {s : Set α} (h : countable s) (default : α) :
  s ⊆ range (enumerate_countable h default) :=
  fun x hx =>
    ⟨@Encodable.encode s h.to_encodable ⟨x, hx⟩,
      by 
        simp [enumerate_countable, Encodable.encodek]⟩

end Enumerate

end Set

theorem Finset.countable_to_set (s : Finset α) : Set.Countable («expr↑ » s : Set α) :=
  s.finite_to_set.countable

