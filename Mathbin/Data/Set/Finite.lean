/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.Finset.Sort
import Mathbin.Data.Set.Functor

/-!
# Finite sets

This file defines predicates `finite : set α → Prop` and `infinite : set α → Prop` and proves some
basic facts about finite sets.
-/


open Set Function

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Set

/-- A set is finite if the subtype is a fintype, i.e. there is a
  list that enumerates its members. -/
inductive Finite (s : Set α) : Prop
  | intro : Fintype s → finite

theorem finite_def {s : Set α} : Finite s ↔ Nonempty (Fintype s) :=
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩

/-- A set is infinite if it is not finite. -/
def Infinite (s : Set α) : Prop :=
  ¬Finite s

/-- The subtype corresponding to a finite set is a finite type. Note
that because `finite` isn't a typeclass, this will not fire if it
is made into an instance -/
noncomputable def Finite.fintype {s : Set α} (h : Finite s) : Fintype s :=
  Classical.choice <| finite_def.1 h

/-- Get a finset from a finite set -/
noncomputable def Finite.toFinset {s : Set α} (h : Finite s) : Finset α :=
  @Set.toFinset _ _ h.Fintype

@[simp]
theorem not_infinite {s : Set α} : ¬s.Infinite ↔ s.Finite := by
  simp [Infinite]

/-- See also `fintype_or_infinite`. -/
theorem finite_or_infinite {s : Set α} : s.Finite ∨ s.Infinite :=
  em _

@[simp]
theorem Finite.mem_to_finset {s : Set α} (h : Finite s) {a : α} : a ∈ h.toFinset ↔ a ∈ s :=
  @mem_to_finset _ _ h.Fintype _

@[simp]
theorem Finite.toFinset.nonempty {s : Set α} (h : Finite s) : h.toFinset.Nonempty ↔ s.Nonempty :=
  show (∃ x, x ∈ h.toFinset) ↔ ∃ x, x ∈ s from exists_congr fun _ => h.mem_to_finset

@[simp]
theorem Finite.coe_to_finset {s : Set α} (h : Finite s) : ↑h.toFinset = s :=
  @Set.coe_to_finset _ s h.Fintype

@[simp]
theorem Finite.coe_sort_to_finset {s : Set α} (h : Finite s) : (h.toFinset : Type _) = s := by
  rw [← Finset.coe_sort_coe _, h.coe_to_finset]

@[simp]
theorem finite_empty_to_finset (h : Finite (∅ : Set α)) : h.toFinset = ∅ := by
  rw [← Finset.coe_inj, h.coe_to_finset, Finset.coe_empty]

@[simp]
theorem Finite.to_finset_inj {s t : Set α} {hs : Finite s} {ht : Finite t} : hs.toFinset = ht.toFinset ↔ s = t := by
  simp [← Finset.coe_inj]

theorem subset_to_finset_iff {s : Finset α} {t : Set α} (ht : Finite t) : s ⊆ ht.toFinset ↔ ↑s ⊆ t := by
  rw [← Finset.coe_subset, ht.coe_to_finset]

@[simp]
theorem finite_to_finset_eq_empty_iff {s : Set α} {h : Finite s} : h.toFinset = ∅ ↔ s = ∅ := by
  simp [← Finset.coe_inj]

theorem Finite.exists_finset {s : Set α} : Finite s → ∃ s' : Finset α, ∀ a : α, a ∈ s' ↔ a ∈ s
  | ⟨h⟩ => ⟨to_finset s, fun _ => mem_to_finset⟩

theorem Finite.exists_finset_coe {s : Set α} (hs : Finite s) : ∃ s' : Finset α, ↑s' = s :=
  ⟨hs.toFinset, hs.coe_to_finset⟩

/-- Finite sets can be lifted to finsets. -/
instance : CanLift (Set α) (Finset α) where
  coe := coe
  cond := Finite
  prf := fun s hs => hs.exists_finset_coe

theorem finite_mem_finset (s : Finset α) : Finite { a | a ∈ s } :=
  ⟨Fintype.ofFinset s fun _ => Iff.rfl⟩

theorem Finite.of_fintype [Fintype α] (s : Set α) : Finite s := by
  classical <;> exact ⟨setFintype s⟩

theorem exists_finite_iff_finset {p : Set α → Prop} : (∃ s, Finite s ∧ p s) ↔ ∃ s : Finset α, p ↑s :=
  ⟨fun ⟨s, hs, hps⟩ => ⟨hs.toFinset, hs.coe_to_finset.symm ▸ hps⟩, fun ⟨s, hs⟩ => ⟨↑s, finite_mem_finset s, hs⟩⟩

theorem Finite.fin_embedding {s : Set α} (h : Finite s) : ∃ (n : ℕ)(f : Finₓ n ↪ α), Range f = s :=
  ⟨_, (Fintype.equivFin (h.toFinset : Set α)).symm.asEmbedding, by
    simp ⟩

theorem Finite.fin_param {s : Set α} (h : Finite s) : ∃ (n : ℕ)(f : Finₓ n → α), Injective f ∧ Range f = s :=
  let ⟨n, f, hf⟩ := h.fin_embedding
  ⟨n, f, f.Injective, hf⟩

/-- Membership of a subset of a finite type is decidable.

Using this as an instance leads to potential loops with `subtype.fintype` under certain decidability
assumptions, so it should only be declared a local instance. -/
def decidableMemOfFintype [DecidableEq α] (s : Set α) [Fintype s] a : Decidable (a ∈ s) :=
  decidableOfIff _ mem_to_finset

instance fintypeEmpty : Fintype (∅ : Set α) :=
  Fintype.ofFinset ∅ <| by
    simp

theorem empty_card : Fintype.card (∅ : Set α) = 0 :=
  rfl

@[simp]
theorem empty_card' {h : Fintype.{u} (∅ : Set α)} : @Fintype.card (∅ : Set α) h = 0 :=
  Eq.trans
    (by
      congr)
    empty_card

@[simp]
theorem finite_empty : @Finite α ∅ :=
  ⟨Set.fintypeEmpty⟩

instance Finite.inhabited : Inhabited { s : Set α // Finite s } :=
  ⟨⟨∅, finite_empty⟩⟩

/-- A `fintype` structure on `insert a s`. -/
def fintypeInsert' {a : α} (s : Set α) [Fintype s] (h : a ∉ s) : Fintype (insert a s : Set α) :=
  Fintype.ofFinset
      ⟨a ::ₘ s.toFinset.1,
        s.toFinset.Nodup.cons
          (by
            simp [h])⟩ <|
    by
    simp

theorem card_fintype_insert' {a : α} (s : Set α) [Fintype s] (h : a ∉ s) :
    @Fintype.card _ (fintypeInsert' s h) = Fintype.card s + 1 := by
  rw [fintype_insert', Fintype.card_of_finset] <;> simp [Finset.card, to_finset] <;> rfl

@[simp]
theorem card_insert {a : α} (s : Set α) [Fintype s] (h : a ∉ s) {d : Fintype.{u} (insert a s : Set α)} :
    @Fintype.card _ d = Fintype.card s + 1 := by
  rw [← card_fintype_insert' s h] <;> congr

theorem card_image_of_inj_on {s : Set α} [Fintype s] {f : α → β} [Fintype (f '' s)]
    (H : ∀, ∀ x ∈ s, ∀, ∀, ∀ y ∈ s, ∀, f x = f y → x = y) : Fintype.card (f '' s) = Fintype.card s :=
  have := Classical.propDecidable
  calc
    Fintype.card (f '' s) = (s.to_finset.image f).card :=
      Fintype.card_of_finset' _
        (by
          simp )
    _ = s.to_finset.card :=
      Finset.card_image_of_inj_on fun x hx y hy hxy => H x (mem_to_finset.1 hx) y (mem_to_finset.1 hy) hxy
    _ = Fintype.card s := (Fintype.card_of_finset' _ fun a => mem_to_finset).symm
    

theorem card_image_of_injective (s : Set α) [Fintype s] {f : α → β} [Fintype (f '' s)] (H : Function.Injective f) :
    Fintype.card (f '' s) = Fintype.card s :=
  card_image_of_inj_on fun _ _ _ _ h => H h

section

attribute [local instance] decidable_mem_of_fintype

instance fintypeInsert [DecidableEq α] (a : α) (s : Set α) [Fintype s] : Fintype (insert a s : Set α) :=
  if h : a ∈ s then by
    rwa [insert_eq, union_eq_self_of_subset_left (singleton_subset_iff.2 h)]
  else fintypeInsert' _ h

end

@[simp]
theorem Finite.insert (a : α) {s : Set α} : Finite s → Finite (insert a s)
  | ⟨h⟩ => ⟨@Set.fintypeInsert _ (Classical.decEq α) _ _ h⟩

theorem to_finset_insert [DecidableEq α] {a : α} {s : Set α} (hs : Finite s) :
    (hs.insert a).toFinset = insert a hs.toFinset :=
  Finset.ext <| by
    simp

@[simp]
theorem insert_to_finset [DecidableEq α] {a : α} {s : Set α} [Fintype s] :
    (insert a s).toFinset = insert a s.toFinset := by
  simp [Finset.ext_iff, mem_insert_iff]

@[elab_as_eliminator]
theorem Finite.induction_on {C : Set α → Prop} {s : Set α} (h : Finite s) (H0 : C ∅)
    (H1 : ∀ {a s}, a ∉ s → Finite s → C s → C (insert a s)) : C s :=
  let ⟨t⟩ := h
  match s.to_finset, @mem_to_finset _ s _ with
  | ⟨l, nd⟩, al => by
    change ∀ a, a ∈ l ↔ a ∈ s at al
    clear _let_match _match t h
    revert s nd al
    refine' Multiset.induction_on l _ fun a l IH => _ <;> intro s nd al
    · rw
        [show s = ∅ from
          eq_empty_iff_forall_not_mem.2
            (by
              simpa using al)]
      exact H0
      
    · rw [←
        show insert a { x | x ∈ l } = s from
          Set.ext
            (by
              simpa using al)]
      cases' Multiset.nodup_cons.1 nd with m nd'
      refine' H1 _ ⟨Finset.subtype.fintype ⟨l, nd'⟩⟩ (IH nd' fun _ => Iff.rfl)
      exact m
      

@[elab_as_eliminator]
theorem Finite.dinduction_on {C : ∀ s : Set α, Finite s → Prop} {s : Set α} (h : Finite s) (H0 : C ∅ finite_empty)
    (H1 : ∀ {a s}, a ∉ s → ∀ h : Finite s, C s h → C (insert a s) (h.insert a)) : C s h :=
  have : ∀ h : Finite s, C s h := Finite.induction_on h (fun h => H0) fun a s has hs ih h => H1 has hs (ih _)
  this h

instance fintypeSingleton (a : α) : Fintype ({a} : Set α) :=
  Unique.fintype

@[simp]
theorem card_singleton (a : α) : Fintype.card ({a} : Set α) = 1 :=
  Fintype.card_of_subsingleton _

@[simp]
theorem finite_singleton (a : α) : Finite ({a} : Set α) :=
  ⟨Set.fintypeSingleton _⟩

theorem Subsingleton.finite {s : Set α} (h : s.Subsingleton) : Finite s :=
  h.induction_on finite_empty finite_singleton

theorem to_finset_singleton (a : α) : ({a} : Set α).toFinset = {a} :=
  rfl

theorem finite_is_top (α : Type _) [PartialOrderₓ α] : Finite { x : α | IsTop x } :=
  (subsingleton_is_top α).Finite

theorem finite_is_bot (α : Type _) [PartialOrderₓ α] : Finite { x : α | IsBot x } :=
  (subsingleton_is_bot α).Finite

instance fintypePure : ∀ a : α, Fintype (pure a : Set α) :=
  Set.fintypeSingleton

theorem finite_pure (a : α) : Finite (pure a : Set α) :=
  ⟨Set.fintypePure a⟩

instance fintypeUniv [Fintype α] : Fintype (@Univ α) :=
  Fintype.ofEquiv α <| (Equivₓ.Set.univ α).symm

theorem finite_univ [Fintype α] : Finite (@Univ α) :=
  ⟨Set.fintypeUniv⟩

/-- If `(set.univ : set α)` is finite then `α` is a finite type. -/
noncomputable def fintypeOfUnivFinite (H : (Univ : Set α).Finite) : Fintype α :=
  @Fintype.ofEquiv _ (Univ : Set α) H.Fintype (Equivₓ.Set.univ _)

theorem univ_finite_iff_nonempty_fintype : (Univ : Set α).Finite ↔ Nonempty (Fintype α) := by
  constructor
  · intro h
    exact ⟨fintype_of_univ_finite h⟩
    
  · rintro ⟨_i⟩
    exact finite_univ
    

theorem infinite_univ_iff : (@Univ α).Infinite ↔ Infinite α :=
  ⟨fun h₁ => ⟨fun h₂ => h₁ <| @finite_univ α h₂⟩, fun h₂ => h₁ (fintypeOfUnivFinite h₂)⟩

theorem infinite_univ [h : Infinite α] : Infinite (@Univ α) :=
  infinite_univ_iff.2 h

theorem infinite_coe_iff {s : Set α} : Infinite s ↔ Infinite s :=
  ⟨fun h₂ => h₁ h₂.Fintype, fun h₁ => ⟨fun h₂ => h₁ ⟨h₂⟩⟩⟩

theorem Infinite.to_subtype {s : Set α} (h : Infinite s) : Infinite s :=
  infinite_coe_iff.2 h

/-- Embedding of `ℕ` into an infinite set. -/
noncomputable def Infinite.natEmbedding (s : Set α) (h : Infinite s) : ℕ ↪ s :=
  have := h.to_subtype
  Infinite.natEmbedding s

theorem Infinite.exists_subset_card_eq {s : Set α} (hs : Infinite s) (n : ℕ) : ∃ t : Finset α, ↑t ⊆ s ∧ t.card = n :=
  ⟨((Finset.range n).map (hs.natEmbedding _)).map (Embedding.subtype _), by
    simp ⟩

theorem Infinite.nonempty {s : Set α} (h : s.Infinite) : s.Nonempty :=
  let a := Infinite.natEmbedding s h 37
  ⟨a.1, a.2⟩

instance fintypeUnion [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s ∪ t : Set α) :=
  Fintype.ofFinset (s.toFinset ∪ t.toFinset) <| by
    simp

theorem Finite.union {s t : Set α} : Finite s → Finite t → Finite (s ∪ t)
  | ⟨hs⟩, ⟨ht⟩ => ⟨@Set.fintypeUnion _ (Classical.decEq α) _ _ hs ht⟩

theorem Finite.sup {s t : Set α} : Finite s → Finite t → Finite (s⊔t) :=
  finite.union

theorem infinite_of_finite_compl [Infinite α] {s : Set α} (hs : sᶜ.Finite) : s.Infinite := fun h =>
  Set.infinite_univ
    (by
      simpa using hs.union h)

theorem Finite.infinite_compl [Infinite α] {s : Set α} (hs : s.Finite) : sᶜ.Infinite := fun h =>
  Set.infinite_univ
    (by
      simpa using hs.union h)

instance fintypeSep (s : Set α) (p : α → Prop) [Fintype s] [DecidablePred p] : Fintype ({ a ∈ s | p a } : Set α) :=
  Fintype.ofFinset (s.toFinset.filter p) <| by
    simp

instance fintypeInter (s t : Set α) [Fintype s] [DecidablePred (· ∈ t)] : Fintype (s ∩ t : Set α) :=
  Set.fintypeSep s t

/-- A `fintype` structure on a set defines a `fintype` structure on its subset. -/
def fintypeSubset (s : Set α) {t : Set α} [Fintype s] [DecidablePred (· ∈ t)] (h : t ⊆ s) : Fintype t := by
  rw [← inter_eq_self_of_subset_right h] <;> infer_instance

theorem Finite.subset {s : Set α} : Finite s → ∀ {t : Set α}, t ⊆ s → Finite t
  | ⟨hs⟩, t, h => ⟨@Set.fintypeSubset _ _ _ hs (Classical.decPred t) h⟩

@[simp]
theorem finite_union {s t : Set α} : Finite (s ∪ t) ↔ Finite s ∧ Finite t :=
  ⟨fun h => ⟨h.Subset (subset_union_left _ _), h.Subset (subset_union_right _ _)⟩, fun ⟨hs, ht⟩ => hs.union ht⟩

theorem Finite.of_diff {s t : Set α} (hd : Finite (s \ t)) (ht : Finite t) : Finite s :=
  (hd.union ht).Subset <| subset_diff_union _ _

theorem Finite.inter_of_left {s : Set α} (h : Finite s) (t : Set α) : Finite (s ∩ t) :=
  h.Subset (inter_subset_left _ _)

theorem Finite.inter_of_right {s : Set α} (h : Finite s) (t : Set α) : Finite (t ∩ s) :=
  h.Subset (inter_subset_right _ _)

theorem Finite.inf_of_left {s : Set α} (h : Finite s) (t : Set α) : Finite (s⊓t) :=
  h.inter_of_left t

theorem Finite.inf_of_right {s : Set α} (h : Finite s) (t : Set α) : Finite (t⊓s) :=
  h.inter_of_right t

theorem Finite.sInter {α : Type _} {s : Set (Set α)} {t : Set α} (ht : t ∈ s) (hf : t.Finite) : (⋂₀ s).Finite :=
  hf.Subset (sInter_subset_of_mem ht)

protected theorem Infinite.mono {s t : Set α} (h : s ⊆ t) : Infinite s → Infinite t :=
  mt fun ht => ht.Subset h

theorem Infinite.diff {s t : Set α} (hs : s.Infinite) (ht : t.Finite) : (s \ t).Infinite := fun h => hs <| h.of_diff ht

@[simp]
theorem infinite_union {s t : Set α} : Infinite (s ∪ t) ↔ Infinite s ∨ Infinite t := by
  simp only [Infinite, finite_union, not_and_distrib]

instance fintypeImage [DecidableEq β] (s : Set α) (f : α → β) [Fintype s] : Fintype (f '' s) :=
  Fintype.ofFinset (s.toFinset.Image f) <| by
    simp

instance fintypeRange [DecidableEq α] (f : ι → α) [Fintype (Plift ι)] : Fintype (Range f) :=
  Fintype.ofFinset (Finset.univ.Image <| f ∘ Plift.down) <| by
    simp [(@Equivₓ.plift ι).exists_congr_left]

theorem finite_range (f : ι → α) [Fintype (Plift ι)] : Finite (Range f) :=
  have := Classical.decEq α
  ⟨by
    infer_instance⟩

theorem Finite.image {s : Set α} (f : α → β) : Finite s → Finite (f '' s)
  | ⟨h⟩ => ⟨@Set.fintypeImage _ _ (Classical.decEq β) _ _ h⟩

theorem infinite_of_infinite_image (f : α → β) {s : Set α} (hs : (f '' s).Infinite) : s.Infinite :=
  mt (Finite.image f) hs

theorem Finite.dependent_image {s : Set α} (hs : Finite s) (F : ∀, ∀ i ∈ s, ∀, β) :
    Finite { y : β | ∃ (x : _)(hx : x ∈ s), y = F x hx } := by
  let this : Fintype s := hs.fintype
  convert finite_range fun x : s => F x x.2
  simp only [SetCoe.exists, Subtype.coe_mk, eq_comm]

theorem Finite.of_preimage {f : α → β} {s : Set β} (h : Finite (f ⁻¹' s)) (hf : Surjective f) : Finite s :=
  hf.image_preimage s ▸ h.Image _

instance fintypeMap {α β} [DecidableEq β] : ∀ s : Set α f : α → β [Fintype s], Fintype (f <$> s) :=
  Set.fintypeImage

theorem Finite.map {α β} {s : Set α} : ∀ f : α → β, Finite s → Finite (f <$> s) :=
  finite.image

/-- If a function `f` has a partial inverse and sends a set `s` to a set with `[fintype]` instance,
then `s` has a `fintype` structure as well. -/
def fintypeOfFintypeImage (s : Set α) {f : α → β} {g} (I : IsPartialInv f g) [Fintype (f '' s)] : Fintype s :=
  (Fintype.ofFinset ⟨_, (f '' s).toFinset.2.filterMap g <| injective_of_partial_inv_right I⟩) fun a => by
    suffices (∃ b x, f x = b ∧ g b = some a ∧ x ∈ s) ↔ a ∈ s by
      simpa [exists_and_distrib_left.symm, And.comm, And.left_comm, And.assoc]
    rw [exists_swap]
    suffices (∃ x, x ∈ s ∧ g (f x) = some a) ↔ a ∈ s by
      simpa [And.comm, And.left_comm, And.assoc]
    simp [I _, (injective_of_partial_inv I).eq_iff]

theorem finite_of_finite_image {s : Set α} {f : α → β} (hi : Set.InjOn f s) : Finite (f '' s) → Finite s
  | ⟨h⟩ =>
    ⟨(@Fintype.ofInjective _ _ h fun a : s => ⟨f a.1, mem_image_of_mem f a.2⟩) fun a b eq =>
        Subtype.eq <| hi a.2 b.2 <| Subtype.ext_iff_val.1 Eq⟩

theorem finite_image_iff {s : Set α} {f : α → β} (hi : InjOn f s) : Finite (f '' s) ↔ Finite s :=
  ⟨finite_of_finite_image hi, Finite.image _⟩

theorem infinite_image_iff {s : Set α} {f : α → β} (hi : InjOn f s) : Infinite (f '' s) ↔ Infinite s :=
  not_congr <| finite_image_iff hi

theorem infinite_of_inj_on_maps_to {s : Set α} {t : Set β} {f : α → β} (hi : InjOn f s) (hm : MapsTo f s t)
    (hs : Infinite s) : Infinite t :=
  ((infinite_image_iff hi).2 hs).mono (maps_to'.mp hm)

theorem Infinite.exists_ne_map_eq_of_maps_to {s : Set α} {t : Set β} {f : α → β} (hs : Infinite s) (hf : MapsTo f s t)
    (ht : Finite t) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ f x = f y := by
  contrapose! ht
  exact infinite_of_inj_on_maps_to (fun x hx y hy => not_imp_not.1 (ht x hx y hy)) hf hs

theorem Infinite.exists_lt_map_eq_of_maps_to [LinearOrderₓ α] {s : Set α} {t : Set β} {f : α → β} (hs : Infinite s)
    (hf : MapsTo f s t) (ht : Finite t) : ∃ x ∈ s, ∃ y ∈ s, x < y ∧ f x = f y :=
  let ⟨x, hx, y, hy, hxy, hf⟩ := hs.exists_ne_map_eq_of_maps_to hf ht
  hxy.lt_or_lt.elim (fun hxy => ⟨x, hx, y, hy, hxy, hf⟩) fun hyx => ⟨y, hy, x, hx, hyx, hf.symm⟩

theorem Finite.exists_lt_map_eq_of_range_subset [LinearOrderₓ α] [Infinite α] {t : Set β} {f : α → β} (hf : Range f ⊆ t)
    (ht : Finite t) : ∃ a b, a < b ∧ f a = f b := by
  rw [range_subset_iff, ← maps_univ_to] at hf
  obtain ⟨a, -, b, -, h⟩ := (@infinite_univ α _).exists_lt_map_eq_of_maps_to hf ht
  exact ⟨a, b, h⟩

theorem infinite_range_of_injective [Infinite α] {f : α → β} (hi : Injective f) : Infinite (Range f) := by
  rw [← image_univ, infinite_image_iff (inj_on_of_injective hi _)]
  exact infinite_univ

theorem infinite_of_injective_forall_mem [Infinite α] {s : Set β} {f : α → β} (hi : Injective f)
    (hf : ∀ x : α, f x ∈ s) : Infinite s := by
  rw [← range_subset_iff] at hf
  exact (infinite_range_of_injective hi).mono hf

theorem Finite.preimage {s : Set β} {f : α → β} (I : Set.InjOn f (f ⁻¹' s)) (h : Finite s) : Finite (f ⁻¹' s) :=
  finite_of_finite_image I (h.Subset (image_preimage_subset f s))

theorem Finite.preimage_embedding {s : Set β} (f : α ↪ β) (h : s.Finite) : (f ⁻¹' s).Finite :=
  Finite.preimage (fun _ _ _ _ h' => f.Injective h') h

theorem finite_option {s : Set (Option α)} : Finite s ↔ Finite { x : α | some x ∈ s } :=
  ⟨fun h => h.preimage_embedding Embedding.some, fun h =>
    ((h.Image some).insert none).Subset fun x =>
      Option.casesOn x (fun _ => Or.inl rfl) fun x hx => Or.inr <| mem_image_of_mem _ hx⟩

instance fintypeUnionₓ [DecidableEq α] [Fintype (Plift ι)] (f : ι → Set α) [∀ i, Fintype (f i)] : Fintype (⋃ i, f i) :=
  Fintype.ofFinset (Finset.univ.bUnion fun i : Plift ι => (f i.down).toFinset) <| by
    simp

theorem finite_Union [Fintype (Plift ι)] {f : ι → Set α} (H : ∀ i, Finite (f i)) : Finite (⋃ i, f i) :=
  ⟨@Set.fintypeUnionₓ _ _ (Classical.decEq α) _ _ fun i => Finite.fintype (H i)⟩

/-- A union of sets with `fintype` structure over a set with `fintype` structure has a `fintype`
structure. -/
def fintypeBUnion [DecidableEq α] {ι : Type _} {s : Set ι} [Fintype s] (f : ι → Set α)
    (H : ∀, ∀ i ∈ s, ∀, Fintype (f i)) : Fintype (⋃ i ∈ s, f i) := by
  rw [bUnion_eq_Union] <;>
    exact
      @Set.fintypeUnionₓ _ _ _ _ _
        (by
          rintro ⟨i, hi⟩ <;> exact H i hi)

instance fintypeBUnion' [DecidableEq α] {ι : Type _} {s : Set ι} [Fintype s] (f : ι → Set α) [H : ∀ i, Fintype (f i)] :
    Fintype (⋃ i ∈ s, f i) :=
  fintypeBUnion _ fun i _ => H i

theorem Finite.sUnion {s : Set (Set α)} (h : Finite s) (H : ∀, ∀ t ∈ s, ∀, Finite t) : Finite (⋃₀s) := by
  rw [sUnion_eq_Union] <;> have := finite.fintype h <;> apply finite_Union <;> simpa using H

theorem Finite.bUnion {α} {ι : Type _} {s : Set ι} {f : ∀, ∀ i ∈ s, ∀, Set α} :
    Finite s → (∀, ∀ i ∈ s, ∀, Finite (f i ‹_›)) → Finite (⋃ i ∈ s, f i ‹_›)
  | ⟨hs⟩, h => by
    rw [bUnion_eq_Union] <;> exact finite_Union fun i => h _ _

instance fintypeLtNat (n : ℕ) : Fintype { i | i < n } :=
  Fintype.ofFinset (Finset.range n) <| by
    simp

instance fintypeLeNat (n : ℕ) : Fintype { i | i ≤ n } := by
  simpa [Nat.lt_succ_iffₓ] using Set.fintypeLtNat (n + 1)

theorem finite_le_nat (n : ℕ) : Finite { i | i ≤ n } :=
  ⟨Set.fintypeLeNat _⟩

theorem finite_lt_nat (n : ℕ) : Finite { i | i < n } :=
  ⟨Set.fintypeLtNat _⟩

theorem Infinite.exists_nat_lt {s : Set ℕ} (hs : Infinite s) (n : ℕ) : ∃ m ∈ s, n < m :=
  let ⟨m, hm⟩ := (hs.diff <| Set.finite_le_nat n).Nonempty
  ⟨m, by
    simpa using hm⟩

instance fintypeProd (s : Set α) (t : Set β) [Fintype s] [Fintype t] : Fintype (s ×ˢ t : Set _) :=
  Fintype.ofFinset (s.toFinset.product t.toFinset) <| by
    simp

theorem Finite.prod {s : Set α} {t : Set β} : Finite s → Finite t → Finite (s ×ˢ t)
  | ⟨hs⟩, ⟨ht⟩ => ⟨Set.fintypeProd s t⟩

theorem finite_image_fst_and_snd_iff {s : Set (α × β)} : Finite (Prod.fst '' s) ∧ Finite (Prod.snd '' s) ↔ Finite s :=
  ⟨fun h => (h.1.Prod h.2).Subset fun x h => ⟨mem_image_of_mem _ h, mem_image_of_mem _ h⟩, fun h =>
    ⟨h.Image _, h.Image _⟩⟩

/-- `image2 f s t` is finitype if `s` and `t` are. -/
instance fintypeImage2 [DecidableEq γ] (f : α → β → γ) (s : Set α) (t : Set β) [hs : Fintype s] [ht : Fintype t] :
    Fintype (Image2 f s t : Set γ) := by
  rw [← image_prod]
  apply Set.fintypeImage

theorem Finite.image2 (f : α → β → γ) {s : Set α} {t : Set β} (hs : Finite s) (ht : Finite t) : Finite (Image2 f s t) :=
  by
  rw [← image_prod]
  exact (hs.prod ht).Image _

/-- If `s : set α` is a set with `fintype` instance and `f : α → set β` is a function such that
each `f a`, `a ∈ s`, has a `fintype` structure, then `s >>= f` has a `fintype` structure. -/
def fintypeBind {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β) (H : ∀, ∀ a ∈ s, ∀, Fintype (f a)) :
    Fintype (s >>= f) :=
  Set.fintypeBUnion _ H

instance fintypeBind' {α β} [DecidableEq β] (s : Set α) [Fintype s] (f : α → Set β) [H : ∀ a, Fintype (f a)] :
    Fintype (s >>= f) :=
  fintypeBind _ _ fun i _ => H i

theorem Finite.bind {α β} {s : Set α} {f : α → Set β} (h : Finite s) (hf : ∀, ∀ a ∈ s, ∀, Finite (f a)) :
    Finite (s >>= f) :=
  h.bUnion hf

instance fintypeSeq [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f] [Fintype s] : Fintype (f.seq s) := by
  rw [seq_def]
  apply Set.fintypeBUnion'

instance fintypeSeq' {α β : Type u} [DecidableEq β] (f : Set (α → β)) (s : Set α) [Fintype f] [Fintype s] :
    Fintype (f <*> s) :=
  Set.fintypeSeq f s

theorem Finite.seq {f : Set (α → β)} {s : Set α} (hf : Finite f) (hs : Finite s) : Finite (f.seq s) := by
  rw [seq_def]
  exact hf.bUnion fun f _ => hs.image _

theorem Finite.seq' {α β : Type u} {f : Set (α → β)} {s : Set α} (hf : Finite f) (hs : Finite s) : Finite (f <*> s) :=
  hf.seq hs

/-- There are finitely many subsets of a given finite set -/
theorem Finite.finite_subsets {α : Type u} {a : Set α} (h : Finite a) : Finite { b | b ⊆ a } :=
  ⟨(Fintype.ofFinset ((Finset.powerset h.toFinset).map Finset.coeEmb.1)) fun s => by
      simpa [← @exists_finite_iff_finset α fun t => t ⊆ a ∧ t = s, subset_to_finset_iff, ← And.assoc] using h.subset⟩

theorem exists_min_image [LinearOrderₓ β] (s : Set α) (f : α → β) (h1 : Finite s) :
    s.Nonempty → ∃ a ∈ s, ∀, ∀ b ∈ s, ∀, f a ≤ f b
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, finite.mem_to_finset] using h1.to_finset.exists_min_image f ⟨x, h1.mem_to_finset.2 hx⟩

theorem exists_max_image [LinearOrderₓ β] (s : Set α) (f : α → β) (h1 : Finite s) :
    s.Nonempty → ∃ a ∈ s, ∀, ∀ b ∈ s, ∀, f b ≤ f a
  | ⟨x, hx⟩ => by
    simpa only [exists_prop, finite.mem_to_finset] using h1.to_finset.exists_max_image f ⟨x, h1.mem_to_finset.2 hx⟩

theorem exists_lower_bound_image [hα : Nonempty α] [LinearOrderₓ β] (s : Set α) (f : α → β) (h : s.Finite) :
    ∃ a : α, ∀, ∀ b ∈ s, ∀, f a ≤ f b := by
  by_cases' hs : Set.Nonempty s
  · exact
      let ⟨x₀, H, hx₀⟩ := Set.exists_min_image s f h hs
      ⟨x₀, fun x hx => hx₀ x hx⟩
    
  · exact Nonempty.elimₓ hα fun a => ⟨a, fun x hx => absurd (Set.nonempty_of_mem hx) hs⟩
    

theorem exists_upper_bound_image [hα : Nonempty α] [LinearOrderₓ β] (s : Set α) (f : α → β) (h : s.Finite) :
    ∃ a : α, ∀, ∀ b ∈ s, ∀, f b ≤ f a := by
  by_cases' hs : Set.Nonempty s
  · exact
      let ⟨x₀, H, hx₀⟩ := Set.exists_max_image s f h hs
      ⟨x₀, fun x hx => hx₀ x hx⟩
    
  · exact Nonempty.elimₓ hα fun a => ⟨a, fun x hx => absurd (Set.nonempty_of_mem hx) hs⟩
    

end Set

namespace Finset

variable [DecidableEq β]

variable {s : Finset α}

theorem finite_to_set (s : Finset α) : Set.Finite (↑s : Set α) :=
  Set.finite_mem_finset s

@[simp]
theorem finite_to_set_to_finset {α : Type _} (s : Finset α) : (finite_to_set s).toFinset = s := by
  ext
  rw [Set.Finite.mem_to_finset, mem_coe]

end Finset

namespace Set

/-- Finite product of finite sets is finite -/
theorem Finite.pi {δ : Type _} [Fintype δ] {κ : δ → Type _} {t : ∀ d, Set (κ d)} (ht : ∀ d, (t d).Finite) :
    (Pi Univ t).Finite := by
  lift t to ∀ d, Finset (κ d) using ht
  classical
  rw [← Fintype.coe_pi_finset]
  exact (Fintype.piFinset t).finite_to_set

theorem forall_finite_image_eval_iff {δ : Type _} [Fintype δ] {κ : δ → Type _} {s : Set (∀ d, κ d)} :
    (∀ d, Finite (eval d '' s)) ↔ Finite s :=
  ⟨fun h => (Finite.pi h).Subset <| subset_pi_eval_image _ _, fun h d => h.Image _⟩

/-- A finite union of finsets is finite. -/
theorem union_finset_finite_of_range_finite (f : α → Finset β) (h : (Range f).Finite) : (⋃ a, (f a : Set β)).Finite :=
  by
  rw [← bUnion_range]
  exact h.bUnion fun y hy => y.finite_to_set

theorem finite_subset_Union {s : Set α} (hs : Finite s) {ι} {t : ι → Set α} (h : s ⊆ ⋃ i, t i) :
    ∃ I : Set ι, Finite I ∧ s ⊆ ⋃ i ∈ I, t i := by
  cases hs
  choose f hf using
    show ∀ x : s, ∃ i, x.1 ∈ t i by
      simpa [subset_def] using h
  refine' ⟨range f, finite_range f, fun x hx => _⟩
  rw [bUnion_range, mem_Union]
  exact ⟨⟨x, hx⟩, hf _⟩

theorem eq_finite_Union_of_finite_subset_Union {ι} {s : ι → Set α} {t : Set α} (tfin : Finite t) (h : t ⊆ ⋃ i, s i) :
    ∃ I : Set ι, Finite I ∧ ∃ σ : { i | i ∈ I } → Set α, (∀ i, Finite (σ i)) ∧ (∀ i, σ i ⊆ s i) ∧ t = ⋃ i, σ i :=
  let ⟨I, Ifin, hI⟩ := finite_subset_Union tfin h
  ⟨I, Ifin, fun x => s x ∩ t, fun i => tfin.Subset (inter_subset_right _ _), fun i => inter_subset_left _ _, by
    ext x
    rw [mem_Union]
    constructor
    · intro x_in
      rcases mem_Union.mp (hI x_in) with ⟨i, _, ⟨hi, rfl⟩, H⟩
      use i, hi, H, x_in
      
    · rintro ⟨i, hi, H⟩
      exact H
      ⟩

/-- An increasing union distributes over finite intersection. -/
theorem Union_Inter_of_monotone {ι ι' α : Type _} [Fintype ι] [LinearOrderₓ ι'] [Nonempty ι'] {s : ι → ι' → Set α}
    (hs : ∀ i, Monotone (s i)) : (⋃ j : ι', ⋂ i : ι, s i j) = ⋂ i : ι, ⋃ j : ι', s i j := by
  ext x
  refine' ⟨fun hx => Union_Inter_subset hx, fun hx => _⟩
  simp only [mem_Inter, mem_Union, mem_Inter] at hx⊢
  choose j hj using hx
  obtain ⟨j₀⟩ :=
    show Nonempty ι' by
      infer_instance
  refine' ⟨finset.univ.fold max j₀ j, fun i => hs i _ (hj i)⟩
  rw [Finset.fold_op_rel_iff_or (@le_max_iff _ _)]
  exact Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩

theorem Union_pi_of_monotone {ι ι' : Type _} [LinearOrderₓ ι'] [Nonempty ι'] {α : ι → Type _} {I : Set ι}
    {s : ∀ i, ι' → Set (α i)} (hI : Finite I) (hs : ∀, ∀ i ∈ I, ∀, Monotone (s i)) :
    (⋃ j : ι', I.pi fun i => s i j) = I.pi fun i => ⋃ j, s i j := by
  simp only [pi_def, bInter_eq_Inter, preimage_Union]
  have := hI.fintype
  exact Union_Inter_of_monotone fun i j₁ j₂ h => preimage_mono <| hs i i.2 h

theorem Union_univ_pi_of_monotone {ι ι' : Type _} [LinearOrderₓ ι'] [Nonempty ι'] [Fintype ι] {α : ι → Type _}
    {s : ∀ i, ι' → Set (α i)} (hs : ∀ i, Monotone (s i)) :
    (⋃ j : ι', Pi Univ fun i => s i j) = Pi Univ fun i => ⋃ j, s i j :=
  Union_pi_of_monotone (Finite.of_fintype _) fun i _ => hs i

instance Nat.fintypeIio (n : ℕ) : Fintype (Iio n) :=
  Fintype.ofFinset (Finset.range n) <| by
    simp

/-- If `P` is some relation between terms of `γ` and sets in `γ`,
such that every finite set `t : set γ` has some `c : γ` related to it,
then there is a recursively defined sequence `u` in `γ`
so `u n` is related to the image of `{0, 1, ..., n-1}` under `u`.

(We use this later to show sequentially compact sets
are totally bounded.)
-/
theorem seq_of_forall_finite_exists {γ : Type _} {P : γ → Set γ → Prop} (h : ∀ t, Finite t → ∃ c, P c t) :
    ∃ u : ℕ → γ, ∀ n, P (u n) (u '' Iio n) :=
  ⟨fun n =>
    (@Nat.strongRecOn' (fun _ => γ) n) fun n ih =>
      Classical.some <| h (range fun m : Iio n => ih m.1 m.2) (finite_range _),
    fun n => by
    classical
    refine' Nat.strongRecOn' n fun n ih => _
    rw [Nat.strong_rec_on_beta']
    convert Classical.some_spec (h _ _)
    ext x
    constructor
    · rintro ⟨m, hmn, rfl⟩
      exact ⟨⟨m, hmn⟩, rfl⟩
      
    · rintro ⟨⟨m, hmn⟩, rfl⟩
      exact ⟨m, hmn, rfl⟩
      ⟩

theorem finite_range_ite {p : α → Prop} [DecidablePred p] {f g : α → β} (hf : Finite (Range f))
    (hg : Finite (Range g)) : Finite (Range fun x => if p x then f x else g x) :=
  (hf.union hg).Subset range_ite_subset

theorem finite_range_const {c : β} : Finite (Range fun x : α => c) :=
  (finite_singleton c).Subset range_const_subset

theorem range_find_greatest_subset {P : α → ℕ → Prop} [∀ x, DecidablePred (P x)] {b : ℕ} :
    (Range fun x => Nat.findGreatest (P x) b) ⊆ ↑(Finset.range (b + 1)) := by
  rw [range_subset_iff]
  intro x
  simp [Nat.lt_succ_iffₓ, Nat.find_greatest_le]

theorem finite_range_find_greatest {P : α → ℕ → Prop} [∀ x, DecidablePred (P x)] {b : ℕ} :
    Finite (Range fun x => Nat.findGreatest (P x) b) :=
  (Finset.range (b + 1)).finite_to_set.Subset range_find_greatest_subset

theorem card_lt_card {s t : Set α} [Fintype s] [Fintype t] (h : s ⊂ t) : Fintype.card s < Fintype.card t :=
  (Fintype.card_lt_of_injective_not_surjective (Set.inclusion h.1) (Set.inclusion_injective h.1)) fun hst =>
    (ssubset_iff_subset_ne.1 h).2 (eq_of_inclusion_surjective hst)

theorem card_le_of_subset {s t : Set α} [Fintype s] [Fintype t] (hsub : s ⊆ t) : Fintype.card s ≤ Fintype.card t :=
  Fintype.card_le_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)

theorem eq_of_subset_of_card_le {s t : Set α} [Fintype s] [Fintype t] (hsub : s ⊆ t)
    (hcard : Fintype.card t ≤ Fintype.card s) : s = t :=
  (eq_or_ssubset_of_subset hsub).elim id fun h => absurd hcard <| not_le_of_lt <| card_lt_card h

theorem subset_iff_to_finset_subset (s t : Set α) [Fintype s] [Fintype t] : s ⊆ t ↔ s.toFinset ⊆ t.toFinset := by
  simp

@[simp, mono]
theorem Finite.to_finset_mono {s t : Set α} {hs : Finite s} {ht : Finite t} : hs.toFinset ⊆ ht.toFinset ↔ s ⊆ t := by
  constructor
  · intro h x
    rw [← finite.mem_to_finset hs, ← finite.mem_to_finset ht]
    exact fun hx => h hx
    
  · intro h x
    rw [finite.mem_to_finset hs, finite.mem_to_finset ht]
    exact fun hx => h hx
    

@[simp, mono]
theorem Finite.to_finset_strict_mono {s t : Set α} {hs : Finite s} {ht : Finite t} :
    hs.toFinset ⊂ ht.toFinset ↔ s ⊂ t := by
  rw [← lt_eq_ssubset, ← Finset.lt_iff_ssubset, lt_iff_le_and_ne, lt_iff_le_and_ne]
  simp

theorem card_range_of_injective [Fintype α] {f : α → β} (hf : Injective f) [Fintype (Range f)] :
    Fintype.card (Range f) = Fintype.card α :=
  Eq.symm <| Fintype.card_congr <| Equivₓ.ofInjective f hf

theorem Finite.exists_maximal_wrt [PartialOrderₓ β] (f : α → β) (s : Set α) (h : Set.Finite s) :
    s.Nonempty → ∃ a ∈ s, ∀, ∀ a' ∈ s, ∀, f a ≤ f a' → f a = f a' := by
  classical
  refine' h.induction_on _ _
  · exact fun h => absurd h empty_not_nonempty
    
  intro a s his _ ih _
  cases' s.eq_empty_or_nonempty with h h
  · use a
    simp [h]
    
  rcases ih h with ⟨b, hb, ih⟩
  by_cases' f b ≤ f a
  · refine' ⟨a, Set.mem_insert _ _, fun c hc hac => le_antisymmₓ hac _⟩
    rcases Set.mem_insert_iff.1 hc with (rfl | hcs)
    · rfl
      
    · rwa [← ih c hcs (le_transₓ h hac)]
      
    
  · refine' ⟨b, Set.mem_insert_of_mem _ hb, fun c hc hbc => _⟩
    rcases Set.mem_insert_iff.1 hc with (rfl | hcs)
    · exact (h hbc).elim
      
    · exact ih c hcs hbc
      
    

theorem Finite.card_to_finset {s : Set α} [Fintype s] (h : s.Finite) : h.toFinset.card = Fintype.card s := by
  rw [← Finset.card_attach, Finset.attach_eq_univ, ← Fintype.card]
  refine' Fintype.card_congr (Equivₓ.setCongr _)
  ext x
  show x ∈ h.to_finset ↔ x ∈ s
  simp

theorem Infinite.exists_not_mem_finset {s : Set α} (hs : s.Infinite) (f : Finset α) : ∃ a ∈ s, a ∉ f :=
  let ⟨a, has, haf⟩ := (hs.diff f.finite_to_set).Nonempty
  ⟨a, has, fun h => haf <| Finset.mem_coe.1 h⟩

section DecidableEq

theorem to_finset_inter {α : Type _} [DecidableEq α] (s t : Set α) [Fintype (s ∩ t : Set α)] [Fintype s] [Fintype t] :
    (s ∩ t).toFinset = s.toFinset ∩ t.toFinset := by
  ext <;> simp

theorem to_finset_union {α : Type _} [DecidableEq α] (s t : Set α) [Fintype (s ∪ t : Set α)] [Fintype s] [Fintype t] :
    (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := by
  ext <;> simp

instance fintypeSdiff {α : Type _} [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s \ t : Set α) :=
  Fintype.ofFinset (s.toFinset \ t.toFinset) <| by
    simp

theorem to_finset_sdiff {α : Type _} [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] [Fintype (s \ t : Set α)] :
    (s \ t).toFinset = s.toFinset \ t.toFinset := by
  ext <;> simp

theorem to_finset_ne_eq_erase {α : Type _} [DecidableEq α] [Fintype α] (a : α) [Fintype { x : α | x ≠ a }] :
    { x : α | x ≠ a }.toFinset = Finset.univ.erase a := by
  ext <;> simp

theorem card_ne_eq [Fintype α] (a : α) [Fintype { x : α | x ≠ a }] :
    Fintype.card { x : α | x ≠ a } = Fintype.card α - 1 := by
  have := Classical.decEq α
  rw [← to_finset_card, to_finset_ne_eq_erase, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

end DecidableEq

section

variable [SemilatticeSup α] [Nonempty α] {s : Set α}

/-- A finite set is bounded above.-/
protected theorem Finite.bdd_above (hs : Finite s) : BddAbove s :=
  (Finite.induction_on hs bdd_above_empty) fun a s _ _ h => h.insert a

/-- A finite union of sets which are all bounded above is still bounded above.-/
theorem Finite.bdd_above_bUnion {I : Set β} {S : β → Set α} (H : Finite I) :
    BddAbove (⋃ i ∈ I, S i) ↔ ∀, ∀ i ∈ I, ∀, BddAbove (S i) :=
  Finite.induction_on H
    (by
      simp only [bUnion_empty, bdd_above_empty, ball_empty_iff])
    fun a s ha _ hs => by
    simp only [bUnion_insert, ball_insert_iff, bdd_above_union, hs]

theorem infinite_of_not_bdd_above : ¬BddAbove s → s.Infinite := by
  contrapose!
  rw [not_infinite]
  apply finite.bdd_above

end

section

variable [SemilatticeInf α] [Nonempty α] {s : Set α}

/-- A finite set is bounded below.-/
protected theorem Finite.bdd_below (hs : Finite s) : BddBelow s :=
  @Finite.bdd_above αᵒᵈ _ _ _ hs

/-- A finite union of sets which are all bounded below is still bounded below.-/
theorem Finite.bdd_below_bUnion {I : Set β} {S : β → Set α} (H : Finite I) :
    BddBelow (⋃ i ∈ I, S i) ↔ ∀, ∀ i ∈ I, ∀, BddBelow (S i) :=
  @Finite.bdd_above_bUnion αᵒᵈ _ _ _ _ _ H

theorem infinite_of_not_bdd_below : ¬BddBelow s → s.Infinite := by
  contrapose!
  rw [not_infinite]
  apply finite.bdd_below

end

end Set

namespace Finset

/-- A finset is bounded above. -/
protected theorem bdd_above [SemilatticeSup α] [Nonempty α] (s : Finset α) : BddAbove (↑s : Set α) :=
  s.finite_to_set.BddAbove

/-- A finset is bounded below. -/
protected theorem bdd_below [SemilatticeInf α] [Nonempty α] (s : Finset α) : BddBelow (↑s : Set α) :=
  s.finite_to_set.BddBelow

end Finset

namespace Fintype

variable [Fintype α] {p q : α → Prop} [DecidablePred p] [DecidablePred q]

@[simp]
theorem card_subtype_compl : Fintype.card { x // ¬p x } = Fintype.card α - Fintype.card { x // p x } := by
  classical
  rw [Fintype.card_of_subtype (Set.toFinset (pᶜ)), Set.to_finset_compl p, Finset.card_compl,
      Fintype.card_of_subtype (Set.toFinset p)] <;>
    intros <;> simp <;> rfl

/-- If two subtypes of a fintype have equal cardinality, so do their complements. -/
theorem card_compl_eq_card_compl (h : Fintype.card { x // p x } = Fintype.card { x // q x }) :
    Fintype.card { x // ¬p x } = Fintype.card { x // ¬q x } := by
  simp only [card_subtype_compl, h]

end Fintype

/-- If a set `s` does not contain any elements between any pair of elements `x, z ∈ s` with `x ≤ z`
(i.e if given `x, y, z ∈ s` such that `x ≤ y ≤ z`, then `y` is either `x` or `z`), then `s` is
finite.
-/
theorem Set.finite_of_forall_between_eq_endpoints {α : Type _} [LinearOrderₓ α] (s : Set α)
    (h : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, ∀ z ∈ s, ∀, x ≤ y → y ≤ z → x = y ∨ y = z) : Set.Finite s := by
  by_contra hinf
  change s.infinite at hinf
  rcases hinf.exists_subset_card_eq 3 with ⟨t, hts, ht⟩
  let f := t.order_iso_of_fin ht
  let x := f 0
  let y := f 1
  let z := f 2
  have :=
    h x (hts x.2) y (hts y.2) z (hts z.2)
      (f.monotone <| by
        decide)
      (f.monotone <| by
        decide)
  have key₁ : (0 : Finₓ 3) ≠ 1 := by
    decide
  have key₂ : (1 : Finₓ 3) ≠ 2 := by
    decide
  cases this
  · dsimp' only [x, y]  at this
    exact key₁ (f.injective <| Subtype.coe_injective this)
    
  · dsimp' only [y, z]  at this
    exact key₂ (f.injective <| Subtype.coe_injective this)
    

