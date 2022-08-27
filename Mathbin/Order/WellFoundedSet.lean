/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Order.Antichain
import Mathbin.Order.OrderIsoNat
import Mathbin.Order.WellFounded

/-!
# Well-founded sets

A well-founded subset of an ordered type is one on which the relation `<` is well-founded.

## Main Definitions
 * `set.well_founded_on s r` indicates that the relation `r` is
  well-founded when restricted to the set `s`.
 * `set.is_wf s` indicates that `<` is well-founded when restricted to `s`.
 * `set.partially_well_ordered_on s r` indicates that the relation `r` is
  partially well-ordered (also known as well quasi-ordered) when restricted to the set `s`.
 * `set.is_pwo s` indicates that any infinite sequence of elements in `s` contains an infinite
  monotone subsequence. Note that this is equivalent to containing only two comparable elements.

## Main Results
 * Higman's Lemma, `set.partially_well_ordered_on.partially_well_ordered_on_sublist_forall₂`,
  shows that if `r` is partially well-ordered on `s`, then `list.sublist_forall₂` is partially
  well-ordered on the set of lists of elements of `s`. The result was originally published by
  Higman, but this proof more closely follows Nash-Williams.
 * `set.well_founded_on_iff` relates `well_founded_on` to the well-foundedness of a relation on the
 original type, to avoid dealing with subtypes.
 * `set.is_wf.mono` shows that a subset of a well-founded subset is well-founded.
 * `set.is_wf.union` shows that the union of two well-founded subsets is well-founded.
 * `finset.is_wf` shows that all `finset`s are well-founded.

## TODO

Prove that `s` is partial well ordered iff it has no infinite descending chain or antichain.

## References
 * [Higman, *Ordering by Divisibility in Abstract Algebras*][Higman52]
 * [Nash-Williams, *On Well-Quasi-Ordering Finite Trees*][Nash-Williams63]
-/


variable {ι α β : Type _}

namespace Set

/-! ### Relations well-founded on sets -/


/-- `s.well_founded_on r` indicates that the relation `r` is well-founded when restricted to `s`. -/
def WellFoundedOn (s : Set α) (r : α → α → Prop) : Prop :=
  WellFounded fun a b : s => r a b

@[simp]
theorem well_founded_on_empty (r : α → α → Prop) : WellFoundedOn ∅ r :=
  well_founded_of_empty _

section WellFoundedOn

variable {r r' : α → α → Prop}

section AnyRel

variable {s t : Set α} {x y : α}

theorem well_founded_on_iff : s.WellFoundedOn r ↔ WellFounded fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s := by
  have f : RelEmbedding (fun (a : s) (b : s) => r a b) fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s :=
    ⟨⟨coe, Subtype.coe_injective⟩, fun a b => by
      simp ⟩
  refine' ⟨fun h => _, f.well_founded⟩
  rw [WellFounded.well_founded_iff_has_min]
  intro t ht
  by_cases' hst : (s ∩ t).Nonempty
  · rw [← Subtype.preimage_coe_nonempty] at hst
    rcases h.has_min (coe ⁻¹' t) hst with ⟨⟨m, ms⟩, mt, hm⟩
    exact ⟨m, mt, fun x xt ⟨xm, xs, ms⟩ => hm ⟨x, xs⟩ xt xm⟩
    
  · rcases ht with ⟨m, mt⟩
    exact ⟨m, mt, fun x xt ⟨xm, xs, ms⟩ => hst ⟨m, ⟨ms, mt⟩⟩⟩
    

namespace WellFoundedOn

protected theorem induction (hs : s.WellFoundedOn r) (hx : x ∈ s) {P : α → Prop}
    (hP : ∀ y ∈ s, (∀ z ∈ s, r z y → P z) → P y) : P x := by
  let Q : s → Prop := fun y => P y
  change Q ⟨x, hx⟩
  refine' WellFounded.induction hs ⟨x, hx⟩ _
  simpa only [Subtype.forall]

protected theorem mono (h : t.WellFoundedOn r') (hle : r ≤ r') (hst : s ⊆ t) : s.WellFoundedOn r := by
  rw [well_founded_on_iff] at *
  refine' Subrelation.wfₓ (fun x y xy => _) h
  exact ⟨hle _ _ xy.1, hst xy.2.1, hst xy.2.2⟩

theorem subset (h : t.WellFoundedOn r) (hst : s ⊆ t) : s.WellFoundedOn r :=
  h.mono le_rflₓ hst

end WellFoundedOn

end AnyRel

section IsStrictOrder

variable [IsStrictOrder α r] {s t : Set α}

instance IsStrictOrder.subset : IsStrictOrder α fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s where
  to_is_irrefl := ⟨fun a con => irrefl_of r a con.1⟩
  to_is_trans := ⟨fun a b c ab bc => ⟨trans_of r ab.1 bc.1, ab.2.1, bc.2.2⟩⟩

theorem well_founded_on_iff_no_descending_seq :
    s.WellFoundedOn r ↔ ∀ f : ((· > ·) : ℕ → ℕ → Prop) ↪r r, ¬∀ n, f n ∈ s := by
  simp only [well_founded_on_iff, RelEmbedding.well_founded_iff_no_descending_seq, ← not_exists, ← not_nonempty_iff,
    not_iff_not]
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    have H : ∀ n, f n ∈ s := fun n => (hf.2 n.lt_succ_self).2.2
    refine' ⟨⟨f, _⟩, H⟩
    simpa only [H, and_trueₓ] using @hf
    
  · rintro ⟨⟨f, hf⟩, hfs : ∀ n, f n ∈ s⟩
    refine' ⟨⟨f, _⟩⟩
    simpa only [hfs, and_trueₓ] using @hf
    

theorem WellFoundedOn.union (hs : s.WellFoundedOn r) (ht : t.WellFoundedOn r) : (s ∪ t).WellFoundedOn r := by
  rw [well_founded_on_iff_no_descending_seq] at *
  rintro f hf
  rcases Nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hg | hg⟩
  exacts[hs (g.dual.lt_embedding.trans f) hg, ht (g.dual.lt_embedding.trans f) hg]

@[simp]
theorem well_founded_on_union : (s ∪ t).WellFoundedOn r ↔ s.WellFoundedOn r ∧ t.WellFoundedOn r :=
  ⟨fun h => ⟨h.Subset <| subset_union_left _ _, h.Subset <| subset_union_right _ _⟩, fun h => h.1.union h.2⟩

end IsStrictOrder

end WellFoundedOn

/-! ### Sets well-founded w.r.t. the strict inequality -/


section LT

variable [LT α] {s t : Set α}

/-- `s.is_wf` indicates that `<` is well-founded when restricted to `s`. -/
def IsWf (s : Set α) : Prop :=
  WellFoundedOn s (· < ·)

@[simp]
theorem is_wf_empty : IsWf (∅ : Set α) :=
  well_founded_of_empty _

theorem is_wf_univ_iff : IsWf (Univ : Set α) ↔ WellFounded ((· < ·) : α → α → Prop) := by
  simp [is_wf, well_founded_on_iff]

theorem IsWf.mono (h : IsWf t) (st : s ⊆ t) : IsWf s :=
  h.Subset st

end LT

section Preorderₓ

variable [Preorderₓ α] {s t : Set α} {a : α}

protected theorem IsWf.union (hs : IsWf s) (ht : IsWf t) : IsWf (s ∪ t) :=
  hs.union ht

@[simp]
theorem is_wf_union : IsWf (s ∪ t) ↔ IsWf s ∧ IsWf t :=
  well_founded_on_union

end Preorderₓ

section Preorderₓ

variable [Preorderₓ α] {s t : Set α} {a : α}

theorem is_wf_iff_no_descending_seq : IsWf s ↔ ∀ f : ℕ → α, StrictAnti f → ¬∀ n, f (OrderDual.toDual n) ∈ s :=
  well_founded_on_iff_no_descending_seq.trans
    ⟨fun H f hf => H ⟨⟨f, hf.Injective⟩, fun a b => hf.lt_iff_lt⟩, fun H f => H f fun _ _ => f.map_rel_iff.2⟩

end Preorderₓ

/-!
### Partially well-ordered sets

A set is partially well-ordered by a relation `r` when any infinite sequence contains two elements
where the first is related to the second by `r`. Equivalently, any antichain (see `is_antichain`) is
finite, see `set.partially_well_ordered_on_iff_finite_antichains`.
-/


/-- A subset is partially well-ordered by a relation `r` when any infinite sequence contains
  two elements where the first is related to the second by `r`. -/
def PartiallyWellOrderedOn (s : Set α) (r : α → α → Prop) : Prop :=
  ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ m n : ℕ, m < n ∧ r (f m) (f n)

section PartiallyWellOrderedOn

variable {r : α → α → Prop} {r' : β → β → Prop} {f : α → β} {s : Set α} {t : Set α} {a : α}

theorem PartiallyWellOrderedOn.mono (ht : t.PartiallyWellOrderedOn r) (h : s ⊆ t) : s.PartiallyWellOrderedOn r :=
  fun f hf => (ht f) fun n => h <| hf n

@[simp]
theorem partially_well_ordered_on_empty (r : α → α → Prop) : PartiallyWellOrderedOn ∅ r := fun f hf => (hf 0).elim

theorem PartiallyWellOrderedOn.union (hs : s.PartiallyWellOrderedOn r) (ht : t.PartiallyWellOrderedOn r) :
    (s ∪ t).PartiallyWellOrderedOn r := by
  rintro f hf
  rcases Nat.exists_subseq_of_forall_mem_union f hf with ⟨g, hgs | hgt⟩
  · rcases hs _ hgs with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strict_mono hlt, hr⟩
    
  · rcases ht _ hgt with ⟨m, n, hlt, hr⟩
    exact ⟨g m, g n, g.strict_mono hlt, hr⟩
    

@[simp]
theorem partially_well_ordered_on_union :
    (s ∪ t).PartiallyWellOrderedOn r ↔ s.PartiallyWellOrderedOn r ∧ t.PartiallyWellOrderedOn r :=
  ⟨fun h => ⟨h.mono <| subset_union_left _ _, h.mono <| subset_union_right _ _⟩, fun h => h.1.union h.2⟩

theorem PartiallyWellOrderedOn.image_of_monotone_on (hs : s.PartiallyWellOrderedOn r)
    (hf : ∀ a₁ ∈ s, ∀ a₂ ∈ s, r a₁ a₂ → r' (f a₁) (f a₂)) : (f '' s).PartiallyWellOrderedOn r' := by
  intro g' hg'
  choose g hgs heq using hg'
  obtain rfl : f ∘ g = g'
  exact funext HEq
  obtain ⟨m, n, hlt, hmn⟩ := hs g hgs
  exact ⟨m, n, hlt, hf _ (hgs m) _ (hgs n) hmn⟩

theorem _root_.is_antichain.finite_of_partially_well_ordered_on (ha : IsAntichain r s)
    (hp : s.PartiallyWellOrderedOn r) : s.Finite := by
  refine' finite_or_infinite.resolve_right fun hi => _
  obtain ⟨m, n, hmn, h⟩ := hp (fun n => hi.nat_embedding _ n) fun n => (hi.nat_embedding _ n).2
  exact
    hmn.ne
      ((hi.nat_embedding _).Injective <|
        Subtype.val_injective <| ha.eq (hi.nat_embedding _ m).2 (hi.nat_embedding _ n).2 h)

section IsRefl

variable [IsRefl α r]

protected theorem Finite.partially_well_ordered_on (hs : s.Finite) : s.PartiallyWellOrderedOn r := by
  intro f hf
  obtain ⟨m, n, hmn, h⟩ := hs.exists_lt_map_eq_of_forall_mem hf
  exact ⟨m, n, hmn, h.subst <| refl (f m)⟩

theorem _root_.is_antichain.partially_well_ordered_on_iff (hs : IsAntichain r s) :
    s.PartiallyWellOrderedOn r ↔ s.Finite :=
  ⟨hs.finite_of_partially_well_ordered_on, Finite.partially_well_ordered_on⟩

@[simp]
theorem partially_well_ordered_on_singleton (a : α) : PartiallyWellOrderedOn {a} r :=
  (finite_singleton a).PartiallyWellOrderedOn

@[simp]
theorem partially_well_ordered_on_insert : PartiallyWellOrderedOn (insert a s) r ↔ PartiallyWellOrderedOn s r := by
  simp only [← singleton_union, partially_well_ordered_on_union, partially_well_ordered_on_singleton, true_andₓ]

protected theorem PartiallyWellOrderedOn.insert (h : PartiallyWellOrderedOn s r) (a : α) :
    PartiallyWellOrderedOn (insert a s) r :=
  partially_well_ordered_on_insert.2 h

-- ./././Mathport/Syntax/Translate/Basic.lean:556:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem partially_well_ordered_on_iff_finite_antichains [IsSymm α r] :
    s.PartiallyWellOrderedOn r ↔ ∀ (t) (_ : t ⊆ s), IsAntichain r t → t.Finite := by
  refine' ⟨fun h t ht hrt => hrt.finite_of_partially_well_ordered_on (h.mono ht), _⟩
  rintro hs f hf
  by_contra' H
  refine' infinite_range_of_injective (fun m n hmn => _) (hs _ (range_subset_iff.2 hf) _)
  · obtain h | h | h := lt_trichotomyₓ m n
    · refine' (H _ _ h _).elim
      rw [hmn]
      exact refl _
      
    · exact h
      
    · refine' (H _ _ h _).elim
      rw [hmn]
      exact refl _
      
    
  rintro _ ⟨m, hm, rfl⟩ _ ⟨n, hn, rfl⟩ hmn
  obtain h | h := (ne_of_apply_ne _ hmn).lt_or_lt
  · exact H _ _ h
    
  · exact mt symm (H _ _ h)
    

variable [IsTrans α r]

theorem PartiallyWellOrderedOn.exists_monotone_subseq (h : s.PartiallyWellOrderedOn r) (f : ℕ → α) (hf : ∀ n, f n ∈ s) :
    ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) := by
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq r f
  · refine' ⟨g, fun m n hle => _⟩
    obtain hlt | rfl := hle.lt_or_eq
    exacts[h1 m n hlt, refl_of r _]
    
  · exfalso
    obtain ⟨m, n, hlt, hle⟩ := h (f ∘ g) fun n => hf _
    exact h2 m n hlt hle
    

theorem partially_well_ordered_on_iff_exists_monotone_subseq :
    s.PartiallyWellOrderedOn r ↔ ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) :=
  by
  classical
  constructor <;> intro h f hf
  · exact h.exists_monotone_subseq f hf
    
  · obtain ⟨g, gmon⟩ := h f hf
    exact ⟨g 0, g 1, g.lt_iff_lt.2 zero_lt_one, gmon _ _ zero_le_one⟩
    

protected theorem PartiallyWellOrderedOn.prod {t : Set β} (hs : PartiallyWellOrderedOn s r)
    (ht : PartiallyWellOrderedOn t r') : PartiallyWellOrderedOn (s ×ˢ t) fun x y : α × β => r x.1 y.1 ∧ r' x.2 y.2 := by
  intro f hf
  obtain ⟨g₁, h₁⟩ := hs.exists_monotone_subseq (Prod.fst ∘ f) fun n => (hf n).1
  obtain ⟨m, n, hlt, hle⟩ := ht (Prod.snd ∘ f ∘ g₁) fun n => (hf _).2
  exact ⟨g₁ m, g₁ n, g₁.strict_mono hlt, h₁ _ _ hlt.le, hle⟩

end IsRefl

theorem PartiallyWellOrderedOn.well_founded_on [IsPreorder α r] (h : s.PartiallyWellOrderedOn r) :
    s.WellFoundedOn fun a b => r a b ∧ ¬r b a := by
  letI : Preorderₓ α := { le := r, le_refl := refl_of r, le_trans := fun _ _ _ => trans_of r }
  change s.well_founded_on (· < ·)
  change s.partially_well_ordered_on (· ≤ ·) at h
  rw [well_founded_on_iff_no_descending_seq]
  intro f hf
  obtain ⟨m, n, hlt, hle⟩ := h f hf
  exact (f.map_rel_iff.2 hlt).not_le hle

end PartiallyWellOrderedOn

section IsPwo

variable [Preorderₓ α] [Preorderₓ β] {s t : Set α}

/-- A subset of a preorder is partially well-ordered when any infinite sequence contains
  a monotone subsequence of length 2 (or equivalently, an infinite monotone subsequence). -/
def IsPwo (s : Set α) : Prop :=
  PartiallyWellOrderedOn s (· ≤ ·)

theorem IsPwo.mono (ht : t.IsPwo) : s ⊆ t → s.IsPwo :=
  ht.mono

theorem IsPwo.exists_monotone_subseq (h : s.IsPwo) (f : ℕ → α) (hf : ∀ n, f n ∈ s) : ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  h.exists_monotone_subseq f hf

theorem is_pwo_iff_exists_monotone_subseq : s.IsPwo ↔ ∀ f : ℕ → α, (∀ n, f n ∈ s) → ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  partially_well_ordered_on_iff_exists_monotone_subseq

protected theorem IsPwo.is_wf (h : s.IsPwo) : s.IsWf := by
  simpa only [← lt_iff_le_not_leₓ] using h.well_founded_on

theorem IsPwo.prod {t : Set β} (hs : s.IsPwo) (ht : t.IsPwo) : IsPwo (s ×ˢ t) :=
  hs.Prod ht

theorem IsPwo.image_of_monotone_on (hs : s.IsPwo) {f : α → β} (hf : MonotoneOn f s) : IsPwo (f '' s) :=
  hs.image_of_monotone_on hf

theorem IsPwo.image_of_monotone (hs : s.IsPwo) {f : α → β} (hf : Monotone f) : IsPwo (f '' s) :=
  hs.image_of_monotone_on (hf.MonotoneOn _)

protected theorem IsPwo.union (hs : IsPwo s) (ht : IsPwo t) : IsPwo (s ∪ t) :=
  hs.union ht

@[simp]
theorem is_pwo_union : IsPwo (s ∪ t) ↔ IsPwo s ∧ IsPwo t :=
  partially_well_ordered_on_union

protected theorem Finite.is_pwo (hs : s.Finite) : IsPwo s :=
  hs.PartiallyWellOrderedOn

@[simp]
theorem is_pwo_of_finite [Finite α] : s.IsPwo :=
  s.to_finite.IsPwo

@[simp]
theorem is_pwo_singleton (a : α) : IsPwo ({a} : Set α) :=
  (finite_singleton a).IsPwo

@[simp]
theorem is_pwo_empty : IsPwo (∅ : Set α) :=
  finite_empty.IsPwo

protected theorem Subsingleton.is_pwo (hs : s.Subsingleton) : IsPwo s :=
  hs.Finite.IsPwo

@[simp]
theorem is_pwo_insert {a} : IsPwo (insert a s) ↔ IsPwo s := by
  simp only [← singleton_union, is_pwo_union, is_pwo_singleton, true_andₓ]

protected theorem IsPwo.insert (h : IsPwo s) (a : α) : IsPwo (insert a s) :=
  is_pwo_insert.2 h

protected theorem Finite.is_wf (hs : s.Finite) : IsWf s :=
  hs.IsPwo.IsWf

@[simp]
theorem is_wf_singleton {a : α} : IsWf ({a} : Set α) :=
  (finite_singleton a).IsWf

protected theorem Subsingleton.is_wf (hs : s.Subsingleton) : IsWf s :=
  hs.IsPwo.IsWf

@[simp]
theorem is_wf_insert {a} : IsWf (insert a s) ↔ IsWf s := by
  simp only [← singleton_union, is_wf_union, is_wf_singleton, true_andₓ]

theorem IsWf.insert (h : IsWf s) (a : α) : IsWf (insert a s) :=
  is_wf_insert.2 h

end IsPwo

section WellFoundedOn

variable {r : α → α → Prop} [IsStrictOrder α r] {s : Set α} {a : α}

protected theorem Finite.well_founded_on (hs : s.Finite) : s.WellFoundedOn r := by
  letI := partialOrderOfSO r
  exact hs.is_wf

@[simp]
theorem well_founded_on_singleton : WellFoundedOn ({a} : Set α) r :=
  (finite_singleton a).WellFoundedOn

protected theorem Subsingleton.well_founded_on (hs : s.Subsingleton) : s.WellFoundedOn r :=
  hs.Finite.WellFoundedOn

@[simp]
theorem well_founded_on_insert : WellFoundedOn (insert a s) r ↔ WellFoundedOn s r := by
  simp only [← singleton_union, well_founded_on_union, well_founded_on_singleton, true_andₓ]

theorem WellFoundedOn.insert (h : WellFoundedOn s r) (a : α) : WellFoundedOn (insert a s) r :=
  well_founded_on_insert.2 h

end WellFoundedOn

section LinearOrderₓ

variable [LinearOrderₓ α] {s : Set α}

protected theorem IsWf.is_pwo (hs : s.IsWf) : s.IsPwo := by
  intro f hf
  lift f to ℕ → s using hf
  have hrange : (range f).Nonempty := range_nonempty _
  rcases hs.has_min (range f) (range_nonempty _) with ⟨_, ⟨m, rfl⟩, hm⟩
  simp only [forall_range_iff, not_ltₓ] at hm
  exact ⟨m, m + 1, lt_add_one m, hm _⟩

/-- In a linear order, the predicates `set.is_wf` and `set.is_pwo` are equivalent. -/
theorem is_wf_iff_is_pwo : s.IsWf ↔ s.IsPwo :=
  ⟨IsWf.is_pwo, IsPwo.is_wf⟩

end LinearOrderₓ

end Set

namespace Finset

variable {r : α → α → Prop}

@[simp]
protected theorem partially_well_ordered_on [IsRefl α r] (s : Finset α) : (s : Set α).PartiallyWellOrderedOn r :=
  s.finite_to_set.PartiallyWellOrderedOn

@[simp]
protected theorem is_pwo [Preorderₓ α] (s : Finset α) : Set.IsPwo (↑s : Set α) :=
  s.PartiallyWellOrderedOn

@[simp]
protected theorem is_wf [Preorderₓ α] (s : Finset α) : Set.IsWf (↑s : Set α) :=
  s.finite_to_set.IsWf

@[simp]
protected theorem well_founded_on [IsStrictOrder α r] (s : Finset α) : Set.WellFoundedOn (↑s : Set α) r := by
  letI := partialOrderOfSO r
  exact s.is_wf

theorem well_founded_on_sup [IsStrictOrder α r] (s : Finset ι) {f : ι → Set α} :
    (s.sup f).WellFoundedOn r ↔ ∀ i ∈ s, (f i).WellFoundedOn r :=
  (Finset.cons_induction_on s
      (by
        simp ))
    fun a s ha hs => by
    simp [-sup_set_eq_bUnion, hs]

theorem partially_well_ordered_on_sup (s : Finset ι) {f : ι → Set α} :
    (s.sup f).PartiallyWellOrderedOn r ↔ ∀ i ∈ s, (f i).PartiallyWellOrderedOn r :=
  (Finset.cons_induction_on s
      (by
        simp ))
    fun a s ha hs => by
    simp [-sup_set_eq_bUnion, hs]

theorem is_wf_sup [Preorderₓ α] (s : Finset ι) {f : ι → Set α} : (s.sup f).IsWf ↔ ∀ i ∈ s, (f i).IsWf :=
  s.well_founded_on_sup

theorem is_pwo_sup [Preorderₓ α] (s : Finset ι) {f : ι → Set α} : (s.sup f).IsPwo ↔ ∀ i ∈ s, (f i).IsPwo :=
  s.partially_well_ordered_on_sup

@[simp]
theorem well_founded_on_bUnion [IsStrictOrder α r] (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).WellFoundedOn r ↔ ∀ i ∈ s, (f i).WellFoundedOn r := by
  simpa only [Finset.sup_eq_supr] using s.well_founded_on_sup

@[simp]
theorem partially_well_ordered_on_bUnion (s : Finset ι) {f : ι → Set α} :
    (⋃ i ∈ s, f i).PartiallyWellOrderedOn r ↔ ∀ i ∈ s, (f i).PartiallyWellOrderedOn r := by
  simpa only [Finset.sup_eq_supr] using s.partially_well_ordered_on_sup

@[simp]
theorem is_wf_bUnion [Preorderₓ α] (s : Finset ι) {f : ι → Set α} : (⋃ i ∈ s, f i).IsWf ↔ ∀ i ∈ s, (f i).IsWf :=
  s.well_founded_on_bUnion

@[simp]
theorem is_pwo_bUnion [Preorderₓ α] (s : Finset ι) {f : ι → Set α} : (⋃ i ∈ s, f i).IsPwo ↔ ∀ i ∈ s, (f i).IsPwo :=
  s.partially_well_ordered_on_bUnion

end Finset

namespace Set

section Preorderₓ

variable [Preorderₓ α] {s : Set α} {a : α}

/-- `is_wf.min` returns a minimal element of a nonempty well-founded set. -/
noncomputable def IsWf.min (hs : IsWf s) (hn : s.Nonempty) : α :=
  hs.min Univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)

theorem IsWf.min_mem (hs : IsWf s) (hn : s.Nonempty) : hs.min hn ∈ s :=
  (WellFounded.min hs Univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)).2

theorem IsWf.not_lt_min (hs : IsWf s) (hn : s.Nonempty) (ha : a ∈ s) : ¬a < hs.min hn :=
  hs.not_lt_min Univ (nonempty_iff_univ_nonempty.1 hn.to_subtype) (mem_univ (⟨a, ha⟩ : s))

@[simp]
theorem is_wf_min_singleton (a) {hs : IsWf ({a} : Set α)} {hn : ({a} : Set α).Nonempty} : hs.min hn = a :=
  eq_of_mem_singleton (IsWf.min_mem hs hn)

end Preorderₓ

section LinearOrderₓ

variable [LinearOrderₓ α] {s t : Set α} {a : α}

theorem IsWf.min_le (hs : s.IsWf) (hn : s.Nonempty) (ha : a ∈ s) : hs.min hn ≤ a :=
  le_of_not_ltₓ (hs.not_lt_min hn ha)

theorem IsWf.le_min_iff (hs : s.IsWf) (hn : s.Nonempty) : a ≤ hs.min hn ↔ ∀ b, b ∈ s → a ≤ b :=
  ⟨fun ha b hb => le_transₓ ha (hs.min_le hn hb), fun h => h _ (hs.min_mem _)⟩

theorem IsWf.min_le_min_of_subset {hs : s.IsWf} {hsn : s.Nonempty} {ht : t.IsWf} {htn : t.Nonempty} (hst : s ⊆ t) :
    ht.min htn ≤ hs.min hsn :=
  (IsWf.le_min_iff _ _).2 fun b hb => ht.min_le htn (hst hb)

theorem IsWf.min_union (hs : s.IsWf) (hsn : s.Nonempty) (ht : t.IsWf) (htn : t.Nonempty) :
    (hs.union ht).min (union_nonempty.2 (Or.intro_left _ hsn)) = min (hs.min hsn) (ht.min htn) := by
  refine'
    le_antisymmₓ
      (le_minₓ (is_wf.min_le_min_of_subset (subset_union_left _ _))
        (is_wf.min_le_min_of_subset (subset_union_right _ _)))
      _
  rw [min_le_iff]
  exact
    ((mem_union _ _ _).1 ((hs.union ht).min_mem (union_nonempty.2 (Or.intro_left _ hsn)))).imp (hs.min_le _)
      (ht.min_le _)

end LinearOrderₓ

end Set

open Set

namespace Set.PartiallyWellOrderedOn

variable {r : α → α → Prop}

/-- In the context of partial well-orderings, a bad sequence is a nonincreasing sequence
  whose range is contained in a particular set `s`. One exists if and only if `s` is not
  partially well-ordered. -/
def IsBadSeq (r : α → α → Prop) (s : Set α) (f : ℕ → α) : Prop :=
  (∀ n, f n ∈ s) ∧ ∀ m n : ℕ, m < n → ¬r (f m) (f n)

theorem iff_forall_not_is_bad_seq (r : α → α → Prop) (s : Set α) : s.PartiallyWellOrderedOn r ↔ ∀ f, ¬IsBadSeq r s f :=
  forall_congrₓ fun f => by
    simp [is_bad_seq]

/-- This indicates that every bad sequence `g` that agrees with `f` on the first `n`
  terms has `rk (f n) ≤ rk (g n)`. -/
def IsMinBadSeq (r : α → α → Prop) (rk : α → ℕ) (s : Set α) (n : ℕ) (f : ℕ → α) : Prop :=
  ∀ g : ℕ → α, (∀ m : ℕ, m < n → f m = g m) → rk (g n) < rk (f n) → ¬IsBadSeq r s g

/-- Given a bad sequence `f`, this constructs a bad sequence that agrees with `f` on the first `n`
  terms and is minimal at `n`.
-/
noncomputable def minBadSeqOfBadSeq (r : α → α → Prop) (rk : α → ℕ) (s : Set α) (n : ℕ) (f : ℕ → α)
    (hf : IsBadSeq r s f) : { g : ℕ → α // (∀ m : ℕ, m < n → f m = g m) ∧ IsBadSeq r s g ∧ IsMinBadSeq r rk s n g } :=
  by
  classical
  have h : ∃ (k : ℕ)(g : ℕ → α), (∀ m, m < n → f m = g m) ∧ is_bad_seq r s g ∧ rk (g n) = k :=
    ⟨_, f, fun _ _ => rfl, hf, rfl⟩
  obtain ⟨h1, h2, h3⟩ := Classical.some_spec (Nat.find_specₓ h)
  refine'
    ⟨Classical.some (Nat.find_specₓ h), h1, by
      convert h2, fun g hg1 hg2 con => _⟩
  refine'
    Nat.find_minₓ h _
      ⟨g, fun m mn => (h1 m mn).trans (hg1 m mn), by
        convert con, rfl⟩
  rwa [← h3]

theorem exists_min_bad_of_exists_bad (r : α → α → Prop) (rk : α → ℕ) (s : Set α) :
    (∃ f, IsBadSeq r s f) → ∃ f, IsBadSeq r s f ∧ ∀ n, IsMinBadSeq r rk s n f := by
  rintro ⟨f0, hf0 : is_bad_seq r s f0⟩
  let fs : ∀ n : ℕ, { f : ℕ → α // is_bad_seq r s f ∧ is_min_bad_seq r rk s n f } := by
    refine' Nat.rec _ _
    · exact ⟨(min_bad_seq_of_bad_seq r rk s 0 f0 hf0).1, (min_bad_seq_of_bad_seq r rk s 0 f0 hf0).2.2⟩
      
    · exact fun n fn =>
        ⟨(min_bad_seq_of_bad_seq r rk s (n + 1) fn.1 fn.2.1).1, (min_bad_seq_of_bad_seq r rk s (n + 1) fn.1 fn.2.1).2.2⟩
      
  have h : ∀ m n, m ≤ n → (fs m).1 m = (fs n).1 m := by
    intro m n mn
    obtain ⟨k, rfl⟩ := exists_add_of_le mn
    clear mn
    induction' k with k ih
    · rfl
      
    rw [ih,
      (min_bad_seq_of_bad_seq r rk s (m + k).succ (fs (m + k)).1 (fs (m + k)).2.1).2.1 m
        (Nat.lt_succ_iffₓ.2 (Nat.add_le_add_leftₓ k.zero_le m))]
    rfl
  refine' ⟨fun n => (fs n).1 n, ⟨fun n => (fs n).2.1.1 n, fun m n mn => _⟩, fun n g hg1 hg2 => _⟩
  · dsimp'
    rw [← Subtype.val_eq_coe, h m n (le_of_ltₓ mn)]
    convert (fs n).2.1.2 m n mn
    
  · convert (fs n).2.2 g (fun m mn => Eq.trans _ (hg1 m mn)) (lt_of_lt_of_leₓ hg2 le_rflₓ)
    rw [← h m n (le_of_ltₓ mn)]
    

theorem iff_not_exists_is_min_bad_seq (rk : α → ℕ) {s : Set α} :
    s.PartiallyWellOrderedOn r ↔ ¬∃ f, IsBadSeq r s f ∧ ∀ n, IsMinBadSeq r rk s n f := by
  rw [iff_forall_not_is_bad_seq, ← not_exists, not_congr]
  constructor
  · apply exists_min_bad_of_exists_bad
    
  rintro ⟨f, hf1, hf2⟩
  exact ⟨f, hf1⟩

/-- Higman's Lemma, which states that for any reflexive, transitive relation `r` which is
  partially well-ordered on a set `s`, the relation `list.sublist_forall₂ r` is partially
  well-ordered on the set of lists of elements of `s`. That relation is defined so that
  `list.sublist_forall₂ r l₁ l₂` whenever `l₁` related pointwise by `r` to a sublist of `l₂`.  -/
theorem partially_well_ordered_on_sublist_forall₂ (r : α → α → Prop) [IsRefl α r] [IsTrans α r] {s : Set α}
    (h : s.PartiallyWellOrderedOn r) :
    { l : List α | ∀ x, x ∈ l → x ∈ s }.PartiallyWellOrderedOn (List.SublistForall₂ r) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨as, has⟩)
  · apply partially_well_ordered_on.mono (Finset.partially_well_ordered_on {List.nil})
    · intro l hl
      rw [Finset.mem_coe, Finset.mem_singleton, List.eq_nil_iff_forall_not_memₓ]
      exact hl
      
    infer_instance
    
  haveI : Inhabited α := ⟨as⟩
  rw [iff_not_exists_is_min_bad_seq List.length]
  rintro ⟨f, hf1, hf2⟩
  have hnil : ∀ n, f n ≠ List.nil := fun n con => hf1.2 n n.succ n.lt_succ_self (con.symm ▸ List.SublistForall₂.nil)
  obtain ⟨g, hg⟩ := h.exists_monotone_subseq (List.headₓ ∘ f) _
  swap
  · simp only [Set.range_subset_iff, Function.comp_applyₓ]
    exact fun n => hf1.1 n _ (List.head_mem_self (hnil n))
    
  have hf' := hf2 (g 0) (fun n => if n < g 0 then f n else List.tail (f (g (n - g 0)))) (fun m hm => (if_pos hm).symm) _
  swap
  · simp only [if_neg (lt_irreflₓ (g 0)), tsub_self]
    rw [List.length_tail, ← Nat.pred_eq_sub_one]
    exact Nat.pred_ltₓ fun con => hnil _ (List.length_eq_zero.1 con)
    
  rw [is_bad_seq] at hf'
  push_neg  at hf'
  obtain ⟨m, n, mn, hmn⟩ := hf' _
  swap
  · rintro n x hx
    split_ifs  at hx with hn hn
    · exact hf1.1 _ _ hx
      
    · refine' hf1.1 _ _ (List.tail_subset _ hx)
      
    
  by_cases' hn : n < g 0
  · apply hf1.2 m n mn
    rwa [if_pos hn, if_pos (mn.trans hn)] at hmn
    
  · obtain ⟨n', rfl⟩ := exists_add_of_le (not_ltₓ.1 hn)
    rw [if_neg hn, add_commₓ (g 0) n', add_tsub_cancel_right] at hmn
    split_ifs  at hmn with hm hm
    · apply hf1.2 m (g n') (lt_of_lt_of_leₓ hm (g.monotone n'.zero_le))
      exact trans hmn (List.tail_sublist_forall₂_self _)
      
    · rw [← tsub_lt_iff_left (le_of_not_ltₓ hm)] at mn
      apply hf1.2 _ _ (g.lt_iff_lt.2 mn)
      rw [← List.cons_head_tail (hnil (g (m - g 0))), ← List.cons_head_tail (hnil (g n'))]
      exact List.SublistForall₂.cons (hg _ _ (le_of_ltₓ mn)) hmn
      
    

end Set.PartiallyWellOrderedOn

theorem WellFounded.is_wf [LT α] (h : WellFounded ((· < ·) : α → α → Prop)) (s : Set α) : s.IsWf :=
  (Set.is_wf_univ_iff.2 h).mono s.subset_univ

/-- A version of **Dickson's lemma** any subset of functions `Π s : σ, α s` is partially well
ordered, when `σ` is a `fintype` and each `α s` is a linear well order.
This includes the classical case of Dickson's lemma that `ℕ ^ n` is a well partial order.
Some generalizations would be possible based on this proof, to include cases where the target is
partially well ordered, and also to consider the case of `set.partially_well_ordered_on` instead of
`set.is_pwo`. -/
theorem Pi.is_pwo {α : ι → Type _} [∀ i, LinearOrderₓ (α i)] [∀ i, IsWellOrder (α i) (· < ·)] [Finite ι]
    (s : Set (∀ i, α i)) : s.IsPwo := by
  classical
  cases nonempty_fintype ι
  refine' is_pwo.mono _ (subset_univ _)
  rw [is_pwo_iff_exists_monotone_subseq]
  simp only [mem_univ, forall_const, Function.comp_app]
  suffices
    ∀ s : Finset ι,
      ∀ f : ℕ → ∀ s, α s, ∃ g : ℕ ↪o ℕ, ∀ ⦃a b : ℕ⦄, a ≤ b → ∀ (x : ι) (hs : x ∈ s), (f ∘ g) a x ≤ (f ∘ g) b x
    by
    simpa only [forall_true_left, Finset.mem_univ] using this Finset.univ
  apply' Finset.induction
  · intro f
    exists RelEmbedding.refl (· ≤ ·)
    simp only [IsEmpty.forall_iff, implies_true_iff, forall_const, Finset.not_mem_empty]
    
  · intro x s hx ih f
    obtain ⟨g, hg⟩ := (is_well_founded.wf.is_wf univ).IsPwo.exists_monotone_subseq (fun n => f n x) mem_univ
    obtain ⟨g', hg'⟩ := ih (f ∘ g)
    refine' ⟨g'.trans g, fun a b hab => _⟩
    simp only [Finset.mem_insert, RelEmbedding.coe_trans, Function.comp_app, forall_eq_or_imp]
    exact ⟨hg (OrderHomClass.mono g' hab), hg' hab⟩
    

