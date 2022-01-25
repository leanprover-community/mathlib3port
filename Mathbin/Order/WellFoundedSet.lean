import Mathbin.Algebra.Pointwise
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
 * `set.is_pwo s` indicates that any infinite sequence of elements in `s`
  contains an infinite monotone subsequence. Note that

### Definitions for Hahn Series
 * `set.add_antidiagonal s t a` and `set.mul_antidiagonal s t a` are the sets of pairs of elements
  from `s` and `t` that add/multiply to `a`.
 * `finset.add_antidiagonal` and `finset.mul_antidiagonal` are finite versions of
  `set.add_antidiagonal` and `set.mul_antidiagonal` defined when `s` and `t` are well-founded.

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


open_locale Pointwise

variable {α : Type _}

namespace Set

/-- `s.well_founded_on r` indicates that the relation `r` is well-founded when restricted to `s`. -/
def well_founded_on (s : Set α) (r : α → α → Prop) : Prop :=
  WellFounded fun a : s b : s => r a b

theorem well_founded_on_iff {s : Set α} {r : α → α → Prop} :
    s.well_founded_on r ↔ WellFounded fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s := by
  have f : RelEmbedding (fun a : s b : s => r a b) fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s :=
    ⟨⟨coe, Subtype.coe_injective⟩, fun a b => by
      simp ⟩
  refine' ⟨fun h => _, f.well_founded⟩
  rw [WellFounded.well_founded_iff_has_min]
  intro t ht
  by_cases' hst : (s ∩ t).Nonempty
  · rw [← Subtype.preimage_coe_nonempty] at hst
    rcases WellFounded.well_founded_iff_has_min.1 h (coe ⁻¹' t) hst with ⟨⟨m, ms⟩, mt, hm⟩
    exact ⟨m, mt, fun x xt ⟨xm, xs, ms⟩ => hm ⟨x, xs⟩ xt xm⟩
    
  · rcases ht with ⟨m, mt⟩
    exact ⟨m, mt, fun x xt ⟨xm, xs, ms⟩ => hst ⟨m, ⟨ms, mt⟩⟩⟩
    

theorem well_founded_on.induction {s : Set α} {r : α → α → Prop} (hs : s.well_founded_on r) {x : α} (hx : x ∈ s)
    {P : α → Prop} (hP : ∀, ∀ y ∈ s, ∀, (∀, ∀ z ∈ s, ∀, r z y → P z) → P y) : P x := by
  let Q : s → Prop := fun y => P y
  change Q ⟨x, hx⟩
  refine' WellFounded.induction hs ⟨x, hx⟩ _
  rintro ⟨y, ys⟩ ih
  exact hP _ ys fun z zs zy => ih ⟨z, zs⟩ zy

instance is_strict_order.subset {s : Set α} {r : α → α → Prop} [IsStrictOrder α r] :
    IsStrictOrder α fun a b : α => r a b ∧ a ∈ s ∧ b ∈ s where
  to_is_irrefl := ⟨fun a con => irrefl_of r a con.1⟩
  to_is_trans := ⟨fun a b c ab bc => ⟨trans_of r ab.1 bc.1, ab.2.1, bc.2.2⟩⟩

theorem well_founded_on_iff_no_descending_seq {s : Set α} {r : α → α → Prop} [IsStrictOrder α r] :
    s.well_founded_on r ↔ ∀ f : (· > · : ℕ → ℕ → Prop) ↪r r, ¬range f ⊆ s := by
  rw [well_founded_on_iff, RelEmbedding.well_founded_iff_no_descending_seq]
  refine'
    ⟨fun h f con => by
      refine' h.elim' ⟨⟨f, f.injective⟩, fun a b => _⟩
      simp only [con (mem_range_self a), con (mem_range_self b), and_trueₓ, gt_iff_lt, Function.Embedding.coe_fn_mk,
        f.map_rel_iff],
      fun h => ⟨fun con => _⟩⟩
  rcases con with ⟨f, hf⟩
  have hfs' : ∀ n : ℕ, f n ∈ s := fun n => (hf.2 n.lt_succ_self).2.2
  refine' h ⟨f, fun a b => _⟩ fun n hn => _
  · rw [← hf]
    exact ⟨fun h => ⟨h, hfs' _, hfs' _⟩, fun h => h.1⟩
    
  · rcases Set.mem_range.1 hn with ⟨m, hm⟩
    rw [← hm]
    apply hfs'
    

section LT

variable [LT α]

/-- `s.is_wf` indicates that `<` is well-founded when restricted to `s`. -/
def is_wf (s : Set α) : Prop :=
  well_founded_on s (· < ·)

theorem is_wf_univ_iff : is_wf (univ : Set α) ↔ WellFounded (· < · : α → α → Prop) := by
  simp [is_wf, well_founded_on_iff]

variable {s t : Set α}

theorem is_wf.mono (h : is_wf t) (st : s ⊆ t) : is_wf s := by
  rw [is_wf, well_founded_on_iff] at *
  refine' Subrelation.wfₓ (fun x y xy => _) h
  exact ⟨xy.1, st xy.2.1, st xy.2.2⟩

end LT

section PartialOrderₓ

variable [PartialOrderₓ α] {s t : Set α} {a : α}

theorem is_wf_iff_no_descending_seq : is_wf s ↔ ∀ f : OrderDual ℕ ↪o α, ¬range f ⊆ s := by
  have : IsStrictOrder α fun a b : α => a < b ∧ a ∈ s ∧ b ∈ s :=
    { to_is_irrefl := ⟨fun x con => lt_irreflₓ x con.1⟩,
      to_is_trans := ⟨fun a b c ab bc => ⟨lt_transₓ ab.1 bc.1, ab.2.1, bc.2.2⟩⟩ }
  rw [is_wf, well_founded_on_iff_no_descending_seq]
  exact ⟨fun h f => h f.lt_embedding, fun h f => h (OrderEmbedding.ofStrictMono f fun _ _ => f.map_rel_iff.2)⟩

theorem is_wf.union (hs : is_wf s) (ht : is_wf t) : is_wf (s ∪ t) := by
  classical
  rw [is_wf_iff_no_descending_seq] at *
  rintro f fst
  have h : Infinite (f ⁻¹' s) ∨ Infinite (f ⁻¹' t) := by
    have h : Infinite (univ : Set ℕ) := infinite_univ
    have hpre : f ⁻¹' (s ∪ t) = Set.Univ := by
      rw [← image_univ, image_subset_iff, univ_subset_iff] at fst
      exact fst
    rw [preimage_union] at hpre
    rw [← hpre] at h
    rw [Infinite, Infinite]
    rw [Infinite] at h
    contrapose! h
    exact finite.union h.1 h.2
  rw [← infinite_coe_iff, ← infinite_coe_iff] at h
  cases' h with inf inf <;> have := inf
  · apply hs ((Nat.orderEmbeddingOfSet (f ⁻¹' s)).dual.trans f)
    change range (Function.comp f (Nat.orderEmbeddingOfSet (f ⁻¹' s))) ⊆ s
    rw [range_comp, image_subset_iff]
    simp
    
  · apply ht ((Nat.orderEmbeddingOfSet (f ⁻¹' t)).dual.trans f)
    change range (Function.comp f (Nat.orderEmbeddingOfSet (f ⁻¹' t))) ⊆ t
    rw [range_comp, image_subset_iff]
    simp
    

end PartialOrderₓ

end Set

namespace Set

/-- A subset is partially well-ordered by a relation `r` when any infinite sequence contains
  two elements where the first is related to the second by `r`. -/
def partially_well_ordered_on s (r : α → α → Prop) : Prop :=
  ∀ f : ℕ → α, range f ⊆ s → ∃ m n : ℕ, m < n ∧ r (f m) (f n)

/-- A subset of a preorder is partially well-ordered when any infinite sequence contains
  a monotone subsequence of length 2 (or equivalently, an infinite monotone subsequence). -/
def is_pwo [Preorderₓ α] s : Prop :=
  partially_well_ordered_on s (· ≤ · : α → α → Prop)

theorem partially_well_ordered_on.mono {s t : Set α} {r : α → α → Prop} (ht : t.partially_well_ordered_on r)
    (hsub : s ⊆ t) : s.partially_well_ordered_on r := fun f hf => ht f (Set.Subset.trans hf hsub)

theorem partially_well_ordered_on.image_of_monotone_on {s : Set α} {r : α → α → Prop} {β : Type _} {r' : β → β → Prop}
    (hs : s.partially_well_ordered_on r) {f : α → β} (hf : ∀ a1 a2 : α, a1 ∈ s → a2 ∈ s → r a1 a2 → r' (f a1) (f a2)) :
    (f '' s).PartiallyWellOrderedOn r' := fun g hg => by
  have h := fun n : ℕ => (mem_image _ _ _).1 (hg (mem_range_self n))
  obtain ⟨m, n, hlt, hmn⟩ := hs (fun n => Classical.some (h n)) _
  · refine' ⟨m, n, hlt, _⟩
    rw [← (Classical.some_spec (h m)).2, ← (Classical.some_spec (h n)).2]
    exact hf _ _ (Classical.some_spec (h m)).1 (Classical.some_spec (h n)).1 hmn
    
  · rintro _ ⟨n, rfl⟩
    exact (Classical.some_spec (h n)).1
    

theorem _root_.is_antichain.finite_of_partially_well_ordered_on {s : Set α} {r : α → α → Prop} (ha : IsAntichain r s)
    (hp : s.partially_well_ordered_on r) : s.finite := by
  refine' finite_or_infinite.resolve_right fun hi => _
  obtain ⟨m, n, hmn, h⟩ := hp (fun n => hi.nat_embedding _ n) (range_subset_iff.2 $ fun n => (hi.nat_embedding _ n).2)
  exact
    hmn.ne
      ((hi.nat_embedding _).Injective $
        Subtype.val_injective $ ha.eq (hi.nat_embedding _ m).2 (hi.nat_embedding _ n).2 h)

theorem finite.partially_well_ordered_on {s : Set α} {r : α → α → Prop} [IsRefl α r] (hs : s.finite) :
    s.partially_well_ordered_on r := by
  intro f hf
  obtain ⟨m, n, hmn, h⟩ := hs.exists_lt_map_eq_of_range_subset hf
  exact ⟨m, n, hmn, h.subst $ refl (f m)⟩

theorem _root_.is_antichain.partially_well_ordered_on_iff {s : Set α} {r : α → α → Prop} [IsRefl α r]
    (hs : IsAntichain r s) : s.partially_well_ordered_on r ↔ s.finite :=
  ⟨hs.finite_of_partially_well_ordered_on, finite.partially_well_ordered_on⟩

-- ././Mathport/Syntax/Translate/Basic.lean:417:16: unsupported tactic `by_contra'
-- ././Mathport/Syntax/Translate/Basic.lean:480:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem partially_well_ordered_on_iff_finite_antichains {s : Set α} {r : α → α → Prop} [IsRefl α r] [IsSymm α r] :
    s.partially_well_ordered_on r ↔ ∀ t _ : t ⊆ s, IsAntichain r t → t.finite := by
  refine' ⟨fun h t ht hrt => hrt.finite_of_partially_well_ordered_on (h.mono ht), _⟩
  rintro hs f hf
  "././Mathport/Syntax/Translate/Basic.lean:417:16: unsupported tactic `by_contra'"
  refine' Set.infinite_range_of_injective (fun m n hmn => _) (hs _ hf _)
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
    

section PartialOrderₓ

variable {s : Set α} {t : Set α} {r : α → α → Prop}

theorem partially_well_ordered_on.exists_monotone_subseq [IsRefl α r] [IsTrans α r] (h : s.partially_well_ordered_on r)
    (f : ℕ → α) (hf : range f ⊆ s) : ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) := by
  obtain ⟨g, h1 | h2⟩ := exists_increasing_or_nonincreasing_subseq r f
  · refine' ⟨g, fun m n hle => _⟩
    obtain hlt | heq := lt_or_eq_of_leₓ hle
    · exact h1 m n hlt
      
    · rw [HEq]
      apply refl_of r
      
    
  · exfalso
    obtain ⟨m, n, hlt, hle⟩ := h (f ∘ g) (subset.trans (range_comp_subset_range _ _) hf)
    exact h2 m n hlt hle
    

theorem partially_well_ordered_on_iff_exists_monotone_subseq [IsRefl α r] [IsTrans α r] :
    s.partially_well_ordered_on r ↔ ∀ f : ℕ → α, range f ⊆ s → ∃ g : ℕ ↪o ℕ, ∀ m n : ℕ, m ≤ n → r (f (g m)) (f (g n)) :=
  by
  classical
  constructor <;> intro h f hf
  · exact h.exists_monotone_subseq f hf
    
  · obtain ⟨g, gmon⟩ := h f hf
    refine' ⟨g 0, g 1, g.lt_iff_lt.2 zero_lt_one, gmon _ _ zero_le_one⟩
    

theorem partially_well_ordered_on.well_founded_on [IsPartialOrder α r] (h : s.partially_well_ordered_on r) :
    s.well_founded_on fun a b => r a b ∧ a ≠ b := by
  have : IsStrictOrder α fun a b => r a b ∧ a ≠ b :=
    { to_is_irrefl := ⟨fun a con => con.2 rfl⟩,
      to_is_trans := ⟨fun a b c ab bc => ⟨trans ab.1 bc.1, fun ac => ab.2 (antisymm ab.1 (ac.symm ▸ bc.1))⟩⟩ }
  rw [well_founded_on_iff_no_descending_seq]
  intro f con
  obtain ⟨m, n, hlt, hle⟩ := h f con
  exact (f.map_rel_iff.2 hlt).2 (antisymm hle (f.map_rel_iff.2 hlt).1).symm

variable [PartialOrderₓ α]

theorem is_pwo.is_wf (h : s.is_pwo) : s.is_wf := by
  rw [is_wf]
  convert h.well_founded_on
  ext x y
  rw [lt_iff_le_and_ne]

theorem is_pwo.exists_monotone_subseq (h : s.is_pwo) (f : ℕ → α) (hf : range f ⊆ s) : ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  h.exists_monotone_subseq f hf

theorem is_pwo_iff_exists_monotone_subseq : s.is_pwo ↔ ∀ f : ℕ → α, range f ⊆ s → ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  partially_well_ordered_on_iff_exists_monotone_subseq

theorem is_pwo.prod (hs : s.is_pwo) (ht : t.is_pwo) : (s ×ˢ t : Set _).IsPwo := by
  classical
  rw [is_pwo_iff_exists_monotone_subseq] at *
  intro f hf
  obtain ⟨g1, h1⟩ := hs (Prod.fst ∘ f) _
  swap
  · rw [range_comp, image_subset_iff]
    refine' subset.trans hf _
    rintro ⟨x1, x2⟩ hx
    simp only [mem_preimage, hx.1]
    
  obtain ⟨g2, h2⟩ := ht (Prod.snd ∘ f ∘ g1) _
  refine' ⟨g2.trans g1, fun m n mn => _⟩
  swap
  · rw [range_comp, image_subset_iff]
    refine' subset.trans (range_comp_subset_range _ _) (subset.trans hf _)
    rintro ⟨x1, x2⟩ hx
    simp only [mem_preimage, hx.2]
    
  simp only [RelEmbedding.coe_trans, Function.comp_app]
  exact ⟨h1 (g2.le_iff_le.2 mn), h2 mn⟩

theorem is_pwo.image_of_monotone {β : Type _} [PartialOrderₓ β] (hs : s.is_pwo) {f : α → β} (hf : Monotone f) :
    is_pwo (f '' s) :=
  hs.image_of_monotone_on fun _ _ _ _ ab => hf ab

theorem is_pwo.union (hs : is_pwo s) (ht : is_pwo t) : is_pwo (s ∪ t) := by
  classical
  rw [is_pwo_iff_exists_monotone_subseq] at *
  rintro f fst
  have h : Infinite (f ⁻¹' s) ∨ Infinite (f ⁻¹' t) := by
    have h : Infinite (univ : Set ℕ) := infinite_univ
    have hpre : f ⁻¹' (s ∪ t) = Set.Univ := by
      rw [← image_univ, image_subset_iff, univ_subset_iff] at fst
      exact fst
    rw [preimage_union] at hpre
    rw [← hpre] at h
    rw [Infinite, Infinite]
    rw [Infinite] at h
    contrapose! h
    exact finite.union h.1 h.2
  rw [← infinite_coe_iff, ← infinite_coe_iff] at h
  cases' h with inf inf <;> have := inf
  · obtain ⟨g, hg⟩ := hs (f ∘ Nat.orderEmbeddingOfSet (f ⁻¹' s)) _
    · rw [Function.comp.assoc, ← RelEmbedding.coe_trans] at hg
      exact ⟨_, hg⟩
      
    rw [range_comp, image_subset_iff]
    simp
    
  · obtain ⟨g, hg⟩ := ht (f ∘ Nat.orderEmbeddingOfSet (f ⁻¹' t)) _
    · rw [Function.comp.assoc, ← RelEmbedding.coe_trans] at hg
      exact ⟨_, hg⟩
      
    rw [range_comp, image_subset_iff]
    simp
    

end PartialOrderₓ

theorem is_wf.is_pwo [LinearOrderₓ α] {s : Set α} (hs : s.is_wf) : s.is_pwo := fun f hf => by
  rw [is_wf, well_founded_on_iff] at hs
  have hrange : (range f).Nonempty := ⟨f 0, mem_range_self 0⟩
  let a := hs.min (range f) hrange
  obtain ⟨m, hm⟩ := hs.min_mem (range f) hrange
  refine' ⟨m, m.succ, m.lt_succ_self, le_of_not_ltₓ fun con => _⟩
  rw [hm] at con
  apply hs.not_lt_min (range f) hrange (mem_range_self m.succ) ⟨con, hf (mem_range_self m.succ), hf _⟩
  rw [← hm]
  apply mem_range_self

theorem is_wf_iff_is_pwo [LinearOrderₓ α] {s : Set α} : s.is_wf ↔ s.is_pwo :=
  ⟨is_wf.is_pwo, is_pwo.is_wf⟩

end Set

namespace Finset

@[simp]
theorem partially_well_ordered_on {r : α → α → Prop} [IsRefl α r] (s : Finset α) :
    (s : Set α).PartiallyWellOrderedOn r :=
  s.finite_to_set.partially_well_ordered_on

@[simp]
theorem is_pwo [PartialOrderₓ α] (f : Finset α) : Set.IsPwo (↑f : Set α) :=
  f.partially_well_ordered_on

@[simp]
theorem well_founded_on {r : α → α → Prop} [IsStrictOrder α r] (f : Finset α) : Set.WellFoundedOn (↑f : Set α) r := by
  rw [Set.well_founded_on_iff_no_descending_seq]
  intro g con
  apply Set.infinite_of_injective_forall_mem g.injective (Set.range_subset_iff.1 con)
  exact f.finite_to_set

@[simp]
theorem is_wf [PartialOrderₓ α] (f : Finset α) : Set.IsWf (↑f : Set α) :=
  f.is_pwo.is_wf

end Finset

namespace Set

variable [PartialOrderₓ α] {s : Set α} {a : α}

theorem finite.is_pwo (h : s.finite) : s.is_pwo := by
  rw [← h.coe_to_finset]
  exact h.to_finset.is_pwo

@[simp]
theorem fintype.is_pwo [Fintype α] : s.is_pwo :=
  (finite.of_fintype s).IsPwo

@[simp]
theorem is_pwo_empty : is_pwo (∅ : Set α) :=
  finite_empty.IsPwo

@[simp]
theorem is_pwo_singleton a : is_pwo ({a} : Set α) :=
  (finite_singleton a).IsPwo

theorem is_pwo.insert a (hs : is_pwo s) : is_pwo (insert a s) := by
  rw [← union_singleton]
  exact hs.union (is_pwo_singleton a)

/-- `is_wf.min` returns a minimal element of a nonempty well-founded set. -/
noncomputable def is_wf.min (hs : is_wf s) (hn : s.nonempty) : α :=
  hs.min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)

theorem is_wf.min_mem (hs : is_wf s) (hn : s.nonempty) : hs.min hn ∈ s :=
  (WellFounded.min hs univ (nonempty_iff_univ_nonempty.1 hn.to_subtype)).2

theorem is_wf.not_lt_min (hs : is_wf s) (hn : s.nonempty) (ha : a ∈ s) : ¬a < hs.min hn :=
  hs.not_lt_min univ (nonempty_iff_univ_nonempty.1 hn.to_subtype) (mem_univ (⟨a, ha⟩ : s))

@[simp]
theorem is_wf_min_singleton a {hs : is_wf ({a} : Set α)} {hn : ({a} : Set α).Nonempty} : hs.min hn = a :=
  eq_of_mem_singleton (is_wf.min_mem hs hn)

end Set

@[simp]
theorem Finset.is_wf_sup {ι : Type _} [PartialOrderₓ α] (f : Finset ι) (g : ι → Set α)
    (hf : ∀ i : ι, i ∈ f → (g i).IsWf) : (f.sup g).IsWf := by
  classical
  revert hf
  apply f.induction_on
  · intro h
    simp [set.is_pwo_empty.is_wf]
    
  · intro s f sf hf hsf
    rw [Finset.sup_insert]
    exact (hsf s (Finset.mem_insert_self _ _)).union (hf fun s' s'f => hsf _ (Finset.mem_insert_of_mem s'f))
    

@[simp]
theorem Finset.is_pwo_sup {ι : Type _} [PartialOrderₓ α] (f : Finset ι) (g : ι → Set α)
    (hf : ∀ i : ι, i ∈ f → (g i).IsPwo) : (f.sup g).IsPwo := by
  classical
  revert hf
  apply f.induction_on
  · intro h
    simp [set.is_pwo_empty.is_wf]
    
  · intro s f sf hf hsf
    rw [Finset.sup_insert]
    exact (hsf s (Finset.mem_insert_self _ _)).union (hf fun s' s'f => hsf _ (Finset.mem_insert_of_mem s'f))
    

namespace Set

variable [LinearOrderₓ α] {s t : Set α} {a : α}

theorem is_wf.min_le (hs : s.is_wf) (hn : s.nonempty) (ha : a ∈ s) : hs.min hn ≤ a :=
  le_of_not_ltₓ (hs.not_lt_min hn ha)

theorem is_wf.le_min_iff (hs : s.is_wf) (hn : s.nonempty) : a ≤ hs.min hn ↔ ∀ b, b ∈ s → a ≤ b :=
  ⟨fun ha b hb => le_transₓ ha (hs.min_le hn hb), fun h => h _ (hs.min_mem _)⟩

theorem is_wf.min_le_min_of_subset {hs : s.is_wf} {hsn : s.nonempty} {ht : t.is_wf} {htn : t.nonempty} (hst : s ⊆ t) :
    ht.min htn ≤ hs.min hsn :=
  (is_wf.le_min_iff _ _).2 fun b hb => ht.min_le htn (hst hb)

theorem is_wf.min_union (hs : s.is_wf) (hsn : s.nonempty) (ht : t.is_wf) (htn : t.nonempty) :
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

end Set

namespace Set

variable {s : Set α} {t : Set α}

@[to_additive]
theorem is_pwo.mul [OrderedCancelCommMonoid α] (hs : s.is_pwo) (ht : t.is_pwo) : is_pwo (s * t) := by
  rw [← image_mul_prod]
  exact (is_pwo.prod hs ht).image_of_monotone fun _ _ h => mul_le_mul' h.1 h.2

variable [LinearOrderedCancelCommMonoid α]

@[to_additive]
theorem is_wf.mul (hs : s.is_wf) (ht : t.is_wf) : is_wf (s * t) :=
  (hs.is_pwo.mul ht.is_pwo).IsWf

@[to_additive]
theorem is_wf.min_mul (hs : s.is_wf) (ht : t.is_wf) (hsn : s.nonempty) (htn : t.nonempty) :
    (hs.mul ht).min (hsn.mul htn) = hs.min hsn * ht.min htn := by
  refine' le_antisymmₓ (is_wf.min_le _ _ (mem_mul.2 ⟨_, _, hs.min_mem _, ht.min_mem _, rfl⟩)) _
  rw [is_wf.le_min_iff]
  rintro _ ⟨x, y, hx, hy, rfl⟩
  exact mul_le_mul' (hs.min_le _ hx) (ht.min_le _ hy)

end Set

namespace Set

namespace PartiallyWellOrderedOn

/-- In the context of partial well-orderings, a bad sequence is a nonincreasing sequence
  whose range is contained in a particular set `s`. One exists if and only if `s` is not
  partially well-ordered. -/
def is_bad_seq (r : α → α → Prop) (s : Set α) (f : ℕ → α) : Prop :=
  Set.Range f ⊆ s ∧ ∀ m n : ℕ, m < n → ¬r (f m) (f n)

theorem iff_forall_not_is_bad_seq (r : α → α → Prop) (s : Set α) :
    s.partially_well_ordered_on r ↔ ∀ f, ¬is_bad_seq r s f := by
  rw [Set.PartiallyWellOrderedOn]
  apply forall_congrₓ fun f => _
  simp [is_bad_seq]

/-- This indicates that every bad sequence `g` that agrees with `f` on the first `n`
  terms has `rk (f n) ≤ rk (g n)`. -/
def is_min_bad_seq (r : α → α → Prop) (rk : α → ℕ) (s : Set α) (n : ℕ) (f : ℕ → α) : Prop :=
  ∀ g : ℕ → α, (∀ m : ℕ, m < n → f m = g m) → rk (g n) < rk (f n) → ¬is_bad_seq r s g

/-- Given a bad sequence `f`, this constructs a bad sequence that agrees with `f` on the first `n`
  terms and is minimal at `n`.
-/
noncomputable def min_bad_seq_of_bad_seq (r : α → α → Prop) (rk : α → ℕ) (s : Set α) (n : ℕ) (f : ℕ → α)
    (hf : is_bad_seq r s f) :
    { g : ℕ → α // (∀ m : ℕ, m < n → f m = g m) ∧ is_bad_seq r s g ∧ is_min_bad_seq r rk s n g } := by
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
    (∃ f, is_bad_seq r s f) → ∃ f, is_bad_seq r s f ∧ ∀ n, is_min_bad_seq r rk s n f := by
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
  refine'
    ⟨fun n => (fs n).1 n, ⟨Set.range_subset_iff.2 fun n => (fs n).2.1.1 (mem_range_self n), fun m n mn => _⟩,
      fun n g hg1 hg2 => _⟩
  · dsimp
    rw [← Subtype.val_eq_coe, h m n (le_of_ltₓ mn)]
    convert (fs n).2.1.2 m n mn
    
  · convert (fs n).2.2 g (fun m mn => Eq.trans _ (hg1 m mn)) (lt_of_lt_of_leₓ hg2 (le_reflₓ _))
    rw [← h m n (le_of_ltₓ mn)]
    

theorem iff_not_exists_is_min_bad_seq {r : α → α → Prop} (rk : α → ℕ) {s : Set α} :
    s.partially_well_ordered_on r ↔ ¬∃ f, is_bad_seq r s f ∧ ∀ n, is_min_bad_seq r rk s n f := by
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
    (h : s.partially_well_ordered_on r) :
    { l : List α | ∀ x, x ∈ l → x ∈ s }.PartiallyWellOrderedOn (List.SublistForall₂ r) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨as, has⟩)
  · apply partially_well_ordered_on.mono (Finset.partially_well_ordered_on {List.nil})
    · intro l hl
      rw [Finset.mem_coe, Finset.mem_singleton, List.eq_nil_iff_forall_not_memₓ]
      exact hl
      
    infer_instance
    
  have : Inhabited α := ⟨as⟩
  rw [iff_not_exists_is_min_bad_seq List.length]
  rintro ⟨f, hf1, hf2⟩
  have hnil : ∀ n, f n ≠ List.nil := fun n con => hf1.2 n n.succ n.lt_succ_self (con.symm ▸ List.SublistForall₂.nil)
  obtain ⟨g, hg⟩ := h.exists_monotone_subseq (List.headₓ ∘ f) _
  swap
  · simp only [Set.range_subset_iff, Function.comp_applyₓ]
    exact fun n => hf1.1 (Set.mem_range_self n) _ (List.head_mem_self (hnil n))
    
  have hf' := hf2 (g 0) (fun n => if n < g 0 then f n else List.tail (f (g (n - g 0)))) (fun m hm => (if_pos hm).symm) _
  swap
  · simp only [if_neg (lt_irreflₓ (g 0)), tsub_self]
    rw [List.length_tail, ← Nat.pred_eq_sub_one]
    exact Nat.pred_ltₓ fun con => hnil _ (List.length_eq_zero.1 con)
    
  rw [is_bad_seq] at hf'
  push_neg  at hf'
  obtain ⟨m, n, mn, hmn⟩ := hf' _
  swap
  · rw [Set.range_subset_iff]
    rintro n x hx
    split_ifs  at hx with hn hn
    · exact hf1.1 (Set.mem_range_self _) _ hx
      
    · refine' hf1.1 (Set.mem_range_self _) _ (List.tail_subset _ hx)
      
    
  by_cases' hn : n < g 0
  · apply hf1.2 m n mn
    rwa [if_pos hn, if_pos (mn.trans hn)] at hmn
    
  · obtain ⟨n', rfl⟩ := le_iff_exists_add.1 (not_ltₓ.1 hn)
    rw [if_neg hn, add_commₓ (g 0) n', add_tsub_cancel_right] at hmn
    split_ifs  at hmn with hm hm
    · apply hf1.2 m (g n') (lt_of_lt_of_leₓ hm (g.monotone n'.zero_le))
      exact trans hmn (List.tail_sublist_forall₂_self _)
      
    · rw [← tsub_lt_iff_left (le_of_not_ltₓ hm)] at mn
      apply hf1.2 _ _ (g.lt_iff_lt.2 mn)
      rw [← List.cons_head_tail (hnil (g (m - g 0))), ← List.cons_head_tail (hnil (g n'))]
      exact List.SublistForall₂.cons (hg _ _ (le_of_ltₓ mn)) hmn
      
    

end PartiallyWellOrderedOn

namespace IsPwo

@[to_additive]
theorem submonoid_closure [OrderedCancelCommMonoid α] {s : Set α} (hpos : ∀ x : α, x ∈ s → 1 ≤ x) (h : s.is_pwo) :
    is_pwo (Submonoid.closure s : Set α) := by
  have hl : (Submonoid.closure s : Set α) ⊆ List.prod '' { l : List α | ∀ x, x ∈ l → x ∈ s } := by
    intro x hx
    rw [SetLike.mem_coe] at hx
    refine'
      Submonoid.closure_induction hx (fun x hx => ⟨_, fun y hy => _, List.prod_singleton⟩)
        ⟨_, fun y hy => (List.not_mem_nil _ hy).elim, List.prod_nil⟩ _
    · rwa [List.mem_singleton.1 hy]
      
    rintro _ _ ⟨l, hl, rfl⟩ ⟨l', hl', rfl⟩
    refine' ⟨_, fun y hy => _, List.prod_append⟩
    cases' List.mem_appendₓ.1 hy with hy hy
    · exact hl _ hy
      
    · exact hl' _ hy
      
  apply ((h.partially_well_ordered_on_sublist_forall₂ (· ≤ ·)).image_of_monotone_on _).mono hl
  intro l1 l2 hl1 hl2 h12
  obtain ⟨l, hll1, hll2⟩ := List.sublist_forall₂_iff.1 h12
  refine' le_transₓ (List.rel_prod (le_reflₓ 1) (fun a b ab c d cd => mul_le_mul' ab cd) hll1) _
  obtain ⟨l', hl'⟩ := hll2.exists_perm_append
  rw [hl'.prod_eq, List.prod_append, ← mul_oneₓ l.prod, mul_assoc, one_mulₓ]
  apply mul_le_mul_left'
  have hl's := fun x hx => hl2 x (List.Subset.trans (l.subset_append_right _) hl'.symm.subset hx)
  clear hl'
  induction' l' with x1 x2 x3 x4 x5
  · rfl
    
  rw [List.prod_cons, ← one_mulₓ (1 : α)]
  exact mul_le_mul' (hpos x1 (hl's x1 (List.mem_cons_selfₓ x1 x2))) (x3 fun x hx => hl's x (List.mem_cons_of_memₓ _ hx))

end IsPwo

/-- `set.mul_antidiagonal s t a` is the set of all pairs of an element in `s` and an element in `t`
  that multiply to `a`. -/
@[to_additive
      "`set.add_antidiagonal s t a` is the set of all pairs of an element in `s`\n  and an element in `t` that add to `a`."]
def mul_antidiagonal [Monoidₓ α] (s t : Set α) (a : α) : Set (α × α) :=
  { x | x.1 * x.2 = a ∧ x.1 ∈ s ∧ x.2 ∈ t }

namespace MulAntidiagonal

@[simp, to_additive]
theorem mem_mul_antidiagonal [Monoidₓ α] {s t : Set α} {a : α} {x : α × α} :
    x ∈ mul_antidiagonal s t a ↔ x.1 * x.2 = a ∧ x.1 ∈ s ∧ x.2 ∈ t :=
  Iff.refl _

section CancelCommMonoid

variable [CancelCommMonoid α] {s t : Set α} {a : α}

@[to_additive]
theorem fst_eq_fst_iff_snd_eq_snd {x y : mul_antidiagonal s t a} :
    (x : α × α).fst = (y : α × α).fst ↔ (x : α × α).snd = (y : α × α).snd :=
  ⟨fun h => by
    have hx := x.2.1
    rw [Subtype.val_eq_coe, h] at hx
    apply mul_left_cancelₓ (hx.trans y.2.1.symm), fun h => by
    have hx := x.2.1
    rw [Subtype.val_eq_coe, h] at hx
    apply mul_right_cancelₓ (hx.trans y.2.1.symm)⟩

@[to_additive]
theorem eq_of_fst_eq_fst {x y : mul_antidiagonal s t a} (h : (x : α × α).fst = (y : α × α).fst) : x = y :=
  Subtype.ext (Prod.extₓ h (mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd.1 h))

@[to_additive]
theorem eq_of_snd_eq_snd {x y : mul_antidiagonal s t a} (h : (x : α × α).snd = (y : α × α).snd) : x = y :=
  Subtype.ext (Prod.extₓ (mul_antidiagonal.fst_eq_fst_iff_snd_eq_snd.2 h) h)

end CancelCommMonoid

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] (s t : Set α) (a : α)

@[to_additive]
theorem eq_of_fst_le_fst_of_snd_le_snd {x y : mul_antidiagonal s t a} (h1 : (x : α × α).fst ≤ (y : α × α).fst)
    (h2 : (x : α × α).snd ≤ (y : α × α).snd) : x = y := by
  apply eq_of_fst_eq_fst
  cases' eq_or_lt_of_le h1 with heq hlt
  · exact HEq
    
  exfalso
  exact
    ne_of_ltₓ (mul_lt_mul_of_lt_of_le hlt h2) ((mem_mul_antidiagonal.1 x.2).1.trans (mem_mul_antidiagonal.1 y.2).1.symm)

variable {s} {t}

@[to_additive]
theorem finite_of_is_pwo (hs : s.is_pwo) (ht : t.is_pwo) a : (mul_antidiagonal s t a).Finite := by
  by_contra h
  rw [← Set.Infinite] at h
  have h1 : (mul_antidiagonal s t a).PartiallyWellOrderedOn (Prod.fst ⁻¹'o (· ≤ ·)) := by
    intro f hf
    refine' hs (Prod.fst ∘ f) _
    rw [range_comp]
    rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
    exact (mem_mul_antidiagonal.1 (hf hxy)).2.1
  have h2 : (mul_antidiagonal s t a).PartiallyWellOrderedOn (Prod.snd ⁻¹'o (· ≤ ·)) := by
    intro f hf
    refine' ht (Prod.snd ∘ f) _
    rw [range_comp]
    rintro _ ⟨⟨x, y⟩, hxy, rfl⟩
    exact (mem_mul_antidiagonal.1 (hf hxy)).2.2
  obtain ⟨g, hg⟩ := h1.exists_monotone_subseq (fun x => h.nat_embedding _ x) _
  swap
  · rintro _ ⟨k, rfl⟩
    exact ((Infinite.natEmbedding (s.mul_antidiagonal t a) h) _).2
    
  obtain ⟨m, n, mn, h2'⟩ := h2 (fun x => (h.nat_embedding _) (g x)) _
  swap
  · rintro _ ⟨k, rfl⟩
    exact ((Infinite.natEmbedding (s.mul_antidiagonal t a) h) _).2
    
  apply ne_of_ltₓ mn (g.injective ((h.nat_embedding _).Injective _))
  exact eq_of_fst_le_fst_of_snd_le_snd _ _ _ (hg _ _ (le_of_ltₓ mn)) h2'

end OrderedCancelCommMonoid

@[to_additive]
theorem finite_of_is_wf [LinearOrderedCancelCommMonoid α] {s t : Set α} (hs : s.is_wf) (ht : t.is_wf) a :
    (mul_antidiagonal s t a).Finite :=
  finite_of_is_pwo hs.is_pwo ht.is_pwo a

end MulAntidiagonal

end Set

namespace Finset

variable [OrderedCancelCommMonoid α]

variable {s t : Set α} (hs : s.is_pwo) (ht : t.is_pwo) (a : α)

/-- `finset.mul_antidiagonal_of_is_wf hs ht a` is the set of all pairs of an element in
  `s` and an element in `t` that multiply to `a`, but its construction requires proofs
  `hs` and `ht` that `s` and `t` are well-ordered. -/
@[to_additive
      "`finset.add_antidiagonal_of_is_wf hs ht a` is the set of all pairs of an element in\n  `s` and an element in `t` that add to `a`, but its construction requires proofs\n  `hs` and `ht` that `s` and `t` are well-ordered."]
noncomputable def mul_antidiagonal : Finset (α × α) :=
  (Set.MulAntidiagonal.finite_of_is_pwo hs ht a).toFinset

variable {hs} {ht} {u : Set α} {hu : u.is_pwo} {a} {x : α × α}

@[simp, to_additive]
theorem mem_mul_antidiagonal : x ∈ mul_antidiagonal hs ht a ↔ x.1 * x.2 = a ∧ x.1 ∈ s ∧ x.2 ∈ t := by
  simp [mul_antidiagonal]

@[to_additive]
theorem mul_antidiagonal_mono_left (hus : u ⊆ s) : Finset.mulAntidiagonal hu ht a ⊆ Finset.mulAntidiagonal hs ht a :=
  fun x hx => by
  rw [mem_mul_antidiagonal] at *
  exact ⟨hx.1, hus hx.2.1, hx.2.2⟩

@[to_additive]
theorem mul_antidiagonal_mono_right (hut : u ⊆ t) : Finset.mulAntidiagonal hs hu a ⊆ Finset.mulAntidiagonal hs ht a :=
  fun x hx => by
  rw [mem_mul_antidiagonal] at *
  exact ⟨hx.1, hx.2.1, hut hx.2.2⟩

@[to_additive]
theorem support_mul_antidiagonal_subset_mul : { a : α | (mul_antidiagonal hs ht a).Nonempty } ⊆ s * t :=
  fun x ⟨⟨a1, a2⟩, ha⟩ => by
  obtain ⟨hmul, h1, h2⟩ := mem_mul_antidiagonal.1 ha
  exact ⟨a1, a2, h1, h2, hmul⟩

@[to_additive]
theorem is_pwo_support_mul_antidiagonal : { a : α | (mul_antidiagonal hs ht a).Nonempty }.IsPwo :=
  (hs.mul ht).mono support_mul_antidiagonal_subset_mul

@[to_additive]
theorem mul_antidiagonal_min_mul_min {α} [LinearOrderedCancelCommMonoid α] {s t : Set α} (hs : s.is_wf) (ht : t.is_wf)
    (hns : s.nonempty) (hnt : t.nonempty) :
    mul_antidiagonal hs.is_pwo ht.is_pwo (hs.min hns * ht.min hnt) = {(hs.min hns, ht.min hnt)} := by
  ext ⟨a1, a2⟩
  rw [mem_mul_antidiagonal, Finset.mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨hast, has, hat⟩
    cases' eq_or_lt_of_le (hs.min_le hns has) with heq hlt
    · refine' ⟨HEq.symm, _⟩
      rw [HEq] at hast
      exact mul_left_cancelₓ hast
      
    · contrapose hast
      exact ne_of_gtₓ (mul_lt_mul_of_lt_of_le hlt (ht.min_le hnt hat))
      
    
  · rintro ⟨ha1, ha2⟩
    rw [ha1, ha2]
    exact ⟨rfl, hs.min_mem _, ht.min_mem _⟩
    

end Finset

theorem WellFounded.is_wf [LT α] (h : WellFounded (· < · : α → α → Prop)) (s : Set α) : s.is_wf :=
  (Set.is_wf_univ_iff.2 h).mono (Set.subset_univ s)

