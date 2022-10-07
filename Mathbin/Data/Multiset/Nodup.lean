/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Multiset.Bind
import Mathbin.Data.Multiset.Powerset
import Mathbin.Data.Multiset.Range

/-!
# The `nodup` predicate for multisets without duplicate elements.
-/


namespace Multiset

open Function List

variable {α β γ : Type _} {r : α → α → Prop} {s t : Multiset α} {a : α}

-- nodup
/-- `nodup s` means that `s` has no duplicates, i.e. the multiplicity of
  any element is at most 1. -/
def Nodupₓ (s : Multiset α) : Prop :=
  Quot.liftOn s Nodupₓ fun s t p => propext p.nodup_iff

@[simp]
theorem coe_nodup {l : List α} : @Nodupₓ α l ↔ l.Nodup :=
  Iff.rfl

@[simp]
theorem nodup_zero : @Nodupₓ α 0 :=
  pairwise.nil

@[simp]
theorem nodup_cons {a : α} {s : Multiset α} : Nodupₓ (a ::ₘ s) ↔ a ∉ s ∧ Nodupₓ s :=
  (Quot.induction_on s) fun l => nodup_cons

theorem Nodupₓ.cons (m : a ∉ s) (n : Nodupₓ s) : Nodupₓ (a ::ₘ s) :=
  nodup_cons.2 ⟨m, n⟩

@[simp]
theorem nodup_singleton : ∀ a : α, Nodupₓ ({a} : Multiset α) :=
  nodup_singleton

theorem Nodupₓ.of_cons (h : Nodupₓ (a ::ₘ s)) : Nodupₓ s :=
  (nodup_cons.1 h).2

theorem Nodupₓ.not_mem (h : Nodupₓ (a ::ₘ s)) : a ∉ s :=
  (nodup_cons.1 h).1

theorem nodup_of_le {s t : Multiset α} (h : s ≤ t) : Nodupₓ t → Nodupₓ s :=
  (le_induction_on h) fun l₁ l₂ => Nodupₓ.sublist

theorem not_nodup_pair : ∀ a : α, ¬Nodupₓ (a ::ₘ a ::ₘ 0) :=
  not_nodup_pair

theorem nodup_iff_le {s : Multiset α} : Nodupₓ s ↔ ∀ a : α, ¬a ::ₘ a ::ₘ 0 ≤ s :=
  (Quot.induction_on s) fun l =>
    nodup_iff_sublist.trans <| forall_congrₓ fun a => not_congr (@repeat_le_coe _ a 2 _).symm

theorem nodup_iff_ne_cons_cons {s : Multiset α} : s.Nodup ↔ ∀ a t, s ≠ a ::ₘ a ::ₘ t :=
  nodup_iff_le.trans
    ⟨fun h a t s_eq => h a (s_eq.symm ▸ cons_le_cons a (cons_le_cons a (zero_le _))), fun h a le =>
      let ⟨t, s_eq⟩ := le_iff_exists_add.mp le
      h a t (by rwa [cons_add, cons_add, zero_addₓ] at s_eq)⟩

theorem nodup_iff_count_le_one [DecidableEq α] {s : Multiset α} : Nodupₓ s ↔ ∀ a, count a s ≤ 1 :=
  (Quot.induction_on s) fun l => nodup_iff_count_le_one

@[simp]
theorem count_eq_one_of_mem [DecidableEq α] {a : α} {s : Multiset α} (d : Nodupₓ s) (h : a ∈ s) : count a s = 1 :=
  le_antisymmₓ (nodup_iff_count_le_one.1 d a) (count_pos.2 h)

theorem count_eq_of_nodup [DecidableEq α] {a : α} {s : Multiset α} (d : Nodupₓ s) :
    count a s = if a ∈ s then 1 else 0 := by
  split_ifs with h
  · exact count_eq_one_of_mem d h
    
  · exact count_eq_zero_of_not_mem h
    

theorem nodup_iff_pairwise {α} {s : Multiset α} : Nodupₓ s ↔ Pairwise (· ≠ ·) s :=
  (Quotientₓ.induction_on s) fun l => (pairwise_coe_iff_pairwise fun a b => Ne.symm).symm

protected theorem Nodupₓ.pairwise : (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b) → Nodupₓ s → Pairwise r s :=
  (Quotientₓ.induction_on s) fun l h hl => ⟨l, rfl, hl.imp_of_mem fun a b ha hb => h a ha b hb⟩

theorem Pairwise.forall (H : Symmetric r) (hs : Pairwise r s) : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b → r a b :=
  let ⟨l, hl₁, hl₂⟩ := hs
  hl₁.symm ▸ hl₂.forall H

theorem nodup_add {s t : Multiset α} : Nodupₓ (s + t) ↔ Nodupₓ s ∧ Nodupₓ t ∧ Disjoint s t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ => nodup_append

theorem disjoint_of_nodup_add {s t : Multiset α} (d : Nodupₓ (s + t)) : Disjoint s t :=
  (nodup_add.1 d).2.2

theorem Nodupₓ.add_iff (d₁ : Nodupₓ s) (d₂ : Nodupₓ t) : Nodupₓ (s + t) ↔ Disjoint s t := by simp [nodup_add, d₁, d₂]

theorem Nodupₓ.of_map (f : α → β) : Nodupₓ (map f s) → Nodupₓ s :=
  (Quot.induction_on s) fun l => Nodupₓ.of_map f

theorem Nodupₓ.map_on {f : α → β} : (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) → Nodupₓ s → Nodupₓ (map f s) :=
  (Quot.induction_on s) fun l => Nodupₓ.map_on

theorem Nodupₓ.map {f : α → β} {s : Multiset α} (hf : Injective f) : Nodupₓ s → Nodupₓ (map f s) :=
  Nodupₓ.map_on fun x _ y _ h => hf h

theorem inj_on_of_nodup_map {f : α → β} {s : Multiset α} : Nodupₓ (map f s) → ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  (Quot.induction_on s) fun l => inj_on_of_nodup_map

theorem nodup_map_iff_inj_on {f : α → β} {s : Multiset α} (d : Nodupₓ s) :
    Nodupₓ (map f s) ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩

theorem Nodupₓ.filter (p : α → Prop) [DecidablePred p] {s} : Nodupₓ s → Nodupₓ (filter p s) :=
  (Quot.induction_on s) fun l => Nodupₓ.filter p

@[simp]
theorem nodup_attach {s : Multiset α} : Nodupₓ (attach s) ↔ Nodupₓ s :=
  (Quot.induction_on s) fun l => nodup_attach

theorem Nodupₓ.pmap {p : α → Prop} {f : ∀ a, p a → β} {s : Multiset α} {H} (hf : ∀ a ha b hb, f a ha = f b hb → a = b) :
    Nodupₓ s → Nodupₓ (pmap f s H) :=
  Quot.induction_on s (fun l H => Nodupₓ.pmap hf) H

instance nodupDecidable [DecidableEq α] (s : Multiset α) : Decidable (Nodupₓ s) :=
  (Quotientₓ.recOnSubsingleton s) fun l => l.nodupDecidable

theorem Nodupₓ.erase_eq_filter [DecidableEq α] (a : α) {s} : Nodupₓ s → s.erase a = filter (· ≠ a) s :=
  (Quot.induction_on s) fun l d => congr_arg coe <| d.erase_eq_filter a

theorem Nodupₓ.erase [DecidableEq α] (a : α) {l} : Nodupₓ l → Nodupₓ (l.erase a) :=
  nodup_of_le (erase_le _ _)

theorem Nodupₓ.mem_erase_iff [DecidableEq α] {a b : α} {l} (d : Nodupₓ l) : a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l := by
  rw [d.erase_eq_filter b, mem_filter, and_comm]

theorem Nodupₓ.not_mem_erase [DecidableEq α] {a : α} {s} (h : Nodupₓ s) : a ∉ s.erase a := fun ha =>
  (h.mem_erase_iff.1 ha).1 rfl

protected theorem Nodupₓ.product {t : Multiset β} : Nodupₓ s → Nodupₓ t → Nodupₓ (product s t) :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ d₁ d₂ => by simp [d₁.product d₂]

protected theorem Nodupₓ.sigma {σ : α → Type _} {t : ∀ a, Multiset (σ a)} :
    Nodupₓ s → (∀ a, Nodupₓ (t a)) → Nodupₓ (s.Sigma t) :=
  (Quot.induction_on s) fun l₁ => by
    choose f hf using fun a => Quotientₓ.exists_rep (t a)
    rw [show t = fun a => f a from Eq.symm <| funext fun a => hf a]
    simpa using nodup.sigma

protected theorem Nodupₓ.filter_map (f : α → Option β) (H : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    Nodupₓ s → Nodupₓ (filterMap f s) :=
  (Quot.induction_on s) fun l => Nodupₓ.filter_map H

theorem nodup_range (n : ℕ) : Nodupₓ (range n) :=
  nodup_range _

theorem Nodupₓ.inter_left [DecidableEq α] (t) : Nodupₓ s → Nodupₓ (s ∩ t) :=
  nodup_of_le <| inter_le_left _ _

theorem Nodupₓ.inter_right [DecidableEq α] (s) : Nodupₓ t → Nodupₓ (s ∩ t) :=
  nodup_of_le <| inter_le_right _ _

@[simp]
theorem nodup_union [DecidableEq α] {s t : Multiset α} : Nodupₓ (s ∪ t) ↔ Nodupₓ s ∧ Nodupₓ t :=
  ⟨fun h => ⟨nodup_of_le (le_union_left _ _) h, nodup_of_le (le_union_right _ _) h⟩, fun ⟨h₁, h₂⟩ =>
    nodup_iff_count_le_one.2 fun a => by
      rw [count_union] <;> exact max_leₓ (nodup_iff_count_le_one.1 h₁ a) (nodup_iff_count_le_one.1 h₂ a)⟩

@[simp]
theorem nodup_powerset {s : Multiset α} : Nodupₓ (powerset s) ↔ Nodupₓ s :=
  ⟨fun h => (nodup_of_le (map_single_le_powerset _) h).of_map _,
    (Quotientₓ.induction_on s) fun l h => by
      simp <;>
        refine' (nodup_sublists'.2 h).map_on _ <;>
          exact fun x sx y sy e => (h.sublist_ext (mem_sublists'.1 sx) (mem_sublists'.1 sy)).1 (Quotientₓ.exact e)⟩

alias nodup_powerset ↔ nodup.of_powerset nodup.powerset

protected theorem Nodupₓ.powerset_len {n : ℕ} (h : Nodupₓ s) : Nodupₓ (powersetLen n s) :=
  nodup_of_le (powerset_len_le_powerset _ _) (nodup_powerset.2 h)

@[simp]
theorem nodup_bind {s : Multiset α} {t : α → Multiset β} :
    Nodupₓ (bind s t) ↔ (∀ a ∈ s, Nodupₓ (t a)) ∧ s.Pairwise fun a b => Disjoint (t a) (t b) :=
  have h₁ : ∀ a, ∃ l : List β, t a = l := fun a => (Quot.induction_on (t a)) fun l => ⟨l, rfl⟩
  let ⟨t', h'⟩ := Classical.axiom_of_choice h₁
  have : t = fun a => t' a := funext h'
  have hd : Symmetric fun a b => List.Disjointₓ (t' a) (t' b) := fun a b h => h.symm
  Quot.induction_on s <| by simp [this, List.nodup_bind, pairwise_coe_iff_pairwise hd]

theorem Nodupₓ.ext {s t : Multiset α} : Nodupₓ s → Nodupₓ t → (s = t ↔ ∀ a, a ∈ s ↔ a ∈ t) :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ d₁ d₂ => Quotientₓ.eq.trans <| perm_ext d₁ d₂

theorem le_iff_subset {s t : Multiset α} : Nodupₓ s → (s ≤ t ↔ s ⊆ t) :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ d => ⟨subset_of_le, d.Subperm⟩

theorem range_le {m n : ℕ} : range m ≤ range n ↔ m ≤ n :=
  (le_iff_subset (nodup_range _)).trans range_subset

theorem mem_sub_of_nodup [DecidableEq α] {a : α} {s t : Multiset α} (d : Nodupₓ s) : a ∈ s - t ↔ a ∈ s ∧ a ∉ t :=
  ⟨fun h =>
    ⟨mem_of_le tsub_le_self h, fun h' => by
      refine' count_eq_zero.1 _ h <;>
        rw [count_sub a s t, tsub_eq_zero_iff_le] <;> exact le_transₓ (nodup_iff_count_le_one.1 d _) (count_pos.2 h')⟩,
    fun ⟨h₁, h₂⟩ => Or.resolve_right (mem_add.1 <| mem_of_le le_tsub_add h₁) h₂⟩

theorem map_eq_map_of_bij_of_nodup (f : α → γ) (g : β → γ) {s : Multiset α} {t : Multiset β} (hs : s.Nodup)
    (ht : t.Nodup) (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂) (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) :
    s.map f = t.map g :=
  have : t = s.attach.map fun x => i x.1 x.2 :=
    (ht.ext <|
          (nodup_attach.2 hs).map <|
            show Injective fun x : { x // x ∈ s } => i x.1 x.2 from fun x y hxy =>
              Subtype.eq <| i_inj x.1 y.1 x.2 y.2 hxy).2
      fun x => by
      simp only [mem_map, true_andₓ, Subtype.exists, eq_comm, mem_attach] <;>
        exact ⟨i_surj _, fun ⟨y, hy⟩ => hy.snd.symm ▸ hi _ _⟩
  calc
    s.map f = s.pmap (fun x _ => f x) fun _ => id := by rw [pmap_eq_map]
    _ = s.attach.map fun x => f x.1 := by rw [pmap_eq_map_attach]
    _ = t.map g := by rw [this, Multiset.map_map] <;> exact map_congr rfl fun x _ => h _ _
    

end Multiset

