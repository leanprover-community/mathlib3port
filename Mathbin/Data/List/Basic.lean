import Mathbin.Data.Nat.Basic

/-!
# Basic properties of lists
-/


open Function Nat

namespace List

universe u v w x

variable{α : Type u}{β : Type v}{γ : Type w}{δ : Type x}

attribute [inline] List.headₓ

instance  : IsLeftId (List α) Append.append [] :=
  ⟨nil_append⟩

instance  : IsRightId (List α) Append.append [] :=
  ⟨append_nil⟩

instance  : IsAssociative (List α) Append.append :=
  ⟨append_assoc⟩

theorem cons_ne_nil (a : α) (l : List α) : a :: l ≠ [] :=
  fun.

theorem cons_ne_self (a : α) (l : List α) : a :: l ≠ l :=
  mt (congr_argₓ length) (Nat.succ_ne_self _)

theorem head_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : List α} : h₁ :: t₁ = h₂ :: t₂ → h₁ = h₂ :=
  fun Peq => List.noConfusion Peq fun Pheq Pteq => Pheq

theorem tail_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : List α} : h₁ :: t₁ = h₂ :: t₂ → t₁ = t₂ :=
  fun Peq => List.noConfusion Peq fun Pheq Pteq => Pteq

@[simp]
theorem cons_injective {a : α} : injective (cons a) :=
  fun l₁ l₂ => fun Pe => tail_eq_of_cons_eq Pe

theorem cons_inj (a : α) {l l' : List α} : a :: l = a :: l' ↔ l = l' :=
  cons_injective.eq_iff

theorem exists_cons_of_ne_nil {l : List α} (h : l ≠ nil) : ∃ b L, l = b :: L :=
  by 
    induction' l with c l' 
    contradiction 
    use c, l'

/-! ### mem -/


theorem mem_singleton_self (a : α) : a ∈ [a] :=
  mem_cons_self _ _

theorem eq_of_mem_singleton {a b : α} : a ∈ [b] → a = b :=
  fun this : a ∈ [b] =>
    Or.elim (eq_or_mem_of_mem_cons this) (fun this : a = b => this) fun this : a ∈ [] => absurd this (not_mem_nil a)

@[simp]
theorem mem_singleton {a b : α} : a ∈ [b] ↔ a = b :=
  ⟨eq_of_mem_singleton, Or.inl⟩

theorem mem_of_mem_cons_of_mem {a b : α} {l : List α} : a ∈ b :: l → b ∈ l → a ∈ l :=
  fun ainbl binl =>
    Or.elim (eq_or_mem_of_mem_cons ainbl)
      (fun this : a = b =>
        by 
          subst a 
          exact binl)
      fun this : a ∈ l => this

theorem _root_.decidable.list.eq_or_ne_mem_of_mem [DecidableEq α] {a b : α} {l : List α} (h : a ∈ b :: l) :
  a = b ∨ a ≠ b ∧ a ∈ l :=
  Decidable.byCases Or.inl$ fun this : a ≠ b => h.elim Or.inl$ fun h => Or.inr ⟨this, h⟩

theorem eq_or_ne_mem_of_mem {a b : α} {l : List α} : a ∈ b :: l → a = b ∨ a ≠ b ∧ a ∈ l :=
  by 
    classical <;> exact Decidable.List.eq_or_ne_mem_of_mem

theorem not_mem_append {a : α} {s t : List α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t :=
  mt mem_append.1$ not_or_distrib.2 ⟨h₁, h₂⟩

theorem ne_nil_of_mem {a : α} {l : List α} (h : a ∈ l) : l ≠ [] :=
  by 
    intro e <;> rw [e] at h <;> cases h

theorem mem_split {a : α} {l : List α} (h : a ∈ l) : ∃ s t : List α, l = s ++ a :: t :=
  by 
    induction' l with b l ih
    ·
      cases h 
    rcases h with (rfl | h)
    ·
      exact ⟨[], l, rfl⟩
    ·
      rcases ih h with ⟨s, t, rfl⟩
      exact ⟨b :: s, t, rfl⟩

theorem mem_of_ne_of_mem {a y : α} {l : List α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
  Or.elim (eq_or_mem_of_mem_cons h₂) (fun e => absurd e h₁) fun r => r

theorem ne_of_not_mem_cons {a b : α} {l : List α} : a ∉ b :: l → a ≠ b :=
  fun nin aeqb => absurd (Or.inl aeqb) nin

theorem not_mem_of_not_mem_cons {a b : α} {l : List α} : a ∉ b :: l → a ∉ l :=
  fun nin nainl => absurd (Or.inr nainl) nin

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} : a ≠ y → a ∉ l → a ∉ y :: l :=
  fun p1 p2 => Not.intro fun Pain => absurd (eq_or_mem_of_mem_cons Pain) (not_orₓ p1 p2)

theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : List α} : a ∉ y :: l → a ≠ y ∧ a ∉ l :=
  fun p => And.intro (ne_of_not_mem_cons p) (not_mem_of_not_mem_cons p)

@[simp]
theorem mem_map {f : α → β} {b : β} {l : List α} : b ∈ map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
  by 
    induction' l with a l ihl
    ·
      split 
      ·
        rintro ⟨_⟩
      ·
        rintro ⟨a, ⟨_⟩, _⟩
    ·
      refine' (or_congr eq_comm ihl).trans _ 
      split 
      ·
        rintro (h | ⟨c, hcl, h⟩)
        exacts[⟨a, Or.inl rfl, h⟩, ⟨c, Or.inr hcl, h⟩]
      ·
        rintro ⟨c, hc | hc, h⟩
        exacts[Or.inl$ (congr_argₓ f hc.symm).trans h, Or.inr ⟨c, hc, h⟩]

alias mem_map ↔ List.exists_of_mem_mapₓ _

theorem mem_map_of_mem (f : α → β) {a : α} {l : List α} (h : a ∈ l) : f a ∈ map f l :=
  mem_map.2 ⟨a, h, rfl⟩

theorem mem_map_of_injective {f : α → β} (H : injective f) {a : α} {l : List α} : f a ∈ map f l ↔ a ∈ l :=
  ⟨fun m =>
      let ⟨a', m', e⟩ := exists_of_mem_map m 
      H e ▸ m',
    mem_map_of_mem _⟩

theorem forall_mem_map_iff {f : α → β} {l : List α} {P : β → Prop} :
  (∀ i (_ : i ∈ l.map f), P i) ↔ ∀ j (_ : j ∈ l), P (f j) :=
  by 
    split 
    ·
      intro H j hj 
      exact H (f j) (mem_map_of_mem f hj)
    ·
      intro H i hi 
      rcases mem_map.1 hi with ⟨j, hj, ji⟩
      rw [←ji]
      exact H j hj

@[simp]
theorem map_eq_nil {f : α → β} {l : List α} : List.map f l = [] ↔ l = [] :=
  ⟨by 
      cases l <;> simp only [forall_prop_of_true, map, forall_prop_of_false, not_false_iff],
    fun h => h.symm ▸ rfl⟩

@[simp]
theorem mem_join {a : α} : ∀ {L : List (List α)}, a ∈ join L ↔ ∃ l, l ∈ L ∧ a ∈ l
| [] => ⟨False.elim, fun ⟨_, h, _⟩ => False.elim h⟩
| c :: L =>
  by 
    simp only [join, mem_append, @mem_join L, mem_cons_iff, or_and_distrib_right, exists_or_distrib, exists_eq_left]

theorem exists_of_mem_join {a : α} {L : List (List α)} : a ∈ join L → ∃ l, l ∈ L ∧ a ∈ l :=
  mem_join.1

theorem mem_join_of_mem {a : α} {L : List (List α)} {l} (lL : l ∈ L) (al : a ∈ l) : a ∈ join L :=
  mem_join.2 ⟨l, lL, al⟩

@[simp]
theorem mem_bind {b : β} {l : List α} {f : α → List β} : b ∈ List.bind l f ↔ ∃ (a : _)(_ : a ∈ l), b ∈ f a :=
  Iff.trans mem_join
    ⟨fun ⟨l', h1, h2⟩ =>
        let ⟨a, al, fa⟩ := exists_of_mem_map h1
        ⟨a, al, fa.symm ▸ h2⟩,
      fun ⟨a, al, bfa⟩ => ⟨f a, mem_map_of_mem _ al, bfa⟩⟩

theorem exists_of_mem_bind {b : β} {l : List α} {f : α → List β} : b ∈ List.bind l f → ∃ (a : _)(_ : a ∈ l), b ∈ f a :=
  mem_bind.1

theorem mem_bind_of_mem {b : β} {l : List α} {f : α → List β} {a} (al : a ∈ l) (h : b ∈ f a) : b ∈ List.bind l f :=
  mem_bind.2 ⟨a, al, h⟩

theorem bind_map {g : α → List β} {f : β → γ} : ∀ (l : List α), List.map f (l.bind g) = l.bind fun a => (g a).map f
| [] => rfl
| a :: l =>
  by 
    simp only [cons_bind, map_append, bind_map l]

theorem map_bind (g : β → List γ) (f : α → β) : ∀ (l : List α), (List.map f l).bind g = l.bind fun a => g (f a)
| [] => rfl
| a :: l =>
  by 
    simp only [cons_bind, map_cons, map_bind l]

/-- If each element of a list can be lifted to some type, then the whole list can be lifted to this
type. -/
instance  [h : CanLift α β] : CanLift (List α) (List β) :=
  { coe := List.map h.coe, cond := fun l => ∀ x (_ : x ∈ l), CanLift.Cond β x,
    prf :=
      fun l H =>
        by 
          induction' l with a l ihl
          ·
            exact ⟨[], rfl⟩
          rcases ihl fun x hx => H x (Or.inr hx) with ⟨l, rfl⟩
          rcases CanLift.prf a (H a (Or.inl rfl)) with ⟨a, rfl⟩
          exact ⟨a :: l, rfl⟩ }

/-! ### length -/


theorem length_eq_zero {l : List α} : length l = 0 ↔ l = [] :=
  ⟨eq_nil_of_length_eq_zero, fun h => h.symm ▸ rfl⟩

@[simp]
theorem length_singleton (a : α) : length [a] = 1 :=
  rfl

theorem length_pos_of_mem {a : α} : ∀ {l : List α}, a ∈ l → 0 < length l
| b :: l, _ => zero_lt_succ _

theorem exists_mem_of_length_pos : ∀ {l : List α}, 0 < length l → ∃ a, a ∈ l
| b :: l, _ => ⟨b, mem_cons_self _ _⟩

theorem length_pos_iff_exists_mem {l : List α} : 0 < length l ↔ ∃ a, a ∈ l :=
  ⟨exists_mem_of_length_pos, fun ⟨a, h⟩ => length_pos_of_mem h⟩

theorem ne_nil_of_length_pos {l : List α} : 0 < length l → l ≠ [] :=
  fun h1 h2 => lt_irreflₓ 0 ((length_eq_zero.2 h2).subst h1)

theorem length_pos_of_ne_nil {l : List α} : l ≠ [] → 0 < length l :=
  fun h => pos_iff_ne_zero.2$ fun h0 => h$ length_eq_zero.1 h0

theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l ≠ [] :=
  ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩

theorem exists_mem_of_ne_nil (l : List α) (h : l ≠ []) : ∃ x, x ∈ l :=
  exists_mem_of_length_pos (length_pos_of_ne_nil h)

theorem length_eq_one {l : List α} : length l = 1 ↔ ∃ a, l = [a] :=
  ⟨match l with 
    | [a], _ => ⟨a, rfl⟩,
    fun ⟨a, e⟩ => e.symm ▸ rfl⟩

theorem exists_of_length_succ {n} : ∀ (l : List α), (l.length = n+1) → ∃ h t, l = h :: t
| [], H => absurd H.symm$ succ_ne_zero n
| h :: t, H => ⟨h, t, rfl⟩

@[simp]
theorem length_injective_iff : injective (List.length : List α → ℕ) ↔ Subsingleton α :=
  by 
    split 
    ·
      intro h 
      refine' ⟨fun x y => _⟩
      suffices  : [x] = [y]
      ·
        simpa using this 
      apply h 
      rfl
    ·
      intro hα l1 l2 hl 
      induction l1 generalizing l2 <;> cases l2
      ·
        rfl
      ·
        cases hl
      ·
        cases hl 
      congr 
      exact Subsingleton.elimₓ _ _ 
      apply l1_ih 
      simpa using hl

@[simp]
theorem length_injective [Subsingleton α] : injective (length : List α → ℕ) :=
  length_injective_iff.mpr$
    by 
      infer_instance

theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b, l = [a, b] :=
  ⟨match l with 
    | [a, b], _ => ⟨a, b, rfl⟩,
    fun ⟨a, b, e⟩ => e.symm ▸ rfl⟩

theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] :=
  ⟨match l with 
    | [a, b, c], _ => ⟨a, b, c, rfl⟩,
    fun ⟨a, b, c, e⟩ => e.symm ▸ rfl⟩

/-! ### set-theoretic notation of lists -/


theorem empty_eq : (∅ : List α) = [] :=
  by 
    rfl

theorem singleton_eq (x : α) : ({x} : List α) = [x] :=
  rfl

theorem insert_neg [DecidableEq α] {x : α} {l : List α} (h : x ∉ l) : HasInsert.insert x l = x :: l :=
  if_neg h

theorem insert_pos [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) : HasInsert.insert x l = l :=
  if_pos h

theorem doubleton_eq [DecidableEq α] {x y : α} (h : x ≠ y) : ({x, y} : List α) = [x, y] :=
  by 
    rw [insert_neg, singleton_eq]
    rwa [singleton_eq, mem_singleton]

/-! ### bounded quantifiers over lists -/


theorem forall_mem_nil (p : α → Prop) : ∀ x (_ : x ∈ @nil α), p x :=
  fun.

theorem forall_mem_cons :
  ∀ {p : α → Prop} {a : α} {l : List α}, (∀ x (_ : x ∈ a :: l), p x) ↔ p a ∧ ∀ x (_ : x ∈ l), p x :=
  ball_cons

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : List α} (h : ∀ x (_ : x ∈ a :: l), p x) :
  ∀ x (_ : x ∈ l), p x :=
  (forall_mem_cons.1 h).2

theorem forall_mem_singleton {p : α → Prop} {a : α} : (∀ x (_ : x ∈ [a]), p x) ↔ p a :=
  by 
    simp only [mem_singleton, forall_eq]

theorem forall_mem_append {p : α → Prop} {l₁ l₂ : List α} :
  (∀ x (_ : x ∈ l₁ ++ l₂), p x) ↔ (∀ x (_ : x ∈ l₁), p x) ∧ ∀ x (_ : x ∈ l₂), p x :=
  by 
    simp only [mem_append, or_imp_distrib, forall_and_distrib]

theorem not_exists_mem_nil (p : α → Prop) : ¬∃ (x : _)(_ : x ∈ @nil α), p x :=
  fun.

theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) : ∃ (x : _)(_ : x ∈ a :: l), p x :=
  Bex.intro a (mem_cons_self _ _) h

theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : List α} (h : ∃ (x : _)(_ : x ∈ l), p x) :
  ∃ (x : _)(_ : x ∈ a :: l), p x :=
  Bex.elim h fun x xl px => Bex.intro x (mem_cons_of_mem _ xl) px

theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : List α} (h : ∃ (x : _)(_ : x ∈ a :: l), p x) :
  p a ∨ ∃ (x : _)(_ : x ∈ l), p x :=
  Bex.elim h
    fun x xal px =>
      Or.elim (eq_or_mem_of_mem_cons xal)
        (fun this : x = a =>
          by 
            rw [←this]
            left 
            exact px)
        fun this : x ∈ l => Or.inr (Bex.intro x this px)

theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : List α) :
  (∃ (x : _)(_ : x ∈ a :: l), p x) ↔ p a ∨ ∃ (x : _)(_ : x ∈ l), p x :=
  Iff.intro or_exists_of_exists_mem_cons fun h => Or.elim h (exists_mem_cons_of l) exists_mem_cons_of_exists

/-! ### list subset -/


theorem subset_def {l₁ l₂ : List α} : l₁ ⊆ l₂ ↔ ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂ :=
  Iff.rfl

theorem subset_append_of_subset_left (l l₁ l₂ : List α) : l ⊆ l₁ → l ⊆ l₁ ++ l₂ :=
  fun s => subset.trans s$ subset_append_left _ _

theorem subset_append_of_subset_right (l l₁ l₂ : List α) : l ⊆ l₂ → l ⊆ l₁ ++ l₂ :=
  fun s => subset.trans s$ subset_append_right _ _

@[simp]
theorem cons_subset {a : α} {l m : List α} : a :: l ⊆ m ↔ a ∈ m ∧ l ⊆ m :=
  by 
    simp only [subset_def, mem_cons_iff, or_imp_distrib, forall_and_distrib, forall_eq]

theorem cons_subset_of_subset_of_mem {a : α} {l m : List α} (ainm : a ∈ m) (lsubm : l ⊆ m) : a :: l ⊆ m :=
  cons_subset.2 ⟨ainm, lsubm⟩

theorem append_subset_of_subset_of_subset {l₁ l₂ l : List α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) : l₁ ++ l₂ ⊆ l :=
  fun a h => (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)

@[simp]
theorem append_subset_iff {l₁ l₂ l : List α} : l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l :=
  by 
    split 
    ·
      intro h 
      simp only [subset_def] at *
      split  <;> intros  <;> simp 
    ·
      rintro ⟨h1, h2⟩
      apply append_subset_of_subset_of_subset h1 h2

theorem eq_nil_of_subset_nil : ∀ {l : List α}, l ⊆ [] → l = []
| [], s => rfl
| a :: l, s => False.elim$ s$ mem_cons_self a l

theorem eq_nil_iff_forall_not_mem {l : List α} : l = [] ↔ ∀ a, a ∉ l :=
  show l = [] ↔ l ⊆ [] from ⟨fun e => e ▸ subset.refl _, eq_nil_of_subset_nil⟩

theorem map_subset {l₁ l₂ : List α} (f : α → β) (H : l₁ ⊆ l₂) : map f l₁ ⊆ map f l₂ :=
  fun x =>
    by 
      simp only [mem_map, not_and, exists_imp_distrib, and_imp] <;> exact fun a h e => ⟨a, H h, e⟩

theorem map_subset_iff {l₁ l₂ : List α} (f : α → β) (h : injective f) : map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ :=
  by 
    refine' ⟨_, map_subset f⟩
    intro h2 x hx 
    rcases mem_map.1 (h2 (mem_map_of_mem f hx)) with ⟨x', hx', hxx'⟩
    cases h hxx' 
    exact hx'

/-! ### append -/


theorem append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂ :=
  rfl

@[simp]
theorem singleton_append {x : α} {l : List α} : [x] ++ l = x :: l :=
  rfl

theorem append_ne_nil_of_ne_nil_left (s t : List α) : s ≠ [] → s ++ t ≠ [] :=
  by 
    induction s <;> intros  <;> contradiction

theorem append_ne_nil_of_ne_nil_right (s t : List α) : t ≠ [] → s ++ t ≠ [] :=
  by 
    induction s <;> intros  <;> contradiction

@[simp]
theorem append_eq_nil {p q : List α} : p ++ q = [] ↔ p = [] ∧ q = [] :=
  by 
    cases p <;> simp only [nil_append, cons_append, eq_self_iff_true, true_andₓ, false_andₓ]

@[simp]
theorem nil_eq_append_iff {a b : List α} : [] = a ++ b ↔ a = [] ∧ b = [] :=
  by 
    rw [eq_comm, append_eq_nil]

theorem append_eq_cons_iff {a b c : List α} {x : α} :
  a ++ b = x :: c ↔ a = [] ∧ b = x :: c ∨ ∃ a', a = x :: a' ∧ c = a' ++ b :=
  by 
    cases a <;>
      simp only [and_assoc, @eq_comm _ c, nil_append, cons_append, eq_self_iff_true, true_andₓ, false_andₓ,
        exists_false, false_orₓ, or_falseₓ, exists_and_distrib_left, exists_eq_left']

theorem cons_eq_append_iff {a b c : List α} {x : α} :
  (x :: c : List α) = a ++ b ↔ a = [] ∧ b = x :: c ∨ ∃ a', a = x :: a' ∧ c = a' ++ b :=
  by 
    rw [eq_comm, append_eq_cons_iff]

theorem append_eq_append_iff {a b c d : List α} :
  a ++ b = c ++ d ↔ (∃ a', c = a ++ a' ∧ b = a' ++ d) ∨ ∃ c', a = c ++ c' ∧ d = c' ++ b :=
  by 
    induction a generalizing c 
    case nil => 
      rw [nil_append]
      split 
      ·
        rintro rfl 
        left 
        exact ⟨_, rfl, rfl⟩
      ·
        rintro (⟨a', rfl, rfl⟩ | ⟨a', H, rfl⟩)
        ·
          rfl
        ·
          rw [←append_assoc, ←H]
          rfl 
    case cons a as ih => 
      cases c
      ·
        simp only [cons_append, nil_append, false_andₓ, exists_false, false_orₓ, exists_eq_left']
        exact eq_comm
      ·
        simp only [cons_append, @eq_comm _ a, ih, and_assoc, and_or_distrib_left, exists_and_distrib_left]

@[simp]
theorem take_append_drop : ∀ (n : ℕ) (l : List α), take n l ++ drop n l = l
| 0, a => rfl
| succ n, [] => rfl
| succ n, x :: xs => congr_argₓ (cons x)$ take_append_drop n xs

theorem append_inj : ∀ {s₁ s₂ t₁ t₂ : List α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
| [], [], t₁, t₂, h, hl => ⟨rfl, h⟩
| a :: s₁, [], t₁, t₂, h, hl => List.noConfusion$ eq_nil_of_length_eq_zero hl
| [], b :: s₂, t₁, t₂, h, hl => List.noConfusion$ eq_nil_of_length_eq_zero hl.symm
| a :: s₁, b :: s₂, t₁, t₂, h, hl =>
  List.noConfusion h$
    fun ab hap =>
      let ⟨e1, e2⟩ := @append_inj s₁ s₂ t₁ t₂ hap (succ.inj hl)
      by 
        rw [ab, e1, e2] <;> exact ⟨rfl, rfl⟩

theorem append_inj_right {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : t₁ = t₂ :=
  (append_inj h hl).right

theorem append_inj_left {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length s₁ = length s₂) : s₁ = s₂ :=
  (append_inj h hl).left

theorem append_inj' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ ∧ t₁ = t₂ :=
  append_inj h$
    @Nat.add_right_cancel _ (length t₁) _$
      let hap := congr_argₓ length h 
      by 
        simp only [length_append] at hap <;> rwa [←hl] at hap

theorem append_inj_right' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : t₁ = t₂ :=
  (append_inj' h hl).right

theorem append_inj_left' {s₁ s₂ t₁ t₂ : List α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) : s₁ = s₂ :=
  (append_inj' h hl).left

theorem append_left_cancel {s t₁ t₂ : List α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ :=
  append_inj_right h rfl

theorem append_right_cancel {s₁ s₂ t : List α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ :=
  append_inj_left' h rfl

theorem append_right_injective (s : List α) : Function.Injective fun t => s ++ t :=
  fun t₁ t₂ => append_left_cancel

theorem append_right_inj {t₁ t₂ : List α} s : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
  (append_right_injective s).eq_iff

theorem append_left_injective (t : List α) : Function.Injective fun s => s ++ t :=
  fun s₁ s₂ => append_right_cancel

theorem append_left_inj {s₁ s₂ : List α} t : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
  (append_left_injective t).eq_iff

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_eq_append_split
{f : α → β}
{l : list α}
{s₁ s₂ : list β}
(h : «expr = »(map f l, «expr ++ »(s₁, s₂))) : «expr∃ , »((l₁
  l₂), «expr ∧ »(«expr = »(l, «expr ++ »(l₁, l₂)), «expr ∧ »(«expr = »(map f l₁, s₁), «expr = »(map f l₂, s₂)))) :=
begin
  have [] [] [":=", expr h],
  rw ["[", "<-", expr take_append_drop (length s₁) l, "]"] ["at", ident this, "⊢"],
  rw [expr map_append] ["at", ident this],
  refine [expr ⟨_, _, rfl, append_inj this _⟩],
  rw ["[", expr length_map, ",", expr length_take, ",", expr min_eq_left, "]"] [],
  rw ["[", "<-", expr length_map f l, ",", expr h, ",", expr length_append, "]"] [],
  apply [expr nat.le_add_right]
end

/-! ### repeat -/


@[simp]
theorem repeat_succ (a : α) n : repeat a (n+1) = a :: repeat a n :=
  rfl

theorem mem_repeat {a b : α} : ∀ {n}, b ∈ repeat a n ↔ n ≠ 0 ∧ b = a
| 0 =>
  by 
    simp 
| n+1 =>
  by 
    simp [mem_repeat]

theorem eq_of_mem_repeat {a b : α} {n} (h : b ∈ repeat a n) : b = a :=
  (mem_repeat.1 h).2

theorem eq_repeat_of_mem {a : α} : ∀ {l : List α}, (∀ b (_ : b ∈ l), b = a) → l = repeat a l.length
| [], H => rfl
| b :: l, H =>
  by 
    cases' forall_mem_cons.1 H with H₁ H₂ <;> unfold length repeat <;> congr <;> [exact H₁, exact eq_repeat_of_mem H₂]

theorem eq_repeat' {a : α} {l : List α} : l = repeat a l.length ↔ ∀ b (_ : b ∈ l), b = a :=
  ⟨fun h => h.symm ▸ fun b => eq_of_mem_repeat, eq_repeat_of_mem⟩

theorem eq_repeat {a : α} {n} {l : List α} : l = repeat a n ↔ length l = n ∧ ∀ b (_ : b ∈ l), b = a :=
  ⟨fun h => h.symm ▸ ⟨length_repeat _ _, fun b => eq_of_mem_repeat⟩, fun ⟨e, al⟩ => e ▸ eq_repeat_of_mem al⟩

theorem repeat_add (a : α) m n : repeat a (m+n) = repeat a m ++ repeat a n :=
  by 
    induction m <;> simp only [zero_addₓ, succ_add, repeat] <;> split  <;> rfl

theorem repeat_subset_singleton (a : α) n : repeat a n ⊆ [a] :=
  fun b h => mem_singleton.2 (eq_of_mem_repeat h)

@[simp]
theorem map_const (l : List α) (b : β) : map (Function.const α b) l = repeat b l.length :=
  by 
    induction l <;> [rfl, simp only [map]] <;> split  <;> rfl

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (Function.const α b₂) l) : b₁ = b₂ :=
  by 
    rw [map_const] at h <;> exact eq_of_mem_repeat h

@[simp]
theorem map_repeat (f : α → β) (a : α) n : map f (repeat a n) = repeat (f a) n :=
  by 
    induction n <;> [rfl, simp only [repeat, map]] <;> split  <;> rfl

@[simp]
theorem tail_repeat (a : α) n : tail (repeat a n) = repeat a n.pred :=
  by 
    cases n <;> rfl

@[simp]
theorem join_repeat_nil (n : ℕ) : join (repeat [] n) = @nil α :=
  by 
    induction n <;> [rfl, simp only [repeat, join, append_nil]]

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem repeat_left_injective {n : exprℕ()} (hn : «expr ≠ »(n, 0)) : function.injective (λ a : α, repeat a n) :=
λ a b h, «expr $ »((eq_repeat.1 h).2 _, mem_repeat.2 ⟨hn, rfl⟩)

theorem repeat_left_inj {a b : α} {n : ℕ} (hn : n ≠ 0) : repeat a n = repeat b n ↔ a = b :=
  (repeat_left_injective hn).eq_iff

@[simp]
theorem repeat_left_inj' {a b : α} : ∀ {n}, repeat a n = repeat b n ↔ n = 0 ∨ a = b
| 0 =>
  by 
    simp 
| n+1 =>
  (repeat_left_inj n.succ_ne_zero).trans$
    by 
      simp only [n.succ_ne_zero, false_orₓ]

theorem repeat_right_injective (a : α) : Function.Injective (repeat a) :=
  Function.LeftInverse.injective (length_repeat a)

@[simp]
theorem repeat_right_inj {a : α} {n m : ℕ} : repeat a n = repeat a m ↔ n = m :=
  (repeat_right_injective a).eq_iff

/-! ### pure -/


@[simp]
theorem mem_pure {α} (x y : α) : x ∈ (pure y : List α) ↔ x = y :=
  by 
    simp [pure, List.ret]

/-! ### bind -/


@[simp]
theorem bind_eq_bind {α β} (f : α → List β) (l : List α) : l >>= f = l.bind f :=
  rfl

theorem bind_append (f : α → List β) (l₁ l₂ : List α) : (l₁ ++ l₂).bind f = l₁.bind f ++ l₂.bind f :=
  append_bind _ _ _

@[simp]
theorem bind_singleton (f : α → List β) (x : α) : [x].bind f = f x :=
  append_nil (f x)

@[simp]
theorem bind_singleton' (l : List α) : (l.bind fun x => [x]) = l :=
  bind_pureₓ l

theorem map_eq_bind {α β} (f : α → β) (l : List α) : map f l = l.bind fun x => [f x] :=
  by 
    trans 
    rw [←bind_singleton' l, bind_map]
    rfl

theorem bind_assoc {α β} (l : List α) (f : α → List β) (g : β → List γ) :
  (l.bind f).bind g = l.bind fun x => (f x).bind g :=
  by 
    induction l <;> simp 

/-! ### concat -/


theorem concat_nil (a : α) : concat [] a = [a] :=
  rfl

theorem concat_cons (a b : α) (l : List α) : concat (a :: l) b = a :: concat l b :=
  rfl

@[simp]
theorem concat_eq_append (a : α) (l : List α) : concat l a = l ++ [a] :=
  by 
    induction l <;> simp only [concat] <;> split  <;> rfl

theorem init_eq_of_concat_eq {a : α} {l₁ l₂ : List α} : concat l₁ a = concat l₂ a → l₁ = l₂ :=
  by 
    intro h 
    rw [concat_eq_append, concat_eq_append] at h 
    exact append_right_cancel h

theorem last_eq_of_concat_eq {a b : α} {l : List α} : concat l a = concat l b → a = b :=
  by 
    intro h 
    rw [concat_eq_append, concat_eq_append] at h 
    exact head_eq_of_cons_eq (append_left_cancel h)

theorem concat_ne_nil (a : α) (l : List α) : concat l a ≠ [] :=
  by 
    simp 

theorem concat_append (a : α) (l₁ l₂ : List α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ :=
  by 
    simp 

theorem length_concat (a : α) (l : List α) : length (concat l a) = succ (length l) :=
  by 
    simp only [concat_eq_append, length_append, length]

theorem append_concat (a : α) (l₁ l₂ : List α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a :=
  by 
    simp 

/-! ### reverse -/


@[simp]
theorem reverse_nil : reverse (@nil α) = [] :=
  rfl

attribute [local simp] reverse_core

@[simp]
theorem reverse_cons (a : α) (l : List α) : reverse (a :: l) = reverse l ++ [a] :=
  have aux : ∀ l₁ l₂, reverse_core l₁ l₂ ++ [a] = reverse_core l₁ (l₂ ++ [a]) :=
    by 
      intro l₁ <;> induction l₁ <;> intros  <;> [rfl, simp only [reverse_core, cons_append]]
  (aux l nil).symm

theorem reverse_core_eq (l₁ l₂ : List α) : reverse_core l₁ l₂ = reverse l₁ ++ l₂ :=
  by 
    induction l₁ generalizing l₂ <;> [rfl, simp only [reverse_core, reverse_cons, append_assoc]] <;> rfl

theorem reverse_cons' (a : α) (l : List α) : reverse (a :: l) = concat (reverse l) a :=
  by 
    simp only [reverse_cons, concat_eq_append]

@[simp]
theorem reverse_singleton (a : α) : reverse [a] = [a] :=
  rfl

@[simp]
theorem reverse_append (s t : List α) : reverse (s ++ t) = reverse t ++ reverse s :=
  by 
    induction s <;> [rw [nil_append, reverse_nil, append_nil], simp only [cons_append, reverse_cons, append_assoc]]

theorem reverse_concat (l : List α) (a : α) : reverse (concat l a) = a :: reverse l :=
  by 
    rw [concat_eq_append, reverse_append, reverse_singleton, singleton_append]

@[simp]
theorem reverse_reverse (l : List α) : reverse (reverse l) = l :=
  by 
    induction l <;> [rfl, simp only [reverse_cons, reverse_append]] <;> rfl

@[simp]
theorem reverse_involutive : involutive (@reverse α) :=
  fun l => reverse_reverse l

@[simp]
theorem reverse_injective : injective (@reverse α) :=
  reverse_involutive.Injective

@[simp]
theorem reverse_inj {l₁ l₂ : List α} : reverse l₁ = reverse l₂ ↔ l₁ = l₂ :=
  reverse_injective.eq_iff

theorem reverse_eq_iff {l l' : List α} : l.reverse = l' ↔ l = l'.reverse :=
  reverse_involutive.eq_iff

@[simp]
theorem reverse_eq_nil {l : List α} : reverse l = [] ↔ l = [] :=
  @reverse_inj _ l []

theorem concat_eq_reverse_cons (a : α) (l : List α) : concat l a = reverse (a :: reverse l) :=
  by 
    simp only [concat_eq_append, reverse_cons, reverse_reverse]

@[simp]
theorem length_reverse (l : List α) : length (reverse l) = length l :=
  by 
    induction l <;> [rfl, simp only [reverse_cons, length_append, length]]

@[simp]
theorem map_reverse (f : α → β) (l : List α) : map f (reverse l) = reverse (map f l) :=
  by 
    induction l <;> [rfl, simp only [map, reverse_cons, map_append]]

theorem map_reverse_core (f : α → β) (l₁ l₂ : List α) :
  map f (reverse_core l₁ l₂) = reverse_core (map f l₁) (map f l₂) :=
  by 
    simp only [reverse_core_eq, map_append, map_reverse]

@[simp]
theorem mem_reverse {a : α} {l : List α} : a ∈ reverse l ↔ a ∈ l :=
  by 
    induction l <;> [rfl,
      simp only [reverse_cons, mem_append, mem_singleton, mem_cons_iff, not_mem_nil, false_orₓ, or_falseₓ, or_comm]]

@[simp]
theorem reverse_repeat (a : α) n : reverse (repeat a n) = repeat a n :=
  eq_repeat.2
    ⟨by 
        simp only [length_reverse, length_repeat],
      fun b h => eq_of_mem_repeat (mem_reverse.1 h)⟩

/-! ### empty -/


attribute [simp] List.empty

theorem empty_iff_eq_nil {l : List α} : l.empty ↔ l = [] :=
  List.casesOn l
    (by 
      simp )
    (by 
      simp )

/-! ### init -/


@[simp]
theorem length_init : ∀ (l : List α), length (init l) = length l - 1
| [] => rfl
| [a] => rfl
| a :: b :: l =>
  by 
    rw [init]
    simp only [add_left_injₓ, length, succ_add_sub_one]
    exact length_init (b :: l)

/-! ### last -/


@[simp]
theorem last_cons {a : α} {l : List α} : ∀ (h₁ : a :: l ≠ nil) (h₂ : l ≠ nil), last (a :: l) h₁ = last l h₂ :=
  by 
    induction l <;> intros 
    contradiction 
    rfl

@[simp]
theorem last_append {a : α} (l : List α) (h : l ++ [a] ≠ []) : last (l ++ [a]) h = a :=
  by 
    induction l <;> [rfl, simp only [cons_append, last_cons _ fun H => cons_ne_nil _ _ (append_eq_nil.1 H).2]]

theorem last_concat {a : α} (l : List α) (h : concat l a ≠ []) : last (concat l a) h = a :=
  by 
    simp only [concat_eq_append, last_append]

@[simp]
theorem last_singleton (a : α) (h : [a] ≠ []) : last [a] h = a :=
  rfl

@[simp]
theorem last_cons_cons (a₁ a₂ : α) (l : List α) (h : a₁ :: a₂ :: l ≠ []) :
  last (a₁ :: a₂ :: l) h = last (a₂ :: l) (cons_ne_nil a₂ l) :=
  rfl

theorem init_append_last : ∀ {l : List α} (h : l ≠ []), init l ++ [last l h] = l
| [], h => absurd rfl h
| [a], h => rfl
| a :: b :: l, h =>
  by 
    rw [init, cons_append, last_cons (cons_ne_nil _ _) (cons_ne_nil _ _)]
    congr 
    exact init_append_last (cons_ne_nil b l)

theorem last_congr {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) : last l₁ h₁ = last l₂ h₂ :=
  by 
    subst l₁

theorem last_mem : ∀ {l : List α} (h : l ≠ []), last l h ∈ l
| [], h => absurd rfl h
| [a], h => Or.inl rfl
| a :: b :: l, h =>
  Or.inr$
    by 
      rw [last_cons_cons]
      exact last_mem (cons_ne_nil b l)

theorem last_repeat_succ (a m : ℕ) :
  (repeat a m.succ).last
      (ne_nil_of_length_eq_succ
        (show (repeat a m.succ).length = m.succ by 
          rw [length_repeat])) =
    a :=
  by 
    induction' m with k IH
    ·
      simp 
    ·
      simpa only [repeat_succ, last]

/-! ### last' -/


@[simp]
theorem last'_is_none : ∀ {l : List α}, (last' l).isNone ↔ l = []
| [] =>
  by 
    simp 
| [a] =>
  by 
    simp 
| a :: b :: l =>
  by 
    simp [@last'_is_none (b :: l)]

@[simp]
theorem last'_is_some : ∀ {l : List α}, l.last'.is_some ↔ l ≠ []
| [] =>
  by 
    simp 
| [a] =>
  by 
    simp 
| a :: b :: l =>
  by 
    simp [@last'_is_some (b :: l)]

theorem mem_last'_eq_last : ∀ {l : List α} {x : α}, x ∈ l.last' → ∃ h, x = last l h
| [], x, hx =>
  False.elim$
    by 
      simpa using hx
| [a], x, hx =>
  have  : a = x :=
    by 
      simpa using hx 
  this ▸ ⟨cons_ne_nil a [], rfl⟩
| a :: b :: l, x, hx =>
  by 
    rw [last'] at hx 
    rcases mem_last'_eq_last hx with ⟨h₁, h₂⟩
    use cons_ne_nil _ _ 
    rwa [last_cons]

theorem last'_eq_last_of_ne_nil : ∀ {l : List α} (h : l ≠ []), l.last' = some (l.last h)
| [], h => (h rfl).elim
| [a], _ =>
  by 
    unfold last 
    unfold last'
| a :: b :: l, _ => @last'_eq_last_of_ne_nil (b :: l) (cons_ne_nil _ _)

theorem mem_last'_cons {x y : α} : ∀ {l : List α} (h : x ∈ l.last'), x ∈ (y :: l).last'
| [], _ =>
  by 
    contradiction
| a :: l, h => h

theorem mem_of_mem_last' {l : List α} {a : α} (ha : a ∈ l.last') : a ∈ l :=
  let ⟨h₁, h₂⟩ := mem_last'_eq_last ha 
  h₂.symm ▸ last_mem _

theorem init_append_last' : ∀ {l : List α} a (_ : a ∈ l.last'), init l ++ [a] = l
| [], a, ha => (Option.not_mem_none a ha).elim
| [a], _, rfl => rfl
| a :: b :: l, c, hc =>
  by 
    rw [last'] at hc 
    rw [init, cons_append, init_append_last' _ hc]

theorem ilast_eq_last' [Inhabited α] : ∀ (l : List α), l.ilast = l.last'.iget
| [] =>
  by 
    simp [ilast, arbitraryₓ]
| [a] => rfl
| [a, b] => rfl
| [a, b, c] => rfl
| a :: b :: c :: l =>
  by 
    simp [ilast, ilast_eq_last' (c :: l)]

@[simp]
theorem last'_append_cons : ∀ (l₁ : List α) (a : α) (l₂ : List α), last' (l₁ ++ a :: l₂) = last' (a :: l₂)
| [], a, l₂ => rfl
| [b], a, l₂ => rfl
| b :: c :: l₁, a, l₂ =>
  by 
    rw [cons_append, cons_append, last', ←cons_append, last'_append_cons]

@[simp]
theorem last'_cons_cons (x y : α) (l : List α) : last' (x :: y :: l) = last' (y :: l) :=
  rfl

theorem last'_append_of_ne_nil (l₁ : List α) : ∀ {l₂ : List α} (hl₂ : l₂ ≠ []), last' (l₁ ++ l₂) = last' l₂
| [], hl₂ =>
  by 
    contradiction
| b :: l₂, _ => last'_append_cons l₁ b l₂

/-! ### head(') and tail -/


theorem head_eq_head' [Inhabited α] (l : List α) : head l = (head' l).iget :=
  by 
    cases l <;> rfl

theorem mem_of_mem_head' {x : α} : ∀ {l : List α}, x ∈ l.head' → x ∈ l
| [], h => (Option.not_mem_none _ h).elim
| a :: l, h =>
  by 
    simp only [head', Option.mem_def] at h 
    exact h ▸ Or.inl rfl

@[simp]
theorem head_cons [Inhabited α] (a : α) (l : List α) : head (a :: l) = a :=
  rfl

@[simp]
theorem tail_nil : tail (@nil α) = [] :=
  rfl

@[simp]
theorem tail_cons (a : α) (l : List α) : tail (a :: l) = l :=
  rfl

@[simp]
theorem head_append [Inhabited α] (t : List α) {s : List α} (h : s ≠ []) : head (s ++ t) = head s :=
  by 
    induction s 
    contradiction 
    rfl

theorem head'_append {s t : List α} {x : α} (h : x ∈ s.head') : x ∈ (s ++ t).head' :=
  by 
    cases s 
    contradiction 
    exact h

theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ nil) : tail (l ++ [a]) = tail l ++ [a] :=
  by 
    induction l 
    contradiction 
    rw [tail, cons_append, tail]

theorem cons_head'_tail : ∀ {l : List α} {a : α} (h : a ∈ head' l), a :: tail l = l
| [], a, h =>
  by 
    contradiction
| b :: l, a, h =>
  by 
    simp  at h 
    simp [h]

theorem head_mem_head' [Inhabited α] : ∀ {l : List α} (h : l ≠ []), head l ∈ head' l
| [], h =>
  by 
    contradiction
| a :: l, h => rfl

theorem cons_head_tail [Inhabited α] {l : List α} (h : l ≠ []) : head l :: tail l = l :=
  cons_head'_tail (head_mem_head' h)

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem head_mem_self [inhabited α] {l : list α} (h : «expr ≠ »(l, nil)) : «expr ∈ »(l.head, l) :=
begin
  have [ident h'] [] [":=", expr mem_cons_self l.head l.tail],
  rwa [expr cons_head_tail h] ["at", ident h']
end

@[simp]
theorem head'_map (f : α → β) l : head' (map f l) = (head' l).map f :=
  by 
    cases l <;> rfl

theorem tail_append_of_ne_nil (l l' : List α) (h : l ≠ []) : (l ++ l').tail = l.tail ++ l' :=
  by 
    cases l
    ·
      contradiction
    ·
      simp 

@[simp]
theorem nth_le_tail (l : List α) i (h : i < l.tail.length)
  (h' : (i+1) < l.length :=
    by 
      simpa [←lt_tsub_iff_right] using h) :
  l.tail.nth_le i h = l.nth_le (i+1) h' :=
  by 
    cases l
    ·
      cases h
    ·
      simpa

/-! ### Induction from the right -/


/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
@[elab_as_eliminator]
def reverse_rec_on {C : List α → Sort _} (l : List α) (H0 : C []) (H1 : ∀ (l : List α) (a : α), C l → C (l ++ [a])) :
  C l :=
  by 
    rw [←reverse_reverse l]
    induction reverse l
    ·
      exact H0
    ·
      rw [reverse_cons]
      exact H1 _ _ ih

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Bidirectional induction principle for lists: if a property holds for the empty list, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. This can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued predicate, i.e., it
can also be used to construct data. -/
def bidirectional_rec
{C : list α → Sort*}
(H0 : C «expr[ , ]»([]))
(H1 : ∀ a : α, C «expr[ , ]»([a]))
(Hn : ∀ (a : α) (l : list α) (b : α), C l → C «expr :: »(a, «expr ++ »(l, «expr[ , ]»([b])))) : ∀ l, C l
| «expr[ , ]»([]) := H0
| «expr[ , ]»([a]) := H1 a
| «expr :: »(a, «expr :: »(b, l)) := let l' := init «expr :: »(b, l), b' := last «expr :: »(b, l) (cons_ne_nil _ _) in
have «expr < »(length l', length «expr :: »(a, «expr :: »(b, l))), by { change [expr «expr < »(_, «expr + »(length l, 2))] [] [],
  simp [] [] [] [] [] [] },
begin
  rw ["<-", expr init_append_last (cons_ne_nil b l)] [],
  have [] [":", expr C l'] [],
  from [expr bidirectional_rec l'],
  exact [expr Hn a l' b' «expr‹ ›»(C l')]
end

/-- Like `bidirectional_rec`, but with the list parameter placed first. -/
@[elab_as_eliminator]
def bidirectional_rec_on {C : List α → Sort _} (l : List α) (H0 : C []) (H1 : ∀ (a : α), C [a])
  (Hn : ∀ (a : α) (l : List α) (b : α), C l → C (a :: (l ++ [b]))) : C l :=
  bidirectional_rec H0 H1 Hn l

/-! ### sublists -/


@[simp]
theorem nil_sublist : ∀ (l : List α), [] <+ l
| [] => sublist.slnil
| a :: l => sublist.cons _ _ a (nil_sublist l)

@[refl, simp]
theorem sublist.refl : ∀ (l : List α), l <+ l
| [] => sublist.slnil
| a :: l => sublist.cons2 _ _ a (sublist.refl l)

@[trans]
theorem sublist.trans {l₁ l₂ l₃ : List α} (h₁ : l₁ <+ l₂) (h₂ : l₂ <+ l₃) : l₁ <+ l₃ :=
  sublist.rec_on h₂ (fun _ s => s) (fun l₂ l₃ a h₂ IH l₁ h₁ => sublist.cons _ _ _ (IH l₁ h₁))
    (fun l₂ l₃ a h₂ IH l₁ h₁ =>
      @sublist.cases_on _ (fun l₁ l₂' => l₂' = a :: l₂ → l₁ <+ a :: l₃) _ _ h₁ (fun _ => nil_sublist _)
        (fun l₁ l₂' a' h₁' e =>
          match a', l₂', e, h₁' with 
          | _, _, rfl, h₁ => sublist.cons _ _ _ (IH _ h₁))
        (fun l₁ l₂' a' h₁' e =>
          match a', l₂', e, h₁' with 
          | _, _, rfl, h₁ => sublist.cons2 _ _ _ (IH _ h₁))
        rfl)
    l₁ h₁

@[simp]
theorem sublist_cons (a : α) (l : List α) : l <+ a :: l :=
  sublist.cons _ _ _ (sublist.refl l)

theorem sublist_of_cons_sublist {a : α} {l₁ l₂ : List α} : a :: l₁ <+ l₂ → l₁ <+ l₂ :=
  sublist.trans (sublist_cons a l₁)

theorem sublist.cons_cons {l₁ l₂ : List α} (a : α) (s : l₁ <+ l₂) : a :: l₁ <+ a :: l₂ :=
  sublist.cons2 _ _ _ s

@[simp]
theorem sublist_append_left : ∀ (l₁ l₂ : List α), l₁ <+ l₁ ++ l₂
| [], l₂ => nil_sublist _
| a :: l₁, l₂ => (sublist_append_left l₁ l₂).cons_cons _

@[simp]
theorem sublist_append_right : ∀ (l₁ l₂ : List α), l₂ <+ l₁ ++ l₂
| [], l₂ => sublist.refl _
| a :: l₁, l₂ => sublist.cons _ _ _ (sublist_append_right l₁ l₂)

theorem sublist_cons_of_sublist (a : α) {l₁ l₂ : List α} : l₁ <+ l₂ → l₁ <+ a :: l₂ :=
  sublist.cons _ _ _

theorem sublist_append_of_sublist_left {l l₁ l₂ : List α} (s : l <+ l₁) : l <+ l₁ ++ l₂ :=
  s.trans$ sublist_append_left _ _

theorem sublist_append_of_sublist_right {l l₁ l₂ : List α} (s : l <+ l₂) : l <+ l₁ ++ l₂ :=
  s.trans$ sublist_append_right _ _

theorem sublist_of_cons_sublist_cons {l₁ l₂ : List α} : ∀ {a : α}, a :: l₁ <+ a :: l₂ → l₁ <+ l₂
| _, sublist.cons _ _ a s => sublist_of_cons_sublist s
| _, sublist.cons2 _ _ a s => s

theorem cons_sublist_cons_iff {l₁ l₂ : List α} {a : α} : a :: l₁ <+ a :: l₂ ↔ l₁ <+ l₂ :=
  ⟨sublist_of_cons_sublist_cons, sublist.cons_cons _⟩

@[simp]
theorem append_sublist_append_left {l₁ l₂ : List α} : ∀ l, l ++ l₁ <+ l ++ l₂ ↔ l₁ <+ l₂
| [] => Iff.rfl
| a :: l => cons_sublist_cons_iff.trans (append_sublist_append_left l)

theorem sublist.append_right {l₁ l₂ : List α} (h : l₁ <+ l₂) l : l₁ ++ l <+ l₂ ++ l :=
  by 
    induction' h with _ _ a _ ih _ _ a _ ih
    ·
      rfl
    ·
      apply sublist_cons_of_sublist a ih
    ·
      apply ih.cons_cons a

theorem sublist_or_mem_of_sublist {l l₁ l₂ : List α} {a : α} (h : l <+ l₁ ++ a :: l₂) : l <+ l₁ ++ l₂ ∨ a ∈ l :=
  by 
    induction' l₁ with b l₁ IH generalizing l
    ·
      cases h
      ·
        left 
        exact ‹l <+ l₂›
      ·
        right 
        apply mem_cons_self
    ·
      cases' h with _ _ _ h _ _ _ h
      ·
        exact Or.imp_left (sublist_cons_of_sublist _) (IH h)
      ·
        exact (IH h).imp (sublist.cons_cons _) (mem_cons_of_mem _)

theorem sublist.reverse {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₁.reverse <+ l₂.reverse :=
  by 
    induction' h with _ _ _ _ ih _ _ a _ ih
    ·
      rfl
    ·
      rw [reverse_cons]
      exact sublist_append_of_sublist_left ih
    ·
      rw [reverse_cons, reverse_cons]
      exact ih.append_right [a]

@[simp]
theorem reverse_sublist_iff {l₁ l₂ : List α} : l₁.reverse <+ l₂.reverse ↔ l₁ <+ l₂ :=
  ⟨fun h => l₁.reverse_reverse ▸ l₂.reverse_reverse ▸ h.reverse, sublist.reverse⟩

@[simp]
theorem append_sublist_append_right {l₁ l₂ : List α} l : l₁ ++ l <+ l₂ ++ l ↔ l₁ <+ l₂ :=
  ⟨fun h =>
      by 
        simpa only [reverse_append, append_sublist_append_left, reverse_sublist_iff] using h.reverse,
    fun h => h.append_right l⟩

theorem sublist.append {l₁ l₂ r₁ r₂ : List α} (hl : l₁ <+ l₂) (hr : r₁ <+ r₂) : l₁ ++ r₁ <+ l₂ ++ r₂ :=
  (hl.append_right _).trans ((append_sublist_append_left _).2 hr)

theorem sublist.subset : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → l₁ ⊆ l₂
| _, _, sublist.slnil, b, h => h
| _, _, sublist.cons l₁ l₂ a s, b, h => mem_cons_of_mem _ (sublist.subset s h)
| _, _, sublist.cons2 l₁ l₂ a s, b, h =>
  match eq_or_mem_of_mem_cons h with 
  | Or.inl h => h ▸ mem_cons_self _ _
  | Or.inr h => mem_cons_of_mem _ (sublist.subset s h)

@[simp]
theorem singleton_sublist {a : α} {l} : [a] <+ l ↔ a ∈ l :=
  ⟨fun h => h.subset (mem_singleton_self _),
    fun h =>
      let ⟨s, t, e⟩ := mem_split h 
      e.symm ▸ ((nil_sublist _).cons_cons _).trans (sublist_append_right _ _)⟩

theorem eq_nil_of_sublist_nil {l : List α} (s : l <+ []) : l = [] :=
  eq_nil_of_subset_nil$ s.subset

@[simp]
theorem sublist_nil_iff_eq_nil {l : List α} : l <+ [] ↔ l = [] :=
  ⟨eq_nil_of_sublist_nil, fun H => H ▸ sublist.refl _⟩

@[simp]
theorem repeat_sublist_repeat (a : α) {m n} : repeat a m <+ repeat a n ↔ m ≤ n :=
  ⟨fun h =>
      by 
        simpa only [length_repeat] using length_le_of_sublist h,
    fun h =>
      by 
        induction h <;> [rfl, simp only [repeat_succ, sublist.cons]]⟩

theorem eq_of_sublist_of_length_eq : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → length l₁ = length l₂ → l₁ = l₂
| _, _, sublist.slnil, h => rfl
| _, _, sublist.cons l₁ l₂ a s, h =>
  absurd (length_le_of_sublist s)$
    not_le_of_gtₓ$
      by 
        rw [h] <;> apply lt_succ_self
| _, _, sublist.cons2 l₁ l₂ a s, h =>
  by 
    rw [length, length] at h <;> injection h with h <;> rw [eq_of_sublist_of_length_eq s h]

theorem eq_of_sublist_of_length_le {l₁ l₂ : List α} (s : l₁ <+ l₂) (h : length l₂ ≤ length l₁) : l₁ = l₂ :=
  eq_of_sublist_of_length_eq s (le_antisymmₓ (length_le_of_sublist s) h)

theorem sublist.antisymm {l₁ l₂ : List α} (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
  eq_of_sublist_of_length_le s₁ (length_le_of_sublist s₂)

instance decidable_sublist [DecidableEq α] : ∀ (l₁ l₂ : List α), Decidable (l₁ <+ l₂)
| [], l₂ => is_true$ nil_sublist _
| a :: l₁, [] => is_false$ fun h => List.noConfusion$ eq_nil_of_sublist_nil h
| a :: l₁, b :: l₂ =>
  if h : a = b then
    decidableOfDecidableOfIff (decidable_sublist l₁ l₂)$
      by 
        rw [←h] <;> exact ⟨sublist.cons_cons _, sublist_of_cons_sublist_cons⟩
  else
    decidableOfDecidableOfIff (decidable_sublist (a :: l₁) l₂)
      ⟨sublist_cons_of_sublist _,
        fun s =>
          match a, l₁, s, h with 
          | a, l₁, sublist.cons _ _ _ s', h => s'
          | _, _, sublist.cons2 t _ _ s', h => absurd rfl h⟩

/-! ### index_of -/


section IndexOf

variable[DecidableEq α]

@[simp]
theorem index_of_nil (a : α) : index_of a [] = 0 :=
  rfl

theorem index_of_cons (a b : α) (l : List α) : index_of a (b :: l) = if a = b then 0 else succ (index_of a l) :=
  rfl

theorem index_of_cons_eq {a b : α} (l : List α) : a = b → index_of a (b :: l) = 0 :=
  fun e => if_pos e

@[simp]
theorem index_of_cons_self (a : α) (l : List α) : index_of a (a :: l) = 0 :=
  index_of_cons_eq _ rfl

@[simp]
theorem index_of_cons_ne {a b : α} (l : List α) : a ≠ b → index_of a (b :: l) = succ (index_of a l) :=
  fun n => if_neg n

theorem index_of_eq_length {a : α} {l : List α} : index_of a l = length l ↔ a ∉ l :=
  by 
    induction' l with b l ih
    ·
      exact iff_of_true rfl (not_mem_nil _)
    simp only [length, mem_cons_iff, index_of_cons]
    splitIfs
    ·
      exact
        iff_of_false
          (by 
            rintro ⟨⟩)
          fun H => H$ Or.inl h
    ·
      simp only [h, false_orₓ]
      rw [←ih]
      exact succ_inj'

@[simp]
theorem index_of_of_not_mem {l : List α} {a : α} : a ∉ l → index_of a l = length l :=
  index_of_eq_length.2

theorem index_of_le_length {a : α} {l : List α} : index_of a l ≤ length l :=
  by 
    induction' l with b l ih
    ·
      rfl 
    simp only [length, index_of_cons]
    byCases' h : a = b
    ·
      rw [if_pos h]
      exact Nat.zero_leₓ _ 
    rw [if_neg h]
    exact succ_le_succ ih

theorem index_of_lt_length {a} {l : List α} : index_of a l < length l ↔ a ∈ l :=
  ⟨fun h => Decidable.by_contradiction$ fun al => ne_of_ltₓ h$ index_of_eq_length.2 al,
    fun al => lt_of_le_of_neₓ index_of_le_length$ fun h => index_of_eq_length.1 h al⟩

end IndexOf

/-! ### nth element -/


theorem nth_le_of_mem : ∀ {a} {l : List α}, a ∈ l → ∃ n h, nth_le l n h = a
| a, _ :: l, Or.inl rfl => ⟨0, succ_pos _, rfl⟩
| a, b :: l, Or.inr m =>
  let ⟨n, h, e⟩ := nth_le_of_mem m
  ⟨n+1, succ_lt_succ h, e⟩

theorem nth_le_nth : ∀ {l : List α} {n} h, nth l n = some (nth_le l n h)
| a :: l, 0, h => rfl
| a :: l, n+1, h => @nth_le_nth l n _

theorem nth_len_le : ∀ {l : List α} {n}, length l ≤ n → nth l n = none
| [], n, h => rfl
| a :: l, n+1, h => nth_len_le (le_of_succ_le_succ h)

theorem nth_eq_some {l : List α} {n a} : nth l n = some a ↔ ∃ h, nth_le l n h = a :=
  ⟨fun e =>
      have h : n < length l :=
        lt_of_not_geₓ$
          fun hn =>
            by 
              rw [nth_len_le hn] at e <;> contradiction
      ⟨h,
        by 
          rw [nth_le_nth h] at e <;> injection e with e <;> apply nth_le_mem⟩,
    fun ⟨h, e⟩ => e ▸ nth_le_nth _⟩

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
@[simp] theorem nth_eq_none_iff : ∀ {l : list α} {n}, «expr ↔ »(«expr = »(nth l n, none), «expr ≤ »(length l, n)) :=
begin
  intros [],
  split,
  { intro [ident h],
    by_contradiction [ident h'],
    have [ident h₂] [":", expr «expr∃ , »((h), «expr = »(l.nth_le n h, l.nth_le n (lt_of_not_ge h')))] [":=", expr ⟨lt_of_not_ge h', rfl⟩],
    rw ["[", "<-", expr nth_eq_some, ",", expr h, "]"] ["at", ident h₂],
    cases [expr h₂] [] },
  { solve_by_elim [] [] ["[", expr nth_len_le, "]"] [] }
end

theorem nth_of_mem {a} {l : List α} (h : a ∈ l) : ∃ n, nth l n = some a :=
  let ⟨n, h, e⟩ := nth_le_of_mem h
  ⟨n,
    by 
      rw [nth_le_nth, e]⟩

theorem nth_le_mem : ∀ (l : List α) n h, nth_le l n h ∈ l
| a :: l, 0, h => mem_cons_self _ _
| a :: l, n+1, h => mem_cons_of_mem _ (nth_le_mem l _ _)

theorem nth_mem {l : List α} {n a} (e : nth l n = some a) : a ∈ l :=
  let ⟨h, e⟩ := nth_eq_some.1 e 
  e ▸ nth_le_mem _ _ _

theorem mem_iff_nth_le {a} {l : List α} : a ∈ l ↔ ∃ n h, nth_le l n h = a :=
  ⟨nth_le_of_mem, fun ⟨n, h, e⟩ => e ▸ nth_le_mem _ _ _⟩

theorem mem_iff_nth {a} {l : List α} : a ∈ l ↔ ∃ n, nth l n = some a :=
  mem_iff_nth_le.trans$ exists_congr$ fun n => nth_eq_some.symm

theorem nth_zero (l : List α) : l.nth 0 = l.head' :=
  by 
    cases l <;> rfl

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem nth_injective
{α : Type u}
{xs : list α}
{i j : exprℕ()}
(h₀ : «expr < »(i, xs.length))
(h₁ : nodup xs)
(h₂ : «expr = »(xs.nth i, xs.nth j)) : «expr = »(i, j) :=
begin
  induction [expr xs] [] ["with", ident x, ident xs] ["generalizing", ident i, ident j],
  { cases [expr h₀] [] },
  { cases [expr i] []; cases [expr j] [],
    case [ident nat.zero, ident nat.zero] { refl },
    case [ident nat.succ, ident nat.succ] { congr,
      cases [expr h₁] [],
      apply [expr xs_ih]; solve_by_elim [] [] ["[", expr lt_of_succ_lt_succ, "]"] [] },
    iterate [2] { dsimp [] [] [] ["at", ident h₂],
      cases [expr h₁] ["with", "_", "_", ident h, ident h'],
      cases [expr h x _ rfl] [],
      rw [expr mem_iff_nth] [],
      exact [expr ⟨_, h₂.symm⟩] <|> exact [expr ⟨_, h₂⟩] } }
end

@[simp]
theorem nth_map (f : α → β) : ∀ l n, nth (map f l) n = (nth l n).map f
| [], n => rfl
| a :: l, 0 => rfl
| a :: l, n+1 => nth_map l n

theorem nth_le_map (f : α → β) {l n} H1 H2 : nth_le (map f l) n H1 = f (nth_le l n H2) :=
  Option.some.injₓ$
    by 
      rw [←nth_le_nth, nth_map, nth_le_nth] <;> rfl

/-- A version of `nth_le_map` that can be used for rewriting. -/
theorem nth_le_map_rev (f : α → β) {l n} H : f (nth_le l n H) = nth_le (map f l) n ((length_map f l).symm ▸ H) :=
  (nth_le_map f _ _).symm

@[simp]
theorem nth_le_map' (f : α → β) {l n} H : nth_le (map f l) n H = f (nth_le l n (length_map f l ▸ H)) :=
  nth_le_map f _ _

/-- If one has `nth_le L i hi` in a formula and `h : L = L'`, one can not `rw h` in the formula as
`hi` gives `i < L.length` and not `i < L'.length`. The lemma `nth_le_of_eq` can be used to make
such a rewrite, with `rw (nth_le_of_eq h)`. -/
theorem nth_le_of_eq {L L' : List α} (h : L = L') {i : ℕ} (hi : i < L.length) : nth_le L i hi = nth_le L' i (h ▸ hi) :=
  by 
    congr 
    exact h

@[simp]
theorem nth_le_singleton (a : α) {n : ℕ} (hn : n < 1) : nth_le [a] n hn = a :=
  have hn0 : n = 0 := le_zero_iff.1 (le_of_lt_succ hn)
  by 
    subst hn0 <;> rfl

theorem nth_le_zero [Inhabited α] {L : List α} (h : 0 < L.length) : L.nth_le 0 h = L.head :=
  by 
    cases L 
    cases h 
    simp 

theorem nth_le_append : ∀ {l₁ l₂ : List α} {n : ℕ} hn₁ hn₂, (l₁ ++ l₂).nthLe n hn₁ = l₁.nth_le n hn₂
| [], _, n, hn₁, hn₂ => (Nat.not_lt_zeroₓ _ hn₂).elim
| a :: l, _, 0, hn₁, hn₂ => rfl
| a :: l, _, n+1, hn₁, hn₂ =>
  by 
    simp only [nth_le, cons_append] <;> exact nth_le_append _ _

theorem nth_le_append_right_aux {l₁ l₂ : List α} {n : ℕ} (h₁ : l₁.length ≤ n) (h₂ : n < (l₁ ++ l₂).length) :
  n - l₁.length < l₂.length :=
  by 
    rw [List.length_append] at h₂ 
    convert (tsub_lt_tsub_iff_right h₁).mpr h₂ 
    simp 

theorem nth_le_append_right :
  ∀ {l₁ l₂ : List α} {n : ℕ} (h₁ : l₁.length ≤ n) h₂,
    (l₁ ++ l₂).nthLe n h₂ = l₂.nth_le (n - l₁.length) (nth_le_append_right_aux h₁ h₂)
| [], _, n, h₁, h₂ => rfl
| a :: l, _, n+1, h₁, h₂ =>
  by 
    dsimp 
    conv  => toRHS congr skip rw [tsub_add_eq_tsub_tsub, tsub_right_comm, add_tsub_cancel_right]
    rw [nth_le_append_right (nat.lt_succ_iff.mp h₁)]

@[simp]
theorem nth_le_repeat (a : α) {n m : ℕ} (h : m < (List.repeat a n).length) : (List.repeat a n).nthLe m h = a :=
  eq_of_mem_repeat (nth_le_mem _ _ _)

theorem nth_append {l₁ l₂ : List α} {n : ℕ} (hn : n < l₁.length) : (l₁ ++ l₂).nth n = l₁.nth n :=
  have hn' : n < (l₁ ++ l₂).length :=
    lt_of_lt_of_leₓ hn
      (by 
        rw [length_append] <;> exact Nat.le_add_rightₓ _ _)
  by 
    rw [nth_le_nth hn, nth_le_nth hn', nth_le_append]

theorem nth_append_right {l₁ l₂ : List α} {n : ℕ} (hn : l₁.length ≤ n) : (l₁ ++ l₂).nth n = l₂.nth (n - l₁.length) :=
  by 
    byCases' hl : n < (l₁ ++ l₂).length
    ·
      rw [nth_le_nth hl, nth_le_nth, nth_le_append_right hn]
    ·
      rw [nth_len_le (le_of_not_ltₓ hl), nth_len_le]
      rw [not_ltₓ, length_append] at hl 
      exact le_tsub_of_add_le_left hl

theorem last_eq_nth_le :
  ∀ (l : List α) (h : l ≠ []), last l h = l.nth_le (l.length - 1) (Nat.sub_ltₓ (length_pos_of_ne_nil h) one_pos)
| [], h => rfl
| [a], h =>
  by 
    rw [last_singleton, nth_le_singleton]
| a :: b :: l, h =>
  by 
    rw [last_cons, last_eq_nth_le (b :: l)]
    rfl 
    exact cons_ne_nil b l

@[simp]
theorem nth_concat_length : ∀ (l : List α) (a : α), (l ++ [a]).nth l.length = some a
| [], a => rfl
| b :: l, a =>
  by 
    rw [cons_append, length_cons, nth, nth_concat_length]

theorem nth_le_cons_length (x : α) (xs : List α) (n : ℕ) (h : n = xs.length) :
  (x :: xs).nthLe n
      (by 
        simp [h]) =
    (x :: xs).last (cons_ne_nil x xs) :=
  by 
    rw [last_eq_nth_le]
    congr 
    simp [h]

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[ext #[]] theorem ext : ∀ {l₁ l₂ : list α}, ∀ n, «expr = »(nth l₁ n, nth l₂ n) → «expr = »(l₁, l₂)
| «expr[ , ]»([]), «expr[ , ]»([]), h := rfl
| «expr :: »(a, l₁), «expr[ , ]»([]), h := by have [ident h0] [] [":=", expr h 0]; contradiction
| «expr[ , ]»([]), «expr :: »(a', l₂), h := by have [ident h0] [] [":=", expr h 0]; contradiction
| «expr :: »(a, l₁), «expr :: »(a', l₂), h := by have [ident h0] [":", expr «expr = »(some a, some a')] [":=", expr h 0]; injection [expr h0] ["with", ident aa]; simp [] [] ["only"] ["[", expr aa, ",", expr ext (λ
  n, h «expr + »(n, 1)), "]"] [] []; split; refl

theorem ext_le {l₁ l₂ : List α} (hl : length l₁ = length l₂) (h : ∀ n h₁ h₂, nth_le l₁ n h₁ = nth_le l₂ n h₂) :
  l₁ = l₂ :=
  ext$
    fun n =>
      if h₁ : n < length l₁ then
        by 
          rw [nth_le_nth, nth_le_nth,
            h n h₁
              (by 
                rwa [←hl])]
      else
        let h₁ := le_of_not_gtₓ h₁ 
        by 
          rw [nth_len_le h₁, nth_len_le]
          rwa [←hl]

@[simp]
theorem index_of_nth_le [DecidableEq α] {a : α} : ∀ {l : List α} h, nth_le l (index_of a l) h = a
| b :: l, h =>
  by 
    byCases' h' : a = b <;> simp only [h', if_pos, if_false, index_of_cons, nth_le, @index_of_nth_le l]

@[simp]
theorem index_of_nth [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) : nth l (index_of a l) = some a :=
  by 
    rw [nth_le_nth, index_of_nth_le (index_of_lt_length.2 h)]

theorem nth_le_reverse_aux1 : ∀ (l r : List α) i h1 h2, nth_le (reverse_core l r) (i+length l) h1 = nth_le r i h2
| [], r, i => fun h1 h2 => rfl
| a :: l, r, i =>
  by 
    rw [show (i+length (a :: l)) = (i+1)+length l from add_right_commₓ i (length l) 1] <;>
      exact fun h1 h2 => nth_le_reverse_aux1 l (a :: r) (i+1) h1 (succ_lt_succ h2)

theorem index_of_inj [DecidableEq α] {l : List α} {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
  index_of x l = index_of y l ↔ x = y :=
  ⟨fun h =>
      have  : nth_le l (index_of x l) (index_of_lt_length.2 hx) = nth_le l (index_of y l) (index_of_lt_length.2 hy) :=
        by 
          simp only [h]
      by 
        simpa only [index_of_nth_le],
    fun h =>
      by 
        subst h⟩

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nth_le_reverse_aux2 : ∀
(l r : list α)
(i : nat)
(h1)
(h2), «expr = »(nth_le (reverse_core l r) «expr - »(«expr - »(length l, 1), i) h1, nth_le l i h2)
| «expr[ , ]»([]), r, i, h1, h2 := absurd h2 (nat.not_lt_zero _)
| «expr :: »(a, l), r, 0, h1, h2 := begin
  have [ident aux] [] [":=", expr nth_le_reverse_aux1 l «expr :: »(a, r) 0],
  rw [expr zero_add] ["at", ident aux],
  exact [expr aux _ (zero_lt_succ _)]
end
| «expr :: »(a, l), r, «expr + »(i, 1), h1, h2 := begin
  have [ident aux] [] [":=", expr nth_le_reverse_aux2 l «expr :: »(a, r) i],
  have [ident heq] [] [":=", expr calc
     «expr = »(«expr - »(«expr - »(length «expr :: »(a, l), 1), «expr + »(i, 1)), «expr - »(length l, «expr + »(1, i))) : by rw [expr add_comm] []; refl
     «expr = »(..., «expr - »(«expr - »(length l, 1), i)) : by rw ["<-", expr tsub_add_eq_tsub_tsub] []],
  rw ["[", "<-", expr heq, "]"] ["at", ident aux],
  apply [expr aux]
end

@[simp]
theorem nth_le_reverse (l : List α) (i : Nat) h1 h2 : nth_le (reverse l) (length l - 1 - i) h1 = nth_le l i h2 :=
  nth_le_reverse_aux2 _ _ _ _ _

theorem nth_le_reverse' (l : List α) (n : ℕ) (hn : n < l.reverse.length) hn' :
  l.reverse.nth_le n hn = l.nth_le (l.length - 1 - n) hn' :=
  by 
    rw [eq_comm]
    convert nth_le_reverse l.reverse _ _ _ using 1
    ·
      simp 
    ·
      simpa

theorem eq_cons_of_length_one {l : List α} (h : l.length = 1) : l = [l.nth_le 0 (h.symm ▸ zero_lt_one)] :=
  by 
    refine'
      ext_le
        (by 
          convert h)
        fun n h₁ h₂ => _ 
    simp only [nth_le_singleton]
    congr 
    exact eq_bot_iff.mpr (nat.lt_succ_iff.mp h₂)

theorem modify_nth_tail_modify_nth_tail {f g : List α → List α} (m : ℕ) :
  ∀ n (l : List α),
    (l.modify_nth_tail f n).modifyNthTail g (m+n) = l.modify_nth_tail (fun l => (f l).modifyNthTail g m) n
| 0, l => rfl
| n+1, [] => rfl
| n+1, a :: l => congr_argₓ (List.cons a) (modify_nth_tail_modify_nth_tail n l)

theorem modify_nth_tail_modify_nth_tail_le {f g : List α → List α} (m n : ℕ) (l : List α) (h : n ≤ m) :
  (l.modify_nth_tail f n).modifyNthTail g m = l.modify_nth_tail (fun l => (f l).modifyNthTail g (m - n)) n :=
  by 
    rcases le_iff_exists_add.1 h with ⟨m, rfl⟩
    rw [add_tsub_cancel_left, add_commₓ, modify_nth_tail_modify_nth_tail]

theorem modify_nth_tail_modify_nth_tail_same {f g : List α → List α} (n : ℕ) (l : List α) :
  (l.modify_nth_tail f n).modifyNthTail g n = l.modify_nth_tail (g ∘ f) n :=
  by 
    rw [modify_nth_tail_modify_nth_tail_le n n l (le_reflₓ n), tsub_self] <;> rfl

theorem modify_nth_tail_id : ∀ n (l : List α), l.modify_nth_tail id n = l
| 0, l => rfl
| n+1, [] => rfl
| n+1, a :: l => congr_argₓ (List.cons a) (modify_nth_tail_id n l)

theorem remove_nth_eq_nth_tail : ∀ n (l : List α), remove_nth l n = modify_nth_tail tail n l
| 0, l =>
  by 
    cases l <;> rfl
| n+1, [] => rfl
| n+1, a :: l => congr_argₓ (cons _) (remove_nth_eq_nth_tail _ _)

theorem update_nth_eq_modify_nth (a : α) : ∀ n (l : List α), update_nth l n a = modify_nth (fun _ => a) n l
| 0, l =>
  by 
    cases l <;> rfl
| n+1, [] => rfl
| n+1, b :: l => congr_argₓ (cons _) (update_nth_eq_modify_nth _ _)

theorem modify_nth_eq_update_nth (f : α → α) :
  ∀ n (l : List α), modify_nth f n l = ((fun a => update_nth l n (f a)) <$> nth l n).getOrElse l
| 0, l =>
  by 
    cases l <;> rfl
| n+1, [] => rfl
| n+1, b :: l =>
  (congr_argₓ (cons b) (modify_nth_eq_update_nth n l)).trans$
    by 
      cases nth l n <;> rfl

theorem nth_modify_nth (f : α → α) :
  ∀ n (l : List α) m, nth (modify_nth f n l) m = (fun a => if n = m then f a else a) <$> nth l m
| n, l, 0 =>
  by 
    cases l <;> cases n <;> rfl
| n, [], m+1 =>
  by 
    cases n <;> rfl
| 0, a :: l, m+1 =>
  by 
    cases nth l m <;> rfl
| n+1, a :: l, m+1 =>
  (nth_modify_nth n l m).trans$
    by 
      cases' nth l m with b <;>
        byCases' n = m <;>
          simp only [h, if_pos, if_true, if_false, Option.map_none, Option.map_some, mt succ.inj, not_false_iff]

theorem modify_nth_tail_length (f : List α → List α) (H : ∀ l, length (f l) = length l) :
  ∀ n l, length (modify_nth_tail f n l) = length l
| 0, l => H _
| n+1, [] => rfl
| n+1, a :: l => @congr_argₓ _ _ _ _ (·+1) (modify_nth_tail_length _ _)

@[simp]
theorem modify_nth_length (f : α → α) : ∀ n l, length (modify_nth f n l) = length l :=
  modify_nth_tail_length _
    fun l =>
      by 
        cases l <;> rfl

@[simp]
theorem update_nth_length (l : List α) n (a : α) : length (update_nth l n a) = length l :=
  by 
    simp only [update_nth_eq_modify_nth, modify_nth_length]

@[simp]
theorem nth_modify_nth_eq (f : α → α) n (l : List α) : nth (modify_nth f n l) n = f <$> nth l n :=
  by 
    simp only [nth_modify_nth, if_pos]

@[simp]
theorem nth_modify_nth_ne (f : α → α) {m n} (l : List α) (h : m ≠ n) : nth (modify_nth f m l) n = nth l n :=
  by 
    simp only [nth_modify_nth, if_neg h, id_map'ₓ]

theorem nth_update_nth_eq (a : α) n (l : List α) : nth (update_nth l n a) n = (fun _ => a) <$> nth l n :=
  by 
    simp only [update_nth_eq_modify_nth, nth_modify_nth_eq]

theorem nth_update_nth_of_lt (a : α) {n} {l : List α} (h : n < length l) : nth (update_nth l n a) n = some a :=
  by 
    rw [nth_update_nth_eq, nth_le_nth h] <;> rfl

theorem nth_update_nth_ne (a : α) {m n} (l : List α) (h : m ≠ n) : nth (update_nth l m a) n = nth l n :=
  by 
    simp only [update_nth_eq_modify_nth, nth_modify_nth_ne _ _ h]

@[simp]
theorem update_nth_nil (n : ℕ) (a : α) : [].updateNth n a = [] :=
  rfl

@[simp]
theorem update_nth_succ (x : α) (xs : List α) (n : ℕ) (a : α) : (x :: xs).updateNth n.succ a = x :: xs.update_nth n a :=
  rfl

theorem update_nth_comm (a b : α) :
  ∀ {n m : ℕ} (l : List α) (h : n ≠ m), (l.update_nth n a).updateNth m b = (l.update_nth m b).updateNth n a
| _, _, [], _ =>
  by 
    simp 
| 0, 0, x :: t, h => absurd rfl h
| n+1, 0, x :: t, h =>
  by 
    simp [List.updateNth]
| 0, m+1, x :: t, h =>
  by 
    simp [List.updateNth]
| n+1, m+1, x :: t, h =>
  by 
    simp only [update_nth, true_andₓ, eq_self_iff_true]
    exact update_nth_comm t fun h' => h$ nat.succ_inj'.mpr h'

@[simp]
theorem nth_le_update_nth_eq (l : List α) (i : ℕ) (a : α) (h : i < (l.update_nth i a).length) :
  (l.update_nth i a).nthLe i h = a :=
  by 
    rw [←Option.some_inj, ←nth_le_nth, nth_update_nth_eq, nth_le_nth] <;> simp_all 

@[simp]
theorem nth_le_update_nth_of_ne {l : List α} {i j : ℕ} (h : i ≠ j) (a : α) (hj : j < (l.update_nth i a).length) :
  (l.update_nth i a).nthLe j hj =
    l.nth_le j
      (by 
        simpa using hj) :=
  by 
    rw [←Option.some_inj, ←List.nth_le_nth, List.nth_update_nth_ne _ _ h, List.nth_le_nth]

theorem mem_or_eq_of_mem_update_nth : ∀ {l : List α} {n : ℕ} {a b : α} (h : a ∈ l.update_nth n b), a ∈ l ∨ a = b
| [], n, a, b, h => False.elim h
| c :: l, 0, a, b, h => ((mem_cons_iff _ _ _).1 h).elim Or.inr (Or.inl ∘ mem_cons_of_mem _)
| c :: l, n+1, a, b, h =>
  ((mem_cons_iff _ _ _).1 h).elim (fun h => h ▸ Or.inl (mem_cons_self _ _))
    fun h => (mem_or_eq_of_mem_update_nth h).elim (Or.inl ∘ mem_cons_of_mem _) Or.inr

section InsertNth

variable{a : α}

@[simp]
theorem insert_nth_zero (s : List α) (x : α) : insert_nth 0 x s = x :: s :=
  rfl

@[simp]
theorem insert_nth_succ_nil (n : ℕ) (a : α) : insert_nth (n+1) a [] = [] :=
  rfl

@[simp]
theorem insert_nth_succ_cons (s : List α) (hd x : α) (n : ℕ) : insert_nth (n+1) x (hd :: s) = hd :: insert_nth n x s :=
  rfl

theorem length_insert_nth : ∀ n as, n ≤ length as → length (insert_nth n a as) = length as+1
| 0, as, h => rfl
| n+1, [], h => (Nat.not_succ_le_zeroₓ _ h).elim
| n+1, a' :: as, h => congr_argₓ Nat.succ$ length_insert_nth n as (Nat.le_of_succ_le_succₓ h)

theorem remove_nth_insert_nth (n : ℕ) (l : List α) : (l.insert_nth n a).removeNth n = l :=
  by 
    rw [remove_nth_eq_nth_tail, insert_nth, modify_nth_tail_modify_nth_tail_same] <;> exact modify_nth_tail_id _ _

theorem insert_nth_remove_nth_of_ge :
  ∀ n m as, n < length as → n ≤ m → insert_nth m a (as.remove_nth n) = (as.insert_nth (m+1) a).removeNth n
| 0, 0, [], has, _ => (lt_irreflₓ _ has).elim
| 0, 0, a :: as, has, hmn =>
  by 
    simp [remove_nth, insert_nth]
| 0, m+1, a :: as, has, hmn => rfl
| n+1, m+1, a :: as, has, hmn =>
  congr_argₓ (cons a)$ insert_nth_remove_nth_of_ge n m as (Nat.lt_of_succ_lt_succₓ has) (Nat.le_of_succ_le_succₓ hmn)

theorem insert_nth_remove_nth_of_le :
  ∀ n m as, n < length as → m ≤ n → insert_nth m a (as.remove_nth n) = (as.insert_nth m a).removeNth (n+1)
| n, 0, a :: as, has, hmn => rfl
| n+1, m+1, a :: as, has, hmn =>
  congr_argₓ (cons a)$ insert_nth_remove_nth_of_le n m as (Nat.lt_of_succ_lt_succₓ has) (Nat.le_of_succ_le_succₓ hmn)

theorem insert_nth_comm (a b : α) :
  ∀ (i j : ℕ) (l : List α) (h : i ≤ j) (hj : j ≤ length l),
    (l.insert_nth i a).insertNth (j+1) b = (l.insert_nth j b).insertNth i a
| 0, j, l =>
  by 
    simp [insert_nth]
| i+1, 0, l => fun h => (Nat.not_lt_zeroₓ _ h).elim
| i+1, j+1, [] =>
  by 
    simp 
| i+1, j+1, c :: l =>
  fun h₀ h₁ =>
    by 
      simp [insert_nth] <;> exact insert_nth_comm i j l (Nat.le_of_succ_le_succₓ h₀) (Nat.le_of_succ_le_succₓ h₁)

theorem mem_insert_nth {a b : α} : ∀ {n : ℕ} {l : List α} (hi : n ≤ l.length), a ∈ l.insert_nth n b ↔ a = b ∨ a ∈ l
| 0, as, h => Iff.rfl
| n+1, [], h => (Nat.not_succ_le_zeroₓ _ h).elim
| n+1, a' :: as, h =>
  by 
    dsimp [List.insertNth]
    erw [List.mem_cons_iffₓ, mem_insert_nth (Nat.le_of_succ_le_succₓ h), List.mem_cons_iffₓ, ←Or.assoc,
      or_comm (a = a'), Or.assoc]

theorem inj_on_insert_nth_index_of_not_mem (l : List α) (x : α) (hx : x ∉ l) :
  Set.InjOn (fun k => insert_nth k x l) { n | n ≤ l.length } :=
  by 
    induction' l with hd tl IH
    ·
      intro n hn m hm h 
      simp only [Set.mem_singleton_iff, Set.set_of_eq_eq_singleton, length, nonpos_iff_eq_zero] at hn hm 
      simp [hn, hm]
    ·
      intro n hn m hm h 
      simp only [length, Set.mem_set_of_eq] at hn hm 
      simp only [mem_cons_iff, not_or_distrib] at hx 
      cases n <;> cases m
      ·
        rfl
      ·
        simpa [hx.left] using h
      ·
        simpa [Ne.symm hx.left] using h
      ·
        simp only [true_andₓ, eq_self_iff_true, insert_nth_succ_cons] at h 
        rw [Nat.succ_inj']
        refine' IH hx.right _ _ h
        ·
          simpa [Nat.succ_le_succ_iff] using hn
        ·
          simpa [Nat.succ_le_succ_iff] using hm

theorem insert_nth_of_length_lt (l : List α) (x : α) (n : ℕ) (h : l.length < n) : insert_nth n x l = l :=
  by 
    induction' l with hd tl IH generalizing n
    ·
      cases n
      ·
        simpa using h
      ·
        simp 
    ·
      cases n
      ·
        simpa using h
      ·
        simp only [Nat.succ_lt_succ_iff, length] at h 
        simpa using IH _ h

@[simp]
theorem insert_nth_length_self (l : List α) (x : α) : insert_nth l.length x l = l ++ [x] :=
  by 
    induction' l with hd tl IH
    ·
      simp 
    ·
      simpa using IH

theorem length_le_length_insert_nth (l : List α) (x : α) (n : ℕ) : l.length ≤ (insert_nth n x l).length :=
  by 
    cases' le_or_ltₓ n l.length with hn hn
    ·
      rw [length_insert_nth _ _ hn]
      exact (Nat.lt_succ_selfₓ _).le
    ·
      rw [insert_nth_of_length_lt _ _ _ hn]

theorem length_insert_nth_le_succ (l : List α) (x : α) (n : ℕ) : (insert_nth n x l).length ≤ l.length+1 :=
  by 
    cases' le_or_ltₓ n l.length with hn hn
    ·
      rw [length_insert_nth _ _ hn]
    ·
      rw [insert_nth_of_length_lt _ _ _ hn]
      exact (Nat.lt_succ_selfₓ _).le

theorem nth_le_insert_nth_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
  (hk' : k < (insert_nth n x l).length := hk.trans_le (length_le_length_insert_nth _ _ _)) :
  (insert_nth n x l).nthLe k hk' = l.nth_le k hk :=
  by 
    induction' n with n IH generalizing k l
    ·
      simpa using hn
    ·
      cases' l with hd tl
      ·
        simp 
      ·
        cases k
        ·
          simp 
        ·
          rw [Nat.succ_lt_succ_iff] at hn 
          simpa using IH _ _ hn _

@[simp]
theorem nth_le_insert_nth_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
  (hn' : n < (insert_nth n x l).length :=
    by 
      rwa [length_insert_nth _ _ hn, Nat.lt_succ_iff]) :
  (insert_nth n x l).nthLe n hn' = x :=
  by 
    induction' l with hd tl IH generalizing n
    ·
      simp only [length, nonpos_iff_eq_zero] at hn 
      simp [hn]
    ·
      cases n
      ·
        simp 
      ·
        simp only [Nat.succ_le_succ_iff, length] at hn 
        simpa using IH _ hn

theorem nth_le_insert_nth_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : (n+k) < l.length)
  (hk : ((n+k)+1) < (insert_nth n x l).length :=
    by 
      rwa [length_insert_nth _ _ (le_self_add.trans hk'.le), Nat.succ_lt_succ_iff]) :
  (insert_nth n x l).nthLe ((n+k)+1) hk = nth_le l (n+k) hk' :=
  by 
    induction' l with hd tl IH generalizing n k
    ·
      simpa using hk'
    ·
      cases n
      ·
        simpa
      ·
        simpa [succ_add] using IH _ _ _

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem insert_nth_injective (n : exprℕ()) (x : α) : function.injective (insert_nth n x) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] [],
  { have [] [":", expr «expr = »(insert_nth 0 x, cons x)] [":=", expr funext (λ _, rfl)],
    simp [] [] [] ["[", expr this, "]"] [] [] },
  { rintros ["(", "_", "|", "⟨", ident a, ",", ident as, "⟩", ")", "(", "_", "|", "⟨", ident b, ",", ident bs, "⟩", ")", ident h]; simpa [] [] [] ["[", expr IH.eq_iff, "]"] [] ["using", expr h] <|> refl }
end

end InsertNth

/-! ### map -/


@[simp]
theorem map_nil (f : α → β) : map f [] = [] :=
  rfl

theorem map_eq_foldr (f : α → β) (l : List α) : map f l = foldr (fun a bs => f a :: bs) [] l :=
  by 
    induction l <;> simp 

theorem map_congr {f g : α → β} : ∀ {l : List α}, (∀ x (_ : x ∈ l), f x = g x) → map f l = map g l
| [], _ => rfl
| a :: l, h =>
  let ⟨h₁, h₂⟩ := forall_mem_cons.1 h 
  by 
    rw [map, map, h₁, map_congr h₂]

theorem map_eq_map_iff {f g : α → β} {l : List α} : map f l = map g l ↔ ∀ x (_ : x ∈ l), f x = g x :=
  by 
    refine' ⟨_, map_congr⟩
    intro h x hx 
    rw [mem_iff_nth_le] at hx 
    rcases hx with ⟨n, hn, rfl⟩
    rw [nth_le_map_rev f, nth_le_map_rev g]
    congr 
    exact h

theorem map_concat (f : α → β) (a : α) (l : List α) : map f (concat l a) = concat (map f l) (f a) :=
  by 
    induction l <;> [rfl, simp only [concat_eq_append, cons_append, map, map_append]] <;> split  <;> rfl

theorem map_id' {f : α → α} (h : ∀ x, f x = x) (l : List α) : map f l = l :=
  by 
    induction l <;> [rfl, simp only [map]] <;> split  <;> rfl

theorem eq_nil_of_map_eq_nil {f : α → β} {l : List α} (h : map f l = nil) : l = nil :=
  eq_nil_of_length_eq_zero$
    by 
      rw [←length_map f l, h] <;> rfl

@[simp]
theorem map_join (f : α → β) (L : List (List α)) : map f (join L) = join (map (map f) L) :=
  by 
    induction L <;> [rfl, simp only [join, map, map_append]]

theorem bind_ret_eq_map (f : α → β) (l : List α) : l.bind (List.ret ∘ f) = map f l :=
  by 
    unfold List.bind <;> induction l <;> simp only [map, join, List.ret, cons_append, nil_append] <;> split  <;> rfl

@[simp]
theorem map_eq_map {α β} (f : α → β) (l : List α) : f <$> l = map f l :=
  rfl

@[simp]
theorem map_tail (f : α → β) l : map f (tail l) = tail (map f l) :=
  by 
    cases l <;> rfl

@[simp]
theorem map_injective_iff {f : α → β} : injective (map f) ↔ injective f :=
  by 
    split  <;> intro h x y hxy
    ·
      suffices  : [x] = [y]
      ·
        simpa using this 
      apply h 
      simp [hxy]
    ·
      induction y generalizing x 
      simpa using hxy 
      cases x 
      simpa using hxy 
      simp  at hxy 
      simp [y_ih hxy.2, h hxy.1]

/--
A single `list.map` of a composition of functions is equal to
composing a `list.map` with another `list.map`, fully applied.
This is the reverse direction of `list.map_map`.
-/
theorem comp_map (h : β → γ) (g : α → β) (l : List α) : map (h ∘ g) l = map h (map g l) :=
  (map_map _ _ _).symm

/--
Composing a `list.map` with another `list.map` is equal to
a single `list.map` of composed functions.
-/
@[simp]
theorem map_comp_map (g : β → γ) (f : α → β) : map g ∘ map f = map (g ∘ f) :=
  by 
    ext l 
    rw [comp_map]

theorem map_filter_eq_foldr (f : α → β) (p : α → Prop) [DecidablePred p] (as : List α) :
  map f (filter p as) = foldr (fun a bs => if p a then f a :: bs else bs) [] as :=
  by 
    induction as
    ·
      rfl
    ·
      simp [apply_ite (map f)]

theorem last_map (f : α → β) {l : List α} (hl : l ≠ []) : (l.map f).last (mt eq_nil_of_map_eq_nil hl) = f (l.last hl) :=
  by 
    induction' l with l_ih l_tl l_ih
    ·
      apply (hl rfl).elim
    ·
      cases l_tl
      ·
        simp 
      ·
        simpa using l_ih

/-! ### map₂ -/


theorem nil_map₂ (f : α → β → γ) (l : List β) : map₂ f [] l = [] :=
  by 
    cases l <;> rfl

theorem map₂_nil (f : α → β → γ) (l : List α) : map₂ f l [] = [] :=
  by 
    cases l <;> rfl

@[simp]
theorem map₂_flip (f : α → β → γ) : ∀ as bs, map₂ (flip f) bs as = map₂ f as bs
| [], [] => rfl
| [], b :: bs => rfl
| a :: as, [] => rfl
| a :: as, b :: bs =>
  by 
    simp [map₂_flip]
    rfl

/-! ### take, drop -/


@[simp]
theorem take_zero (l : List α) : take 0 l = [] :=
  rfl

@[simp]
theorem take_nil : ∀ n, take n [] = ([] : List α)
| 0 => rfl
| n+1 => rfl

theorem take_cons n (a : α) (l : List α) : take (succ n) (a :: l) = a :: take n l :=
  rfl

@[simp]
theorem take_length : ∀ (l : List α), take (length l) l = l
| [] => rfl
| a :: l =>
  by 
    change a :: take (length l) l = a :: l 
    rw [take_length]

theorem take_all_of_le : ∀ {n} {l : List α}, length l ≤ n → take n l = l
| 0, [], h => rfl
| 0, a :: l, h => absurd h (not_le_of_gtₓ (zero_lt_succ _))
| n+1, [], h => rfl
| n+1, a :: l, h =>
  by 
    change a :: take n l = a :: l 
    rw [take_all_of_le (le_of_succ_le_succ h)]

@[simp]
theorem take_left : ∀ (l₁ l₂ : List α), take (length l₁) (l₁ ++ l₂) = l₁
| [], l₂ => rfl
| a :: l₁, l₂ => congr_argₓ (cons a) (take_left l₁ l₂)

theorem take_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : take n (l₁ ++ l₂) = l₁ :=
  by 
    rw [←h] <;> apply take_left

theorem take_take : ∀ n m (l : List α), take n (take m l) = take (min n m) l
| n, 0, l =>
  by 
    rw [min_zero, take_zero, take_nil]
| 0, m, l =>
  by 
    rw [zero_min, take_zero, take_zero]
| succ n, succ m, nil =>
  by 
    simp only [take_nil]
| succ n, succ m, a :: l =>
  by 
    simp only [take, min_succ_succ, take_take n m l] <;> split  <;> rfl

theorem take_repeat (a : α) : ∀ (n m : ℕ), take n (repeat a m) = repeat a (min n m)
| n, 0 =>
  by 
    simp 
| 0, m =>
  by 
    simp 
| succ n, succ m =>
  by 
    simp [min_succ_succ, take_repeat]

theorem map_take {α β : Type _} (f : α → β) : ∀ (L : List α) (i : ℕ), (L.take i).map f = (L.map f).take i
| [], i =>
  by 
    simp 
| L, 0 =>
  by 
    simp 
| h :: t, n+1 =>
  by 
    dsimp 
    rw [map_take]

/-- Taking the first `n` elements in `l₁ ++ l₂` is the same as appending the first `n` elements
of `l₁` to the first `n - l₁.length` elements of `l₂`. -/
theorem take_append_eq_append_take {l₁ l₂ : List α} {n : ℕ} :
  take n (l₁ ++ l₂) = take n l₁ ++ take (n - l₁.length) l₂ :=
  by 
    induction l₁ generalizing n
    ·
      simp 
    cases n
    ·
      simp 
    simp 

theorem take_append_of_le_length {l₁ l₂ : List α} {n : ℕ} (h : n ≤ l₁.length) : (l₁ ++ l₂).take n = l₁.take n :=
  by 
    simp [take_append_eq_append_take, tsub_eq_zero_iff_le.mpr h]

/-- Taking the first `l₁.length + i` elements in `l₁ ++ l₂` is the same as appending the first
`i` elements of `l₂` to `l₁`. -/
theorem take_append {l₁ l₂ : List α} (i : ℕ) : take (l₁.length+i) (l₁ ++ l₂) = l₁ ++ take i l₂ :=
  by 
    simp [take_append_eq_append_take, take_all_of_le le_self_add]

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
theorem nth_le_take (L : List α) {i j : ℕ} (hi : i < L.length) (hj : i < j) :
  nth_le L i hi =
    nth_le (L.take j) i
      (by 
        rw [length_take]
        exact lt_minₓ hj hi) :=
  by 
    rw [nth_le_of_eq (take_append_drop j L).symm hi]
    exact nth_le_append _ _

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
theorem nth_le_take' (L : List α) {i j : ℕ} (hi : i < (L.take j).length) :
  nth_le (L.take j) i hi =
    nth_le L i
      (lt_of_lt_of_leₓ hi
        (by 
          simp [le_reflₓ])) :=
  by 
    simp  at hi 
    rw [nth_le_take L _ hi.1]

theorem nth_take {l : List α} {n m : ℕ} (h : m < n) : (l.take n).nth m = l.nth m :=
  by 
    induction' n with n hn generalizing l m
    ·
      simp only [Nat.nat_zero_eq_zero] at h 
      exact absurd h (not_lt_of_le m.zero_le)
    ·
      cases' l with hd tl
      ·
        simp only [take_nil]
      ·
        cases m
        ·
          simp only [nth, take]
        ·
          simpa only using hn (Nat.lt_of_succ_lt_succₓ h)

@[simp]
theorem nth_take_of_succ {l : List α} {n : ℕ} : (l.take (n+1)).nth n = l.nth n :=
  nth_take (Nat.lt_succ_selfₓ n)

theorem take_succ {l : List α} {n : ℕ} : l.take (n+1) = l.take n ++ (l.nth n).toList :=
  by 
    induction' l with hd tl hl generalizing n
    ·
      simp only [Option.toList, nth, take_nil, append_nil]
    ·
      cases n
      ·
        simp only [Option.toList, nth, eq_self_iff_true, and_selfₓ, take, nil_append]
      ·
        simp only [hl, cons_append, nth, eq_self_iff_true, and_selfₓ, take]

@[simp]
theorem take_eq_nil_iff {l : List α} {k : ℕ} : l.take k = [] ↔ l = [] ∨ k = 0 :=
  by 
    cases l <;> cases k <;> simp [Nat.succ_ne_zero]

theorem init_eq_take (l : List α) : l.init = l.take l.length.pred :=
  by 
    cases' l with x l
    ·
      simp [init]
    ·
      induction' l with hd tl hl generalizing x
      ·
        simp [init]
      ·
        simp [init, hl]

theorem init_take {n : ℕ} {l : List α} (h : n < l.length) : (l.take n).init = l.take n.pred :=
  by 
    simp [init_eq_take, min_eq_left_of_ltₓ h, take_take, pred_le]

@[simp]
theorem init_cons_of_ne_nil {α : Type _} {x : α} : ∀ {l : List α} (h : l ≠ []), (x :: l).init = x :: l.init
| [], h => False.elim (h rfl)
| a :: l, _ =>
  by 
    simp [init]

@[simp]
theorem init_append_of_ne_nil {α : Type _} {l : List α} : ∀ (l' : List α) (h : l ≠ []), (l' ++ l).init = l' ++ l.init
| [], _ =>
  by 
    simp only [nil_append]
| a :: l', h =>
  by 
    simp [append_ne_nil_of_ne_nil_right l' l h, init_append_of_ne_nil l' h]

@[simp]
theorem drop_eq_nil_of_le {l : List α} {k : ℕ} (h : l.length ≤ k) : l.drop k = [] :=
  by 
    simpa [←length_eq_zero] using tsub_eq_zero_iff_le.mpr h

theorem drop_eq_nil_iff_le {l : List α} {k : ℕ} : l.drop k = [] ↔ l.length ≤ k :=
  by 
    refine' ⟨fun h => _, drop_eq_nil_of_le⟩
    induction' k with k hk generalizing l
    ·
      simp only [drop] at h 
      simp [h]
    ·
      cases l
      ·
        simp 
      ·
        simp only [drop] at h 
        simpa [Nat.succ_le_succ_iff] using hk h

theorem tail_drop (l : List α) (n : ℕ) : (l.drop n).tail = l.drop (n+1) :=
  by 
    induction' l with hd tl hl generalizing n
    ·
      simp 
    ·
      cases n
      ·
        simp 
      ·
        simp [hl]

theorem cons_nth_le_drop_succ {l : List α} {n : ℕ} (hn : n < l.length) : l.nth_le n hn :: l.drop (n+1) = l.drop n :=
  by 
    induction' l with hd tl hl generalizing n
    ·
      exact
        absurd n.zero_le
          (not_le_of_lt
            (by 
              simpa using hn))
    ·
      cases n
      ·
        simp 
      ·
        simp only [Nat.succ_lt_succ_iff, List.length] at hn 
        simpa [List.nthLe, List.dropₓ] using hl hn

theorem drop_nil : ∀ n, drop n [] = ([] : List α) :=
  fun _ => drop_eq_nil_of_le (Nat.zero_leₓ _)

@[simp]
theorem drop_one : ∀ (l : List α), drop 1 l = tail l
| [] => rfl
| a :: l => rfl

theorem drop_add : ∀ m n (l : List α), drop (m+n) l = drop m (drop n l)
| m, 0, l => rfl
| m, n+1, [] => (drop_nil _).symm
| m, n+1, a :: l => drop_add m n _

@[simp]
theorem drop_left : ∀ (l₁ l₂ : List α), drop (length l₁) (l₁ ++ l₂) = l₂
| [], l₂ => rfl
| a :: l₁, l₂ => drop_left l₁ l₂

theorem drop_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : drop n (l₁ ++ l₂) = l₂ :=
  by 
    rw [←h] <;> apply drop_left

theorem drop_eq_nth_le_cons : ∀ {n} {l : List α} h, drop n l = nth_le l n h :: drop (n+1) l
| 0, a :: l, h => rfl
| n+1, a :: l, h => @drop_eq_nth_le_cons n _ _

@[simp]
theorem drop_length (l : List α) : l.drop l.length = [] :=
  calc l.drop l.length = (l ++ []).drop l.length :=
    by 
      simp 
    _ = [] := drop_left _ _
    

/-- Dropping the elements up to `n` in `l₁ ++ l₂` is the same as dropping the elements up to `n`
in `l₁`, dropping the elements up to `n - l₁.length` in `l₂`, and appending them. -/
theorem drop_append_eq_append_drop {l₁ l₂ : List α} {n : ℕ} :
  drop n (l₁ ++ l₂) = drop n l₁ ++ drop (n - l₁.length) l₂ :=
  by 
    induction l₁ generalizing n
    ·
      simp 
    cases n
    ·
      simp 
    simp 

theorem drop_append_of_le_length {l₁ l₂ : List α} {n : ℕ} (h : n ≤ l₁.length) : (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ :=
  by 
    simp [drop_append_eq_append_drop, tsub_eq_zero_iff_le.mpr h]

/-- Dropping the elements up to `l₁.length + i` in `l₁ + l₂` is the same as dropping the elements
up to `i` in `l₂`. -/
theorem drop_append {l₁ l₂ : List α} (i : ℕ) : drop (l₁.length+i) (l₁ ++ l₂) = drop i l₂ :=
  by 
    simp [drop_append_eq_append_drop, take_all_of_le le_self_add]

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
theorem nth_le_drop
(L : list α)
{i j : exprℕ()}
(h : «expr < »(«expr + »(i, j), L.length)) : «expr = »(nth_le L «expr + »(i, j) h, nth_le (L.drop i) j (begin
    have [ident A] [":", expr «expr < »(i, L.length)] [":=", expr lt_of_le_of_lt (nat.le.intro rfl) h],
    rw [expr (take_append_drop i L).symm] ["at", ident h],
    simpa [] [] ["only"] ["[", expr le_of_lt A, ",", expr min_eq_left, ",", expr add_lt_add_iff_left, ",", expr length_take, ",", expr length_append, "]"] [] ["using", expr h]
  end)) :=
begin
  have [ident A] [":", expr «expr = »(length (take i L), i)] [],
  by simp [] [] [] ["[", expr le_of_lt (lt_of_le_of_lt (nat.le.intro rfl) h), "]"] [] [],
  rw ["[", expr nth_le_of_eq (take_append_drop i L).symm h, ",", expr nth_le_append_right, "]"] []; simp [] [] [] ["[", expr A, "]"] [] []
end

/--  The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
theorem nth_le_drop' (L : List α) {i j : ℕ} (h : j < (L.drop i).length) :
  nth_le (L.drop i) j h = nth_le L (i+j) (lt_tsub_iff_left.mp (length_drop i L ▸ h)) :=
  by 
    rw [nth_le_drop]

theorem nth_drop (L : List α) (i j : ℕ) : nth (L.drop i) j = nth L (i+j) :=
  by 
    ext 
    simp only [nth_eq_some, nth_le_drop', Option.mem_def]
    split  <;>
      exact
        fun ⟨h, ha⟩ =>
          ⟨by 
              simpa [lt_tsub_iff_left] using h,
            ha⟩

@[simp]
theorem drop_drop (n : ℕ) : ∀ m (l : List α), drop n (drop m l) = drop (n+m) l
| m, [] =>
  by 
    simp 
| 0, l =>
  by 
    simp 
| m+1, a :: l =>
  calc drop n (drop (m+1) (a :: l)) = drop n (drop m l) := rfl 
    _ = drop (n+m) l := drop_drop m l 
    _ = drop (n+m+1) (a :: l) := rfl
    

theorem drop_take : ∀ (m : ℕ) (n : ℕ) (l : List α), drop m (take (m+n) l) = take n (drop m l)
| 0, n, _ =>
  by 
    simp 
| m+1, n, nil =>
  by 
    simp 
| m+1, n, _ :: l =>
  have h : ((m+1)+n) = (m+n)+1 :=
    by 
      acRfl 
  by 
    simpa [take_cons, h] using drop_take m n l

theorem map_drop {α β : Type _} (f : α → β) : ∀ (L : List α) (i : ℕ), (L.drop i).map f = (L.map f).drop i
| [], i =>
  by 
    simp 
| L, 0 =>
  by 
    simp 
| h :: t, n+1 =>
  by 
    dsimp 
    rw [map_drop]

theorem modify_nth_tail_eq_take_drop (f : List α → List α) (H : f [] = []) :
  ∀ n l, modify_nth_tail f n l = take n l ++ f (drop n l)
| 0, l => rfl
| n+1, [] => H.symm
| n+1, b :: l => congr_argₓ (cons b) (modify_nth_tail_eq_take_drop n l)

theorem modify_nth_eq_take_drop (f : α → α) : ∀ n l, modify_nth f n l = take n l ++ modify_head f (drop n l) :=
  modify_nth_tail_eq_take_drop _ rfl

theorem modify_nth_eq_take_cons_drop (f : α → α) {n l} h :
  modify_nth f n l = take n l ++ f (nth_le l n h) :: drop (n+1) l :=
  by 
    rw [modify_nth_eq_take_drop, drop_eq_nth_le_cons h] <;> rfl

theorem update_nth_eq_take_cons_drop (a : α) {n l} (h : n < length l) :
  update_nth l n a = take n l ++ a :: drop (n+1) l :=
  by 
    rw [update_nth_eq_modify_nth, modify_nth_eq_take_cons_drop _ h]

theorem reverse_take {α} {xs : List α} (n : ℕ) (h : n ≤ xs.length) :
  xs.reverse.take n = (xs.drop (xs.length - n)).reverse :=
  by 
    induction xs generalizing n <;> simp only [reverse_cons, drop, reverse_nil, zero_tsub, length, take_nil]
    cases' h.lt_or_eq_dec with h' h'
    ·
      replace h' := le_of_succ_le_succ h' 
      rwa [take_append_of_le_length, xs_ih _ h']
      rw [show (xs_tl.length+1) - n = succ (xs_tl.length - n) from _, drop]
      ·
        rwa [succ_eq_add_one, ←tsub_add_eq_add_tsub]
      ·
        rwa [length_reverse]
    ·
      subst h' 
      rw [length, tsub_self, drop]
      suffices  : (xs_tl.length+1) = (xs_tl.reverse ++ [xs_hd]).length
      ·
        rw [this, take_length, reverse_cons]
      rw [length_append, length_reverse]
      rfl

@[simp]
theorem update_nth_eq_nil (l : List α) (n : ℕ) (a : α) : l.update_nth n a = [] ↔ l = [] :=
  by 
    cases l <;> cases n <;> simp only [update_nth]

section Take'

variable[Inhabited α]

@[simp]
theorem take'_length : ∀ n l, length (@take' α _ n l) = n
| 0, l => rfl
| n+1, l => congr_argₓ succ (take'_length _ _)

@[simp]
theorem take'_nil : ∀ n, take' n (@nil α) = repeat (default _) n
| 0 => rfl
| n+1 => congr_argₓ (cons _) (take'_nil _)

theorem take'_eq_take : ∀ {n} {l : List α}, n ≤ length l → take' n l = take n l
| 0, l, h => rfl
| n+1, a :: l, h => congr_argₓ (cons _)$ take'_eq_take$ le_of_succ_le_succ h

@[simp]
theorem take'_left (l₁ l₂ : List α) : take' (length l₁) (l₁ ++ l₂) = l₁ :=
  (take'_eq_take
        (by 
          simp only [length_append, Nat.le_add_rightₓ])).trans
    (take_left _ _)

theorem take'_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : take' n (l₁ ++ l₂) = l₁ :=
  by 
    rw [←h] <;> apply take'_left

end Take'

/-! ### foldl, foldr -/


theorem foldl_ext (f g : α → β → α) (a : α) {l : List β} (H : ∀ (a : α), ∀ b (_ : b ∈ l), f a b = g a b) :
  foldl f a l = foldl g a l :=
  by 
    induction' l with hd tl ih generalizing a
    ·
      rfl 
    unfold foldl 
    rw [ih fun a b bin => H a b$ mem_cons_of_mem _ bin, H a hd (mem_cons_self _ _)]

theorem foldr_ext (f g : α → β → β) (b : β) {l : List α} (H : ∀ a (_ : a ∈ l), ∀ (b : β), f a b = g a b) :
  foldr f b l = foldr g b l :=
  by 
    induction' l with hd tl ih
    ·
      rfl 
    simp only [mem_cons_iff, or_imp_distrib, forall_and_distrib, forall_eq] at H 
    simp only [foldr, ih H.2, H.1]

@[simp]
theorem foldl_nil (f : α → β → α) (a : α) : foldl f a [] = a :=
  rfl

@[simp]
theorem foldl_cons (f : α → β → α) (a : α) (b : β) (l : List β) : foldl f a (b :: l) = foldl f (f a b) l :=
  rfl

@[simp]
theorem foldr_nil (f : α → β → β) (b : β) : foldr f b [] = b :=
  rfl

@[simp]
theorem foldr_cons (f : α → β → β) (b : β) (a : α) (l : List α) : foldr f b (a :: l) = f a (foldr f b l) :=
  rfl

@[simp]
theorem foldl_append (f : α → β → α) : ∀ (a : α) (l₁ l₂ : List β), foldl f a (l₁ ++ l₂) = foldl f (foldl f a l₁) l₂
| a, [], l₂ => rfl
| a, b :: l₁, l₂ =>
  by 
    simp only [cons_append, foldl_cons, foldl_append (f a b) l₁ l₂]

@[simp]
theorem foldr_append (f : α → β → β) : ∀ (b : β) (l₁ l₂ : List α), foldr f b (l₁ ++ l₂) = foldr f (foldr f b l₂) l₁
| b, [], l₂ => rfl
| b, a :: l₁, l₂ =>
  by 
    simp only [cons_append, foldr_cons, foldr_append b l₁ l₂]

@[simp]
theorem foldl_join (f : α → β → α) : ∀ (a : α) (L : List (List β)), foldl f a (join L) = foldl (foldl f) a L
| a, [] => rfl
| a, l :: L =>
  by 
    simp only [join, foldl_append, foldl_cons, foldl_join (foldl f a l) L]

@[simp]
theorem foldr_join (f : α → β → β) :
  ∀ (b : β) (L : List (List α)), foldr f b (join L) = foldr (fun l b => foldr f b l) b L
| a, [] => rfl
| a, l :: L =>
  by 
    simp only [join, foldr_append, foldr_join a L, foldr_cons]

theorem foldl_reverse (f : α → β → α) (a : α) (l : List β) : foldl f a (reverse l) = foldr (fun x y => f y x) a l :=
  by 
    induction l <;> [rfl, simp only [reverse_cons, foldl_append, foldl_cons, foldl_nil, foldr]]

theorem foldr_reverse (f : α → β → β) (a : β) (l : List α) : foldr f a (reverse l) = foldl (fun x y => f y x) a l :=
  let t := foldl_reverse (fun x y => f y x) a (reverse l)
  by 
    rw [reverse_reverse l] at t <;> rwa [t]

@[simp]
theorem foldr_eta : ∀ (l : List α), foldr cons [] l = l
| [] => rfl
| x :: l =>
  by 
    simp only [foldr_cons, foldr_eta l] <;> split  <;> rfl

@[simp]
theorem reverse_foldl {l : List α} : reverse (foldl (fun t h => h :: t) [] l) = l :=
  by 
    rw [←foldr_reverse] <;> simp 

@[simp]
theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : List β) :
  foldl f a (map g l) = foldl (fun x y => f x (g y)) a l :=
  by 
    revert a <;> induction l <;> intros  <;> [rfl, simp only [map, foldl]]

@[simp]
theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : List β) : foldr f a (map g l) = foldr (f ∘ g) a l :=
  by 
    revert a <;> induction l <;> intros  <;> [rfl, simp only [map, foldr]]

theorem foldl_map' {α β : Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α)
  (h : ∀ x y, f' (g x) (g y) = g (f x y)) : List.foldlₓ f' (g a) (l.map g) = g (List.foldlₓ f a l) :=
  by 
    induction l generalizing a
    ·
      simp 
    ·
      simp [l_ih, h]

theorem foldr_map' {α β : Type u} (g : α → β) (f : α → α → α) (f' : β → β → β) (a : α) (l : List α)
  (h : ∀ x y, f' (g x) (g y) = g (f x y)) : List.foldr f' (g a) (l.map g) = g (List.foldr f a l) :=
  by 
    induction l generalizing a
    ·
      simp 
    ·
      simp [l_ih, h]

theorem foldl_hom (l : List γ) (f : α → β) (op : α → γ → α) (op' : β → γ → β) (a : α)
  (h : ∀ a x, f (op a x) = op' (f a) x) : foldl op' (f a) l = f (foldl op a l) :=
  Eq.symm$
    by 
      revert a 
      induction l <;> intros  <;> [rfl, simp only [foldl]]

theorem foldr_hom (l : List γ) (f : α → β) (op : γ → α → α) (op' : γ → β → β) (a : α)
  (h : ∀ x a, f (op x a) = op' x (f a)) : foldr op' (f a) l = f (foldr op a l) :=
  by 
    revert a 
    induction l <;> intros  <;> [rfl, simp only [foldr]]

theorem injective_foldl_comp {α : Type _} {l : List (α → α)} {f : α → α} (hl : ∀ f (_ : f ∈ l), Function.Injective f)
  (hf : Function.Injective f) : Function.Injective (@List.foldlₓ (α → α) (α → α) Function.comp f l) :=
  by 
    induction l generalizing f
    ·
      exact hf
    ·
      apply l_ih fun _ h => hl _ (List.mem_cons_of_memₓ _ h)
      apply Function.Injective.comp hf 
      apply hl _ (List.mem_cons_selfₓ _ _)

/-- Induction principle for values produced by a `foldr`: if a property holds
for the seed element `b : β` and for all incremental `op : α → β → β`
performed on the elements `(a : α) ∈ l`. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def foldr_rec_on {C : β → Sort _} (l : List α) (op : α → β → β) (b : β) (hb : C b)
  (hl : ∀ (b : β) (hb : C b) (a : α) (ha : a ∈ l), C (op a b)) : C (foldr op b l) :=
  by 
    induction' l with hd tl IH
    ·
      exact hb
    ·
      refine' hl _ _ hd (mem_cons_self hd tl)
      refine' IH _ 
      intro y hy x hx 
      exact hl y hy x (mem_cons_of_mem hd hx)

/-- Induction principle for values produced by a `foldl`: if a property holds
for the seed element `b : β` and for all incremental `op : β → α → β`
performed on the elements `(a : α) ∈ l`. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def foldl_rec_on {C : β → Sort _} (l : List α) (op : β → α → β) (b : β) (hb : C b)
  (hl : ∀ (b : β) (hb : C b) (a : α) (ha : a ∈ l), C (op b a)) : C (foldl op b l) :=
  by 
    induction' l with hd tl IH generalizing b
    ·
      exact hb
    ·
      refine' IH _ _ _
      ·
        intro y hy x hx 
        exact hl y hy x (mem_cons_of_mem hd hx)
      ·
        exact hl b hb hd (mem_cons_self hd tl)

@[simp]
theorem foldr_rec_on_nil {C : β → Sort _} (op : α → β → β) b (hb : C b) hl : foldr_rec_on [] op b hb hl = hb :=
  rfl

@[simp]
theorem foldr_rec_on_cons {C : β → Sort _} (x : α) (l : List α) (op : α → β → β) b (hb : C b)
  (hl : ∀ (b : β) (hb : C b) (a : α) (ha : a ∈ x :: l), C (op a b)) :
  foldr_rec_on (x :: l) op b hb hl =
    hl _ (foldr_rec_on l op b hb fun b hb a ha => hl b hb a (mem_cons_of_mem _ ha)) x (mem_cons_self _ _) :=
  rfl

@[simp]
theorem foldl_rec_on_nil {C : β → Sort _} (op : β → α → β) b (hb : C b) hl : foldl_rec_on [] op b hb hl = hb :=
  rfl

section Scanl

variable{f : β → α → β}{b : β}{a : α}{l : List α}

theorem length_scanl : ∀ a l, length (scanl f a l) = l.length+1
| a, [] => rfl
| a, x :: l =>
  by 
    erw [length_cons, length_cons, length_scanl]

@[simp]
theorem scanl_nil (b : β) : scanl f b nil = [b] :=
  rfl

@[simp]
theorem scanl_cons : scanl f b (a :: l) = [b] ++ scanl f (f b a) l :=
  by 
    simp only [scanl, eq_self_iff_true, singleton_append, and_selfₓ]

@[simp]
theorem nth_zero_scanl : (scanl f b l).nth 0 = some b :=
  by 
    cases l
    ·
      simp only [nth, scanl_nil]
    ·
      simp only [nth, scanl_cons, singleton_append]

@[simp]
theorem nth_le_zero_scanl {h : 0 < (scanl f b l).length} : (scanl f b l).nthLe 0 h = b :=
  by 
    cases l
    ·
      simp only [nth_le, scanl_nil]
    ·
      simp only [nth_le, scanl_cons, singleton_append]

theorem nth_succ_scanl {i : ℕ} :
  (scanl f b l).nth (i+1) = ((scanl f b l).nth i).bind fun x => (l.nth i).map fun y => f x y :=
  by 
    induction' l with hd tl hl generalizing b i
    ·
      symm 
      simp only [Option.bind_eq_none', nth, forall_2_true_iff, not_false_iff, Option.map_none', scanl_nil,
        Option.not_mem_none, forall_true_iff]
    ·
      simp only [nth, scanl_cons, singleton_append]
      cases i
      ·
        simp only [Option.map_some', nth_zero_scanl, nth, Option.some_bind']
      ·
        simp only [hl, nth]

theorem nth_le_succ_scanl {i : ℕ} {h : (i+1) < (scanl f b l).length} :
  (scanl f b l).nthLe (i+1) h =
    f ((scanl f b l).nthLe i (Nat.lt_of_succ_ltₓ h))
      (l.nth_le i (Nat.lt_of_succ_lt_succₓ (lt_of_lt_of_leₓ h (le_of_eqₓ (length_scanl b l))))) :=
  by 
    induction' i with i hi generalizing b l
    ·
      cases l
      ·
        simp only [length, zero_addₓ, scanl_nil] at h 
        exact absurd h (lt_irreflₓ 1)
      ·
        simp only [scanl_cons, singleton_append, nth_le_zero_scanl, nth_le]
    ·
      cases l
      ·
        simp only [length, add_lt_iff_neg_right, scanl_nil] at h 
        exact absurd h (not_lt_of_lt Nat.succ_pos')
      ·
        simpRw [scanl_cons]
        rw [nth_le_append_right _]
        ·
          simpa only [hi, length, succ_add_sub_one]
        ·
          simp only [length, Nat.zero_leₓ, le_add_iff_nonneg_left]

end Scanl

@[simp]
theorem scanr_nil (f : α → β → β) (b : β) : scanr f b [] = [b] :=
  rfl

@[simp]
theorem scanr_aux_cons (f : α → β → β) (b : β) :
  ∀ (a : α) (l : List α), scanr_aux f b (a :: l) = (foldr f b (a :: l), scanr f b l)
| a, [] => rfl
| a, x :: l =>
  let t := scanr_aux_cons x l 
  by 
    simp only [scanr, scanr_aux, t, foldr_cons]

@[simp]
theorem scanr_cons (f : α → β → β) (b : β) (a : α) (l : List α) :
  scanr f b (a :: l) = foldr f b (a :: l) :: scanr f b l :=
  by 
    simp only [scanr, scanr_aux_cons, foldr_cons] <;> split  <;> rfl

section FoldlEqFoldr

variable{f : α → α → α}(hcomm : Commutative f)(hassoc : Associative f)

include hassoc

theorem foldl1_eq_foldr1 : ∀ a b l, foldl f a (l ++ [b]) = foldr f b (a :: l)
| a, b, nil => rfl
| a, b, c :: l =>
  by 
    simp only [cons_append, foldl_cons, foldr_cons, foldl1_eq_foldr1 _ _ l] <;> rw [hassoc]

include hcomm

theorem foldl_eq_of_comm_of_assoc : ∀ a b l, foldl f a (b :: l) = f b (foldl f a l)
| a, b, nil => hcomm a b
| a, b, c :: l =>
  by 
    simp only [foldl_cons] <;> rw [←foldl_eq_of_comm_of_assoc, right_comm _ hcomm hassoc] <;> rfl

theorem foldl_eq_foldr : ∀ a l, foldl f a l = foldr f a l
| a, nil => rfl
| a, b :: l =>
  by 
    simp only [foldr_cons, foldl_eq_of_comm_of_assoc hcomm hassoc] <;> rw [foldl_eq_foldr a l]

end FoldlEqFoldr

section FoldlEqFoldlr'

variable{f : α → β → α}

variable(hf : ∀ a b c, f (f a b) c = f (f a c) b)

include hf

theorem foldl_eq_of_comm' : ∀ a b l, foldl f a (b :: l) = f (foldl f a l) b
| a, b, [] => rfl
| a, b, c :: l =>
  by 
    rw [foldl, foldl, foldl, ←foldl_eq_of_comm', foldl, hf]

theorem foldl_eq_foldr' : ∀ a l, foldl f a l = foldr (flip f) a l
| a, [] => rfl
| a, b :: l =>
  by 
    rw [foldl_eq_of_comm' hf, foldr, foldl_eq_foldr'] <;> rfl

end FoldlEqFoldlr'

section FoldlEqFoldlr'

variable{f : α → β → β}

variable(hf : ∀ a b c, f a (f b c) = f b (f a c))

include hf

theorem foldr_eq_of_comm' : ∀ a b l, foldr f a (b :: l) = foldr f (f b a) l
| a, b, [] => rfl
| a, b, c :: l =>
  by 
    rw [foldr, foldr, foldr, hf, ←foldr_eq_of_comm'] <;> rfl

end FoldlEqFoldlr'

section 

variable{op : α → α → α}[ha : IsAssociative α op][hc : IsCommutative α op]

local notation a "*" b => op a b

local notation l "<*>" a => foldl op a l

include ha

theorem foldl_assoc : ∀ {l : List α} {a₁ a₂}, (l<*>a₁*a₂) = a₁*l<*>a₂
| [], a₁, a₂ => rfl
| a :: l, a₁, a₂ =>
  calc ((a :: l)<*>a₁*a₂) = l<*>a₁*a₂*a :=
    by 
      simp only [foldl_cons, ha.assoc]
    _ = a₁*(a :: l)<*>a₂ :=
    by 
      rw [foldl_assoc, foldl_cons]
    

theorem foldl_op_eq_op_foldr_assoc : ∀ {l : List α} {a₁ a₂}, ((l<*>a₁)*a₂) = a₁*l.foldr (·*·) a₂
| [], a₁, a₂ => rfl
| a :: l, a₁, a₂ =>
  by 
    simp only [foldl_cons, foldr_cons, foldl_assoc, ha.assoc] <;> rw [foldl_op_eq_op_foldr_assoc]

include hc

theorem foldl_assoc_comm_cons {l : List α} {a₁ a₂} : ((a₁ :: l)<*>a₂) = a₁*l<*>a₂ :=
  by 
    rw [foldl_cons, hc.comm, foldl_assoc]

end 

/-! ### mfoldl, mfoldr, mmap -/


section MfoldlMfoldr

variable{m : Type v → Type w}[Monadₓ m]

@[simp]
theorem mfoldl_nil (f : β → α → m β) {b} : mfoldl f b [] = pure b :=
  rfl

@[simp]
theorem mfoldr_nil (f : α → β → m β) {b} : mfoldr f b [] = pure b :=
  rfl

@[simp]
theorem mfoldl_cons {f : β → α → m β} {b a l} : mfoldl f b (a :: l) = f b a >>= fun b' => mfoldl f b' l :=
  rfl

@[simp]
theorem mfoldr_cons {f : α → β → m β} {b a l} : mfoldr f b (a :: l) = mfoldr f b l >>= f a :=
  rfl

theorem mfoldr_eq_foldr (f : α → β → m β) b l : mfoldr f b l = foldr (fun a mb => mb >>= f a) (pure b) l :=
  by 
    induction l <;> simp 

attribute [simp] mmap mmap'

variable[IsLawfulMonad m]

theorem mfoldl_eq_foldl (f : β → α → m β) b l : mfoldl f b l = foldl (fun mb a => mb >>= fun b => f b a) (pure b) l :=
  by 
    suffices h : ∀ (mb : m β), (mb >>= fun b => mfoldl f b l) = foldl (fun mb a => mb >>= fun b => f b a) mb l
    ·
      simp [←h (pure b)]
    induction l <;> intro 
    ·
      simp 
    ·
      simp' only [mfoldl, foldl, ←l_ih] with functor_norm

@[simp]
theorem mfoldl_append {f : β → α → m β} : ∀ {b l₁ l₂}, mfoldl f b (l₁ ++ l₂) = mfoldl f b l₁ >>= fun x => mfoldl f x l₂
| _, [], _ =>
  by 
    simp only [nil_append, mfoldl_nil, pure_bind]
| _, _ :: _, _ =>
  by 
    simp only [cons_append, mfoldl_cons, mfoldl_append, IsLawfulMonad.bind_assoc]

@[simp]
theorem mfoldr_append {f : α → β → m β} : ∀ {b l₁ l₂}, mfoldr f b (l₁ ++ l₂) = mfoldr f b l₂ >>= fun x => mfoldr f x l₁
| _, [], _ =>
  by 
    simp only [nil_append, mfoldr_nil, bind_pureₓ]
| _, _ :: _, _ =>
  by 
    simp only [mfoldr_cons, cons_append, mfoldr_append, IsLawfulMonad.bind_assoc]

end MfoldlMfoldr

/-! ### intersperse -/


@[simp]
theorem intersperse_nil {α : Type u} (a : α) : intersperse a [] = [] :=
  rfl

@[simp]
theorem intersperse_singleton {α : Type u} (a b : α) : intersperse a [b] = [b] :=
  rfl

@[simp]
theorem intersperse_cons_cons {α : Type u} (a b c : α) (tl : List α) :
  intersperse a (b :: c :: tl) = b :: a :: intersperse a (c :: tl) :=
  rfl

/-! ### split_at and split_on -/


@[simp]
theorem split_at_eq_take_drop : ∀ (n : ℕ) (l : List α), split_at n l = (take n l, drop n l)
| 0, a => rfl
| succ n, [] => rfl
| succ n, x :: xs =>
  by 
    simp only [split_at, split_at_eq_take_drop n xs, take, drop]

@[simp]
theorem split_on_nil {α : Type u} [DecidableEq α] (a : α) : [].splitOn a = [[]] :=
  rfl

/-- An auxiliary definition for proving a specification lemma for `split_on_p`.

`split_on_p_aux' P xs ys` splits the list `ys ++ xs` at every element satisfying `P`,
where `ys` is an accumulating parameter for the initial segment of elements not satisfying `P`.
-/
def split_on_p_aux' {α : Type u} (P : α → Prop) [DecidablePred P] : List α → List α → List (List α)
| [], xs => [xs]
| h :: t, xs => if P h then xs :: split_on_p_aux' t [] else split_on_p_aux' t (xs ++ [h])

theorem split_on_p_aux_eq {α : Type u} (P : α → Prop) [DecidablePred P] (xs ys : List α) :
  split_on_p_aux' P xs ys = split_on_p_aux P xs ((· ++ ·) ys) :=
  by 
    induction' xs with a t ih generalizing ys <;> simp only [append_nil, eq_self_iff_true, and_selfₓ]
    splitIfs <;> rw [ih]
    ·
      refine' ⟨rfl, rfl⟩
    ·
      congr 
      ext 
      simp 

theorem split_on_p_aux_nil {α : Type u} (P : α → Prop) [DecidablePred P] (xs : List α) :
  split_on_p_aux P xs id = split_on_p_aux' P xs [] :=
  by 
    rw [split_on_p_aux_eq]
    rfl

/-- The original list `L` can be recovered by joining the lists produced by `split_on_p p L`,
interspersed with the elements `L.filter p`. -/
theorem split_on_p_spec {α : Type u} (p : α → Prop) [DecidablePred p] (as : List α) :
  join (zip_with (· ++ ·) (split_on_p p as) (((as.filter p).map fun x => [x]) ++ [[]])) = as :=
  by 
    rw [split_on_p, split_on_p_aux_nil]
    suffices  :
      ∀ xs, join (zip_with (· ++ ·) (split_on_p_aux' p as xs) (((as.filter p).map fun x => [x]) ++ [[]])) = xs ++ as
    ·
      rw [this]
      rfl 
    induction as <;> intro  <;> simp only [split_on_p_aux', append_nil]
    splitIfs <;> simp [zip_with, join]

/-! ### all & any -/


@[simp]
theorem all_nil (p : α → Bool) : all [] p = tt :=
  rfl

@[simp]
theorem all_cons (p : α → Bool) (a : α) (l : List α) : all (a :: l) p = (p a && all l p) :=
  rfl

theorem all_iff_forall {p : α → Bool} {l : List α} : all l p ↔ ∀ a (_ : a ∈ l), p a :=
  by 
    induction' l with a l ih
    ·
      exact iff_of_true rfl (forall_mem_nil _)
    simp only [all_cons, band_coe_iff, ih, forall_mem_cons]

theorem all_iff_forall_prop {p : α → Prop} [DecidablePred p] {l : List α} :
  (all l fun a => p a) ↔ ∀ a (_ : a ∈ l), p a :=
  by 
    simp only [all_iff_forall, Bool.of_to_bool_iff]

@[simp]
theorem any_nil (p : α → Bool) : any [] p = ff :=
  rfl

@[simp]
theorem any_cons (p : α → Bool) (a : α) (l : List α) : any (a :: l) p = (p a || any l p) :=
  rfl

theorem any_iff_exists {p : α → Bool} {l : List α} : any l p ↔ ∃ (a : _)(_ : a ∈ l), p a :=
  by 
    induction' l with a l ih
    ·
      exact iff_of_false Bool.not_ff (not_exists_mem_nil _)
    simp only [any_cons, bor_coe_iff, ih, exists_mem_cons_iff]

theorem any_iff_exists_prop {p : α → Prop} [DecidablePred p] {l : List α} :
  (any l fun a => p a) ↔ ∃ (a : _)(_ : a ∈ l), p a :=
  by 
    simp [any_iff_exists]

theorem any_of_mem {p : α → Bool} {a : α} {l : List α} (h₁ : a ∈ l) (h₂ : p a) : any l p :=
  any_iff_exists.2 ⟨_, h₁, h₂⟩

instance (priority := 500)decidable_forall_mem {p : α → Prop} [DecidablePred p] (l : List α) :
  Decidable (∀ x (_ : x ∈ l), p x) :=
  decidableOfIff _ all_iff_forall_prop

instance decidable_exists_mem {p : α → Prop} [DecidablePred p] (l : List α) : Decidable (∃ (x : _)(_ : x ∈ l), p x) :=
  decidableOfIff _ any_iff_exists_prop

/-! ### map for partial functions -/


/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp]
def pmap {p : α → Prop} (f : ∀ a, p a → β) : ∀ (l : List α), (∀ a (_ : a ∈ l), p a) → List β
| [], H => []
| a :: l, H => f a (forall_mem_cons.1 H).1 :: pmap l (forall_mem_cons.1 H).2

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new list
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach (l : List α) : List { x // x ∈ l } :=
  pmap Subtype.mk l fun a => id

theorem sizeof_lt_sizeof_of_mem [SizeOf α] {x : α} {l : List α} (hx : x ∈ l) : sizeof x < sizeof l :=
  by 
    induction' l with h t ih <;> cases hx
    ·
      rw [hx]
      exact lt_add_of_lt_of_nonneg (lt_one_add _) (Nat.zero_leₓ _)
    ·
      exact lt_add_of_pos_of_le (zero_lt_one_add _) (le_of_ltₓ (ih hx))

@[simp]
theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : List α) H : @pmap _ _ p (fun a _ => f a) l H = map f l :=
  by 
    induction l <;> [rfl, simp only [pmap, map]] <;> split  <;> rfl

theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (l : List α) {H₁ H₂}
  (h : ∀ a h₁ h₂, f a h₁ = g a h₂) : pmap f l H₁ = pmap g l H₂ :=
  by 
    induction' l with _ _ ih <;> [rfl, rw [pmap, pmap, h, ih]]

theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) l H :
  map g (pmap f l H) = pmap (fun a h => g (f a h)) l H :=
  by 
    induction l <;> [rfl, simp only [pmap, map]] <;> split  <;> rfl

theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β) l H :
  pmap g (map f l) H = pmap (fun a h => g (f a) h) l fun a h => H _ (mem_map_of_mem _ h) :=
  by 
    induction l <;> [rfl, simp only [pmap, map]] <;> split  <;> rfl

theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) l H : pmap f l H = l.attach.map fun x => f x.1 (H _ x.2) :=
  by 
    rw [attach, map_pmap] <;> exact pmap_congr l fun a h₁ h₂ => rfl

theorem attach_map_val (l : List α) : l.attach.map Subtype.val = l :=
  by 
    rw [attach, map_pmap] <;> exact (pmap_eq_map _ _ _ _).trans (map_id l)

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem mem_attach (l : list α) : ∀ x, «expr ∈ »(x, l.attach)
| ⟨a, h⟩ := by have [] [] [":=", expr mem_map.1 (by rw ["[", expr attach_map_val, "]"] []; exact [expr h])]; { rcases [expr this, "with", "⟨", "⟨", "_", ",", "_", "⟩", ",", ident m, ",", ident rfl, "⟩"],
  exact [expr m] }

@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H b} : b ∈ pmap f l H ↔ ∃ (a : _)(h : a ∈ l), f a (H a h) = b :=
  by 
    simp only [pmap_eq_map_attach, mem_map, mem_attach, true_andₓ, Subtype.exists]

@[simp]
theorem length_pmap {p : α → Prop} {f : ∀ a, p a → β} {l H} : length (pmap f l H) = length l :=
  by 
    induction l <;> [rfl, simp only [pmap, length]]

@[simp]
theorem length_attach (L : List α) : L.attach.length = L.length :=
  length_pmap

@[simp]
theorem pmap_eq_nil {p : α → Prop} {f : ∀ a, p a → β} {l H} : pmap f l H = [] ↔ l = [] :=
  by 
    rw [←length_eq_zero, length_pmap, length_eq_zero]

@[simp]
theorem attach_eq_nil (l : List α) : l.attach = [] ↔ l = [] :=
  pmap_eq_nil

theorem last_pmap {α β : Type _} (p : α → Prop) (f : ∀ a, p a → β) (l : List α) (hl₁ : ∀ a (_ : a ∈ l), p a)
  (hl₂ : l ≠ []) : (l.pmap f hl₁).last (mt List.pmap_eq_nil.1 hl₂) = f (l.last hl₂) (hl₁ _ (List.last_mem hl₂)) :=
  by 
    induction' l with l_hd l_tl l_ih
    ·
      apply (hl₂ rfl).elim
    ·
      cases l_tl
      ·
        simp 
      ·
        apply l_ih

theorem nth_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a (_ : a ∈ l), p a) (n : ℕ) :
  nth (pmap f l h) n = Option.pmap f (nth l n) fun x H => h x (nth_mem H) :=
  by 
    induction' l with hd tl hl generalizing n
    ·
      simp 
    ·
      cases n <;> simp [hl]

theorem nth_le_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (h : ∀ a (_ : a ∈ l), p a) {n : ℕ}
  (hn : n < (pmap f l h).length) :
  nth_le (pmap f l h) n hn =
    f (nth_le l n (@length_pmap _ _ p f l h ▸ hn)) (h _ (nth_le_mem l n (@length_pmap _ _ p f l h ▸ hn))) :=
  by 
    induction' l with hd tl hl generalizing n
    ·
      simp only [length, pmap] at hn 
      exact absurd hn (not_lt_of_le n.zero_le)
    ·
      cases n
      ·
        simp 
      ·
        simpa [hl]

/-! ### find -/


section Find

variable{p : α → Prop}[DecidablePred p]{l : List α}{a : α}

@[simp]
theorem find_nil (p : α → Prop) [DecidablePred p] : find p [] = none :=
  rfl

@[simp]
theorem find_cons_of_pos l (h : p a) : find p (a :: l) = some a :=
  if_pos h

@[simp]
theorem find_cons_of_neg l (h : ¬p a) : find p (a :: l) = find p l :=
  if_neg h

@[simp]
theorem find_eq_none : find p l = none ↔ ∀ x (_ : x ∈ l), ¬p x :=
  by 
    induction' l with a l IH
    ·
      exact iff_of_true rfl (forall_mem_nil _)
    rw [forall_mem_cons]
    byCases' h : p a
    ·
      simp only [find_cons_of_pos _ h, h, not_true, false_andₓ]
    ·
      rwa [find_cons_of_neg _ h, iff_true_intro h, true_andₓ]

theorem find_some (H : find p l = some a) : p a :=
  by 
    induction' l with b l IH
    ·
      contradiction 
    byCases' h : p b
    ·
      rw [find_cons_of_pos _ h] at H 
      cases H 
      exact h
    ·
      rw [find_cons_of_neg _ h] at H 
      exact IH H

@[simp]
theorem find_mem (H : find p l = some a) : a ∈ l :=
  by 
    induction' l with b l IH
    ·
      contradiction 
    byCases' h : p b
    ·
      rw [find_cons_of_pos _ h] at H 
      cases H 
      apply mem_cons_self
    ·
      rw [find_cons_of_neg _ h] at H 
      exact mem_cons_of_mem _ (IH H)

end Find

/-! ### lookmap -/


section Lookmap

variable(f : α → Option α)

@[simp]
theorem lookmap_nil : [].lookmap f = [] :=
  rfl

@[simp]
theorem lookmap_cons_none {a : α} (l : List α) (h : f a = none) : (a :: l).lookmap f = a :: l.lookmap f :=
  by 
    simp [lookmap, h]

@[simp]
theorem lookmap_cons_some {a b : α} (l : List α) (h : f a = some b) : (a :: l).lookmap f = b :: l :=
  by 
    simp [lookmap, h]

theorem lookmap_some : ∀ (l : List α), l.lookmap some = l
| [] => rfl
| a :: l => rfl

theorem lookmap_none : ∀ (l : List α), (l.lookmap fun _ => none) = l
| [] => rfl
| a :: l => congr_argₓ (cons a) (lookmap_none l)

theorem lookmap_congr {f g : α → Option α} : ∀ {l : List α}, (∀ a (_ : a ∈ l), f a = g a) → l.lookmap f = l.lookmap g
| [], H => rfl
| a :: l, H =>
  by 
    cases' forall_mem_cons.1 H with H₁ H₂ 
    cases' h : g a with b
    ·
      simp [h, H₁.trans h, lookmap_congr H₂]
    ·
      simp [lookmap_cons_some _ _ h, lookmap_cons_some _ _ (H₁.trans h)]

theorem lookmap_of_forall_not {l : List α} (H : ∀ a (_ : a ∈ l), f a = none) : l.lookmap f = l :=
  (lookmap_congr H).trans (lookmap_none l)

theorem lookmap_map_eq (g : α → β) (h : ∀ a b (_ : b ∈ f a), g a = g b) : ∀ (l : List α), map g (l.lookmap f) = map g l
| [] => rfl
| a :: l =>
  by 
    cases' h' : f a with b
    ·
      simp [h', lookmap_map_eq]
    ·
      simp [lookmap_cons_some _ _ h', h _ _ h']

theorem lookmap_id' (h : ∀ a b (_ : b ∈ f a), a = b) (l : List α) : l.lookmap f = l :=
  by 
    rw [←map_id (l.lookmap f), lookmap_map_eq, map_id] <;> exact h

theorem length_lookmap (l : List α) : length (l.lookmap f) = length l :=
  by 
    rw [←length_map, lookmap_map_eq _ fun _ => (), length_map] <;> simp 

end Lookmap

/-! ### filter_map -/


@[simp]
theorem filter_map_nil (f : α → Option β) : filter_map f [] = [] :=
  rfl

@[simp]
theorem filter_map_cons_none {f : α → Option β} (a : α) (l : List α) (h : f a = none) :
  filter_map f (a :: l) = filter_map f l :=
  by 
    simp only [filter_map, h]

@[simp]
theorem filter_map_cons_some (f : α → Option β) (a : α) (l : List α) {b : β} (h : f a = some b) :
  filter_map f (a :: l) = b :: filter_map f l :=
  by 
    simp only [filter_map, h] <;> split  <;> rfl

theorem filter_map_cons (f : α → Option β) (a : α) (l : List α) :
  filter_map f (a :: l) = Option.casesOn (f a) (filter_map f l) fun b => b :: filter_map f l :=
  by 
    generalize eq : f a = b 
    cases b
    ·
      rw [filter_map_cons_none _ _ Eq]
    ·
      rw [filter_map_cons_some _ _ _ Eq]

theorem filter_map_append {α β : Type _} (l l' : List α) (f : α → Option β) :
  filter_map f (l ++ l') = filter_map f l ++ filter_map f l' :=
  by 
    induction' l with hd tl hl generalizing l'
    ·
      simp 
    ·
      rw [cons_append, filter_map, filter_map]
      cases f hd <;> simp only [filter_map, hl, cons_append, eq_self_iff_true, and_selfₓ]

theorem filter_map_eq_map (f : α → β) : filter_map (some ∘ f) = map f :=
  by 
    funext l 
    induction' l with a l IH
    ·
      rfl 
    simp only [filter_map_cons_some (some ∘ f) _ _ rfl, IH, map_cons]
    split  <;> rfl

theorem filter_map_eq_filter (p : α → Prop) [DecidablePred p] : filter_map (Option.guard p) = filter p :=
  by 
    funext l 
    induction' l with a l IH
    ·
      rfl 
    byCases' pa : p a
    ·
      simp only [filter_map, Option.guard, IH, if_pos pa, filter_cons_of_pos _ pa]
      split  <;> rfl
    ·
      simp only [filter_map, Option.guard, IH, if_neg pa, filter_cons_of_neg _ pa]

theorem filter_map_filter_map (f : α → Option β) (g : β → Option γ) (l : List α) :
  filter_map g (filter_map f l) = filter_map (fun x => (f x).bind g) l :=
  by 
    induction' l with a l IH
    ·
      rfl 
    cases' h : f a with b
    ·
      rw [filter_map_cons_none _ _ h, filter_map_cons_none, IH]
      simp only [h, Option.none_bind']
    rw [filter_map_cons_some _ _ _ h]
    cases' h' : g b with c <;> [rw [filter_map_cons_none _ _ h', filter_map_cons_none, IH],
        rw [filter_map_cons_some _ _ _ h', filter_map_cons_some, IH]] <;>
      simp only [h, h', Option.some_bind']

theorem map_filter_map (f : α → Option β) (g : β → γ) (l : List α) :
  map g (filter_map f l) = filter_map (fun x => (f x).map g) l :=
  by 
    rw [←filter_map_eq_map, filter_map_filter_map] <;> rfl

theorem filter_map_map (f : α → β) (g : β → Option γ) (l : List α) : filter_map g (map f l) = filter_map (g ∘ f) l :=
  by 
    rw [←filter_map_eq_map, filter_map_filter_map] <;> rfl

theorem filter_filter_map (f : α → Option β) (p : β → Prop) [DecidablePred p] (l : List α) :
  filter p (filter_map f l) = filter_map (fun x => (f x).filter p) l :=
  by 
    rw [←filter_map_eq_filter, filter_map_filter_map] <;> rfl

theorem filter_map_filter (p : α → Prop) [DecidablePred p] (f : α → Option β) (l : List α) :
  filter_map f (filter p l) = filter_map (fun x => if p x then f x else none) l :=
  by 
    rw [←filter_map_eq_filter, filter_map_filter_map]
    congr 
    funext x 
    show (Option.guard p x).bind f = ite (p x) (f x) none 
    byCases' h : p x
    ·
      simp only [Option.guard, if_pos h, Option.some_bind']
    ·
      simp only [Option.guard, if_neg h, Option.none_bind']

@[simp]
theorem filter_map_some (l : List α) : filter_map some l = l :=
  by 
    rw [filter_map_eq_map] <;> apply map_id

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem mem_filter_map
(f : α → option β)
(l : list α)
{b : β} : «expr ↔ »(«expr ∈ »(b, filter_map f l), «expr∃ , »((a), «expr ∧ »(«expr ∈ »(a, l), «expr = »(f a, some b)))) :=
begin
  induction [expr l] [] ["with", ident a, ident l, ident IH] [],
  { split,
    { intro [ident H],
      cases [expr H] [] },
    { rintro ["⟨", "_", ",", ident H, ",", "_", "⟩"],
      cases [expr H] [] } },
  cases [expr h, ":", expr f a] ["with", ident b'],
  { have [] [":", expr «expr ≠ »(f a, some b)] [],
    { rw [expr h] [],
      intro [],
      contradiction },
    simp [] [] ["only"] ["[", expr filter_map_cons_none _ _ h, ",", expr IH, ",", expr mem_cons_iff, ",", expr or_and_distrib_right, ",", expr exists_or_distrib, ",", expr exists_eq_left, ",", expr this, ",", expr false_or, "]"] [] [] },
  { have [] [":", expr «expr ↔ »(«expr = »(f a, some b), «expr = »(b, b'))] [],
    { split; intro [ident t],
      { rw [expr t] ["at", ident h]; injection [expr h] [] },
      { exact [expr «expr ▸ »(t.symm, h)] } },
    simp [] [] ["only"] ["[", expr filter_map_cons_some _ _ _ h, ",", expr IH, ",", expr mem_cons_iff, ",", expr or_and_distrib_right, ",", expr exists_or_distrib, ",", expr this, ",", expr exists_eq_left, "]"] [] [] }
end

theorem map_filter_map_of_inv (f : α → Option β) (g : β → α) (H : ∀ (x : α), (f x).map g = some x) (l : List α) :
  map g (filter_map f l) = l :=
  by 
    simp only [map_filter_map, H, filter_map_some]

theorem sublist.filter_map (f : α → Option β) {l₁ l₂ : List α} (s : l₁ <+ l₂) : filter_map f l₁ <+ filter_map f l₂ :=
  by 
    induction' s with l₁ l₂ a s IH l₁ l₂ a s IH <;>
      simp only [filter_map] <;> cases' f a with b <;> simp only [filter_map, IH, sublist.cons, sublist.cons2]

theorem sublist.map (f : α → β) {l₁ l₂ : List α} (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ :=
  filter_map_eq_map f ▸ s.filter_map _

/-! ### reduce_option -/


@[simp]
theorem reduce_option_cons_of_some (x : α) (l : List (Option α)) : reduce_option (some x :: l) = x :: l.reduce_option :=
  by 
    simp only [reduce_option, filter_map, id.def, eq_self_iff_true, and_selfₓ]

@[simp]
theorem reduce_option_cons_of_none (l : List (Option α)) : reduce_option (none :: l) = l.reduce_option :=
  by 
    simp only [reduce_option, filter_map, id.def]

@[simp]
theorem reduce_option_nil : @reduce_option α [] = [] :=
  rfl

@[simp]
theorem reduce_option_map {l : List (Option α)} {f : α → β} :
  reduce_option (map (Option.map f) l) = map f (reduce_option l) :=
  by 
    induction' l with hd tl hl
    ·
      simp only [reduce_option_nil, map_nil]
    ·
      cases hd <;> simpa only [true_andₓ, Option.map_some', map, eq_self_iff_true, reduce_option_cons_of_some] using hl

theorem reduce_option_append (l l' : List (Option α)) : (l ++ l').reduceOption = l.reduce_option ++ l'.reduce_option :=
  filter_map_append l l' id

theorem reduce_option_length_le (l : List (Option α)) : l.reduce_option.length ≤ l.length :=
  by 
    induction' l with hd tl hl
    ·
      simp only [reduce_option_nil, length]
    ·
      cases hd
      ·
        exact Nat.le_succ_of_leₓ hl
      ·
        simpa only [length, add_le_add_iff_right, reduce_option_cons_of_some] using hl

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem reduce_option_length_eq_iff
{l : list (option α)} : «expr ↔ »(«expr = »(l.reduce_option.length, l.length), ∀ x «expr ∈ » l, option.is_some x) :=
begin
  induction [expr l] [] ["with", ident hd, ident tl, ident hl] [],
  { simp [] [] ["only"] ["[", expr forall_const, ",", expr reduce_option_nil, ",", expr not_mem_nil, ",", expr forall_prop_of_false, ",", expr eq_self_iff_true, ",", expr length, ",", expr not_false_iff, "]"] [] [] },
  { cases [expr hd] [],
    { simp [] [] ["only"] ["[", expr mem_cons_iff, ",", expr forall_eq_or_imp, ",", expr bool.coe_sort_ff, ",", expr false_and, ",", expr reduce_option_cons_of_none, ",", expr length, ",", expr option.is_some_none, ",", expr iff_false, "]"] [] [],
      intro [ident H],
      have [] [] [":=", expr reduce_option_length_le tl],
      rw [expr H] ["at", ident this],
      exact [expr absurd (nat.lt_succ_self _) (not_lt_of_le this)] },
    { simp [] [] ["only"] ["[", expr hl, ",", expr true_and, ",", expr mem_cons_iff, ",", expr forall_eq_or_imp, ",", expr add_left_inj, ",", expr bool.coe_sort_tt, ",", expr length, ",", expr option.is_some_some, ",", expr reduce_option_cons_of_some, "]"] [] [] } }
end

theorem reduce_option_length_lt_iff {l : List (Option α)} : l.reduce_option.length < l.length ↔ none ∈ l :=
  by 
    rw [(reduce_option_length_le l).lt_iff_ne, Ne, reduce_option_length_eq_iff]
    induction l <;> simp 
    rw [eq_comm, ←Option.not_is_some_iff_eq_none, Decidable.imp_iff_not_or]

theorem reduce_option_singleton (x : Option α) : [x].reduceOption = x.to_list :=
  by 
    cases x <;> rfl

theorem reduce_option_concat (l : List (Option α)) (x : Option α) :
  (l.concat x).reduceOption = l.reduce_option ++ x.to_list :=
  by 
    induction' l with hd tl hl generalizing x
    ·
      cases x <;> simp [Option.toList]
    ·
      simp only [concat_eq_append, reduce_option_append] at hl 
      cases hd <;> simp [hl, reduce_option_append]

theorem reduce_option_concat_of_some (l : List (Option α)) (x : α) :
  (l.concat (some x)).reduceOption = l.reduce_option.concat x :=
  by 
    simp only [reduce_option_nil, concat_eq_append, reduce_option_append, reduce_option_cons_of_some]

theorem reduce_option_mem_iff {l : List (Option α)} {x : α} : x ∈ l.reduce_option ↔ some x ∈ l :=
  by 
    simp only [reduce_option, id.def, mem_filter_map, exists_eq_right]

theorem reduce_option_nth_iff {l : List (Option α)} {x : α} :
  (∃ i, l.nth i = some (some x)) ↔ ∃ i, l.reduce_option.nth i = some x :=
  by 
    rw [←mem_iff_nth, ←mem_iff_nth, reduce_option_mem_iff]

/-! ### filter -/


section Filter

variable{p : α → Prop}[DecidablePred p]

theorem filter_eq_foldr (p : α → Prop) [DecidablePred p] (l : List α) :
  filter p l = foldr (fun a out => if p a then a :: out else out) [] l :=
  by 
    induction l <;> simp [filter]

theorem filter_congr {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
  ∀ {l : List α}, (∀ x (_ : x ∈ l), p x ↔ q x) → filter p l = filter q l
| [], _ => rfl
| a :: l, h =>
  by 
    rw [forall_mem_cons] at h <;>
      byCases' pa : p a <;> [simp only [filter_cons_of_pos _ pa, filter_cons_of_pos _ (h.1.1 pa), filter_congr h.2],
          simp only [filter_cons_of_neg _ pa, filter_cons_of_neg _ (mt h.1.2 pa), filter_congr h.2]] <;>
        split  <;> rfl

@[simp]
theorem filter_subset (l : List α) : filter p l ⊆ l :=
  (filter_sublist l).Subset

theorem of_mem_filter {a : α} : ∀ {l}, a ∈ filter p l → p a
| b :: l, ain =>
  if pb : p b then
    have  : a ∈ b :: filter p l :=
      by 
        simpa only [filter_cons_of_pos _ pb] using ain 
    Or.elim (eq_or_mem_of_mem_cons this)
      (fun this : a = b =>
        by 
          rw [←this] at pb 
          exact pb)
      fun this : a ∈ filter p l => of_mem_filter this
  else
    by 
      simp only [filter_cons_of_neg _ pb] at ain 
      exact of_mem_filter ain

theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  filter_subset l h

theorem mem_filter_of_mem {a : α} : ∀ {l}, a ∈ l → p a → a ∈ filter p l
| _ :: l, Or.inl rfl, pa =>
  by 
    rw [filter_cons_of_pos _ pa] <;> apply mem_cons_self
| b :: l, Or.inr ain, pa =>
  if pb : p b then
    by 
      rw [filter_cons_of_pos _ pb] <;> apply mem_cons_of_mem <;> apply mem_filter_of_mem ain pa
  else
    by 
      rw [filter_cons_of_neg _ pb] <;> apply mem_filter_of_mem ain pa

@[simp]
theorem mem_filter {a : α} {l} : a ∈ filter p l ↔ a ∈ l ∧ p a :=
  ⟨fun h => ⟨mem_of_mem_filter h, of_mem_filter h⟩, fun ⟨h₁, h₂⟩ => mem_filter_of_mem h₁ h₂⟩

theorem monotone_filter_left (p : α → Prop) [DecidablePred p] ⦃l l' : List α⦄ (h : l ⊆ l') : filter p l ⊆ filter p l' :=
  by 
    intro x hx 
    rw [mem_filter] at hx⊢
    exact ⟨h hx.left, hx.right⟩

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem filter_eq_self {l} : «expr ↔ »(«expr = »(filter p l, l), ∀ a «expr ∈ » l, p a) :=
begin
  induction [expr l] [] ["with", ident a, ident l, ident ih] [],
  { exact [expr iff_of_true rfl (forall_mem_nil _)] },
  rw [expr forall_mem_cons] [],
  by_cases [expr p a],
  { rw ["[", expr filter_cons_of_pos _ h, ",", expr cons_inj, ",", expr ih, ",", expr and_iff_right h, "]"] [] },
  { rw ["[", expr filter_cons_of_neg _ h, "]"] [],
    refine [expr iff_of_false _ (mt and.left h)],
    intro [ident e],
    have [] [] [":=", expr filter_sublist l],
    rw [expr e] ["at", ident this],
    exact [expr not_lt_of_ge (length_le_of_sublist this) (lt_succ_self _)] }
end

theorem filter_eq_nil {l} : filter p l = [] ↔ ∀ a (_ : a ∈ l), ¬p a :=
  by 
    simp only [eq_nil_iff_forall_not_mem, mem_filter, not_and]

variable(p)

theorem sublist.filter {l₁ l₂} (s : l₁ <+ l₂) : filter p l₁ <+ filter p l₂ :=
  filter_map_eq_filter p ▸ s.filter_map _

theorem monotone_filter_right (l : List α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q] (h : p ≤ q) :
  l.filter p <+ l.filter q :=
  by 
    induction' l with hd tl IH
    ·
      rfl
    ·
      byCases' hp : p hd
      ·
        rw [filter_cons_of_pos _ hp, filter_cons_of_pos _ (h _ hp)]
        exact IH.cons_cons hd
      ·
        rw [filter_cons_of_neg _ hp]
        byCases' hq : q hd
        ·
          rw [filter_cons_of_pos _ hq]
          exact sublist_cons_of_sublist hd IH
        ·
          rw [filter_cons_of_neg _ hq]
          exact IH

theorem map_filter (f : β → α) (l : List β) : filter p (map f l) = map f (filter (p ∘ f) l) :=
  by 
    rw [←filter_map_eq_map, filter_filter_map, filter_map_filter] <;> rfl

@[simp]
theorem filter_filter q [DecidablePred q] : ∀ l, filter p (filter q l) = filter (fun a => p a ∧ q a) l
| [] => rfl
| a :: l =>
  by 
    byCases' hp : p a <;>
      byCases' hq : q a <;>
        simp only [hp, hq, filter, if_true, if_false, true_andₓ, false_andₓ, filter_filter l, eq_self_iff_true]

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem filter_true {h : decidable_pred (λ a : α, true)} (l : list α) : «expr = »(@filter α (λ _, true) h l, l) :=
by convert [] [expr filter_eq_self.2 (λ _ _, trivial)] []

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem filter_false
{h : decidable_pred (λ a : α, false)}
(l : list α) : «expr = »(@filter α (λ _, false) h l, «expr[ , ]»([])) :=
by convert [] [expr filter_eq_nil.2 (λ _ _, id)] []

@[simp]
theorem span_eq_take_drop : ∀ (l : List α), span p l = (take_while p l, drop_while p l)
| [] => rfl
| a :: l =>
  if pa : p a then
    by 
      simp only [span, if_pos pa, span_eq_take_drop l, take_while, drop_while]
  else
    by 
      simp only [span, take_while, drop_while, if_neg pa]

@[simp]
theorem take_while_append_drop : ∀ (l : List α), take_while p l ++ drop_while p l = l
| [] => rfl
| a :: l =>
  if pa : p a then
    by 
      rw [take_while, drop_while, if_pos pa, if_pos pa, cons_append, take_while_append_drop l]
  else
    by 
      rw [take_while, drop_while, if_neg pa, if_neg pa, nil_append]

end Filter

/-! ### prefix, suffix, infix -/


@[simp]
theorem prefix_append (l₁ l₂ : List α) : l₁ <+: l₁ ++ l₂ :=
  ⟨l₂, rfl⟩

@[simp]
theorem suffix_append (l₁ l₂ : List α) : l₂ <:+ l₁ ++ l₂ :=
  ⟨l₁, rfl⟩

theorem infix_append (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ l₂ ++ l₃ :=
  ⟨l₁, l₃, rfl⟩

@[simp]
theorem infix_append' (l₁ l₂ l₃ : List α) : l₂ <:+: l₁ ++ (l₂ ++ l₃) :=
  by 
    rw [←List.append_assoc] <;> apply infix_append

theorem nil_prefix (l : List α) : [] <+: l :=
  ⟨l, rfl⟩

theorem nil_suffix (l : List α) : [] <:+ l :=
  ⟨l, append_nil _⟩

@[refl]
theorem prefix_refl (l : List α) : l <+: l :=
  ⟨[], append_nil _⟩

@[refl]
theorem suffix_refl (l : List α) : l <:+ l :=
  ⟨[], rfl⟩

@[simp]
theorem suffix_cons (a : α) : ∀ l, l <:+ a :: l :=
  suffix_append [a]

theorem prefix_concat (a : α) l : l <+: concat l a :=
  by 
    simp 

theorem is_prefix.is_infix {l₁ l₂ : List α} : l₁ <+: l₂ → l₁ <:+: l₂ :=
  fun ⟨t, h⟩ => ⟨[], t, h⟩

theorem is_suffix.is_infix {l₁ l₂ : List α} : l₁ <:+ l₂ → l₁ <:+: l₂ :=
  fun ⟨t, h⟩ =>
    ⟨t, [],
      by 
        simp only [h, append_nil]⟩

@[refl]
theorem infix_refl (l : List α) : l <:+: l :=
  (prefix_refl l).IsInfix

theorem nil_infix (l : List α) : [] <:+: l :=
  (nil_prefix l).IsInfix

theorem infix_cons {L₁ L₂ : List α} {x : α} : L₁ <:+: L₂ → L₁ <:+: x :: L₂ :=
  fun ⟨LP, LS, H⟩ => ⟨x :: LP, LS, H ▸ rfl⟩

@[trans]
theorem is_prefix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₂ → l₂ <+: l₃ → l₁ <+: l₃
| l, _, _, ⟨r₁, rfl⟩, ⟨r₂, rfl⟩ => ⟨r₁ ++ r₂, (append_assoc _ _ _).symm⟩

@[trans]
theorem is_suffix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+ l₂ → l₂ <:+ l₃ → l₁ <:+ l₃
| l, _, _, ⟨l₁, rfl⟩, ⟨l₂, rfl⟩ => ⟨l₂ ++ l₁, append_assoc _ _ _⟩

@[trans]
theorem is_infix.trans : ∀ {l₁ l₂ l₃ : List α}, l₁ <:+: l₂ → l₂ <:+: l₃ → l₁ <:+: l₃
| l, _, _, ⟨l₁, r₁, rfl⟩, ⟨l₂, r₂, rfl⟩ =>
  ⟨l₂ ++ l₁, r₁ ++ r₂,
    by 
      simp only [append_assoc]⟩

protected theorem is_infix.sublist {l₁ l₂ : List α} : l₁ <:+: l₂ → l₁ <+ l₂ :=
  fun ⟨s, t, h⟩ =>
    by 
      rw [←h] <;> exact (sublist_append_right _ _).trans (sublist_append_left _ _)

protected theorem is_prefix.sublist {l₁ l₂ : List α} (h : l₁ <+: l₂) : l₁ <+ l₂ :=
  h.is_infix.sublist

protected theorem is_suffix.sublist {l₁ l₂ : List α} (h : l₁ <:+ l₂) : l₁ <+ l₂ :=
  h.is_infix.sublist

@[simp]
theorem reverse_suffix {l₁ l₂ : List α} : reverse l₁ <:+ reverse l₂ ↔ l₁ <+: l₂ :=
  ⟨fun ⟨r, e⟩ =>
      ⟨reverse r,
        by 
          rw [←reverse_reverse l₁, ←reverse_append, e, reverse_reverse]⟩,
    fun ⟨r, e⟩ =>
      ⟨reverse r,
        by 
          rw [←reverse_append, e]⟩⟩

@[simp]
theorem reverse_prefix {l₁ l₂ : List α} : reverse l₁ <+: reverse l₂ ↔ l₁ <:+ l₂ :=
  by 
    rw [←reverse_suffix] <;> simp only [reverse_reverse]

theorem infix.length_le {l₁ l₂ : List α} (s : l₁ <:+: l₂) : length l₁ ≤ length l₂ :=
  length_le_of_sublist s.sublist

theorem eq_nil_of_infix_nil {l : List α} (s : l <:+: []) : l = [] :=
  eq_nil_of_sublist_nil s.sublist

@[simp]
theorem eq_nil_iff_infix_nil {l : List α} : l <:+: [] ↔ l = [] :=
  ⟨eq_nil_of_infix_nil, fun h => h ▸ infix_refl _⟩

theorem eq_nil_of_prefix_nil {l : List α} (s : l <+: []) : l = [] :=
  eq_nil_of_infix_nil s.is_infix

@[simp]
theorem eq_nil_iff_prefix_nil {l : List α} : l <+: [] ↔ l = [] :=
  ⟨eq_nil_of_prefix_nil, fun h => h ▸ prefix_refl _⟩

theorem eq_nil_of_suffix_nil {l : List α} (s : l <:+ []) : l = [] :=
  eq_nil_of_infix_nil s.is_infix

@[simp]
theorem eq_nil_iff_suffix_nil {l : List α} : l <:+ [] ↔ l = [] :=
  ⟨eq_nil_of_suffix_nil, fun h => h ▸ suffix_refl _⟩

theorem infix_iff_prefix_suffix (l₁ l₂ : List α) : l₁ <:+: l₂ ↔ ∃ t, l₁ <+: t ∧ t <:+ l₂ :=
  ⟨fun ⟨s, t, e⟩ =>
      ⟨l₁ ++ t, ⟨_, rfl⟩,
        by 
          rw [←e, append_assoc] <;> exact ⟨_, rfl⟩⟩,
    fun ⟨_, ⟨t, rfl⟩, ⟨s, e⟩⟩ =>
      ⟨s, t,
        by 
          rw [append_assoc] <;> exact e⟩⟩

theorem eq_of_infix_of_length_eq {l₁ l₂ : List α} (s : l₁ <:+: l₂) : length l₁ = length l₂ → l₁ = l₂ :=
  eq_of_sublist_of_length_eq s.sublist

theorem eq_of_prefix_of_length_eq {l₁ l₂ : List α} (s : l₁ <+: l₂) : length l₁ = length l₂ → l₁ = l₂ :=
  eq_of_sublist_of_length_eq s.sublist

theorem eq_of_suffix_of_length_eq {l₁ l₂ : List α} (s : l₁ <:+ l₂) : length l₁ = length l₂ → l₁ = l₂ :=
  eq_of_sublist_of_length_eq s.sublist

theorem prefix_of_prefix_length_le : ∀ {l₁ l₂ l₃ : List α}, l₁ <+: l₃ → l₂ <+: l₃ → length l₁ ≤ length l₂ → l₁ <+: l₂
| [], l₂, l₃, h₁, h₂, _ => nil_prefix _
| a :: l₁, b :: l₂, _, ⟨r₁, rfl⟩, ⟨r₂, e⟩, ll =>
  by 
    injection e with _ e' 
    subst b 
    rcases prefix_of_prefix_length_le ⟨_, rfl⟩ ⟨_, e'⟩ (le_of_succ_le_succ ll) with ⟨r₃, rfl⟩
    exact ⟨r₃, rfl⟩

theorem prefix_or_prefix_of_prefix {l₁ l₂ l₃ : List α} (h₁ : l₁ <+: l₃) (h₂ : l₂ <+: l₃) : l₁ <+: l₂ ∨ l₂ <+: l₁ :=
  (le_totalₓ (length l₁) (length l₂)).imp (prefix_of_prefix_length_le h₁ h₂) (prefix_of_prefix_length_le h₂ h₁)

theorem suffix_of_suffix_length_le {l₁ l₂ l₃ : List α} (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) (ll : length l₁ ≤ length l₂) :
  l₁ <:+ l₂ :=
  reverse_prefix.1$
    prefix_of_prefix_length_le (reverse_prefix.2 h₁) (reverse_prefix.2 h₂)
      (by 
        simp [ll])

theorem suffix_or_suffix_of_suffix {l₁ l₂ l₃ : List α} (h₁ : l₁ <:+ l₃) (h₂ : l₂ <:+ l₃) : l₁ <:+ l₂ ∨ l₂ <:+ l₁ :=
  (prefix_or_prefix_of_prefix (reverse_prefix.2 h₁) (reverse_prefix.2 h₂)).imp reverse_prefix.1 reverse_prefix.1

theorem suffix_cons_iff {x : α} {l₁ l₂ : List α} : l₁ <:+ x :: l₂ ↔ l₁ = x :: l₂ ∨ l₁ <:+ l₂ :=
  by 
    split 
    ·
      rintro ⟨⟨hd, tl⟩, hl₃⟩
      ·
        exact Or.inl hl₃
      ·
        simp only [cons_append] at hl₃ 
        exact Or.inr ⟨_, hl₃.2⟩
    ·
      rintro (rfl | hl₁)
      ·
        exact (x :: l₂).suffix_refl
      ·
        exact hl₁.trans (l₂.suffix_cons _)

theorem infix_of_mem_join : ∀ {L : List (List α)} {l}, l ∈ L → l <:+: join L
| _ :: L, l, Or.inl rfl => infix_append [] _ _
| l' :: L, l, Or.inr h => is_infix.trans (infix_of_mem_join h)$ (suffix_append _ _).IsInfix

theorem prefix_append_right_inj {l₁ l₂ : List α} l : l ++ l₁ <+: l ++ l₂ ↔ l₁ <+: l₂ :=
  exists_congr$
    fun r =>
      by 
        rw [append_assoc, append_right_inj]

theorem prefix_cons_inj {l₁ l₂ : List α} a : a :: l₁ <+: a :: l₂ ↔ l₁ <+: l₂ :=
  prefix_append_right_inj [a]

theorem take_prefix n (l : List α) : take n l <+: l :=
  ⟨_, take_append_drop _ _⟩

theorem take_sublist n (l : List α) : take n l <+ l :=
  (take_prefix n l).Sublist

theorem take_subset n (l : List α) : take n l ⊆ l :=
  (take_sublist n l).Subset

theorem mem_of_mem_take {n} {l : List α} {x : α} (h : x ∈ l.take n) : x ∈ l :=
  take_subset n l h

theorem drop_suffix n (l : List α) : drop n l <:+ l :=
  ⟨_, take_append_drop _ _⟩

theorem drop_sublist n (l : List α) : drop n l <+ l :=
  (drop_suffix n l).Sublist

theorem drop_subset n (l : List α) : drop n l ⊆ l :=
  (drop_sublist n l).Subset

theorem mem_of_mem_drop {n} {l : List α} {x : α} (h : x ∈ l.drop n) : x ∈ l :=
  drop_subset n l h

theorem init_prefix : ∀ (l : List α), l.init <+: l
| [] =>
  ⟨nil,
    by 
      rw [init, List.append_nil]⟩
| a :: l => ⟨_, init_append_last (cons_ne_nil a l)⟩

theorem init_sublist (l : List α) : l.init <+ l :=
  (init_prefix l).Sublist

theorem init_subset (l : List α) : l.init ⊆ l :=
  (init_sublist l).Subset

theorem mem_of_mem_init {l : List α} {a : α} (h : a ∈ l.init) : a ∈ l :=
  init_subset l h

theorem tail_suffix (l : List α) : tail l <:+ l :=
  by 
    rw [←drop_one] <;> apply drop_suffix

theorem tail_sublist (l : List α) : l.tail <+ l :=
  (tail_suffix l).Sublist

theorem tail_subset (l : List α) : tail l ⊆ l :=
  (tail_sublist l).Subset

theorem mem_of_mem_tail {l : List α} {a : α} (h : a ∈ l.tail) : a ∈ l :=
  tail_subset l h

theorem prefix_iff_eq_append {l₁ l₂ : List α} : l₁ <+: l₂ ↔ l₁ ++ drop (length l₁) l₂ = l₂ :=
  ⟨by 
      rintro ⟨r, rfl⟩ <;> rw [drop_left],
    fun e => ⟨_, e⟩⟩

theorem suffix_iff_eq_append {l₁ l₂ : List α} : l₁ <:+ l₂ ↔ take (length l₂ - length l₁) l₂ ++ l₁ = l₂ :=
  ⟨by 
      rintro ⟨r, rfl⟩ <;> simp only [length_append, add_tsub_cancel_right, take_left],
    fun e => ⟨_, e⟩⟩

theorem prefix_iff_eq_take {l₁ l₂ : List α} : l₁ <+: l₂ ↔ l₁ = take (length l₁) l₂ :=
  ⟨fun h => append_right_cancel$ (prefix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ take_prefix _ _⟩

theorem suffix_iff_eq_drop {l₁ l₂ : List α} : l₁ <:+ l₂ ↔ l₁ = drop (length l₂ - length l₁) l₂ :=
  ⟨fun h => append_left_cancel$ (suffix_iff_eq_append.1 h).trans (take_append_drop _ _).symm,
    fun e => e.symm ▸ drop_suffix _ _⟩

instance decidable_prefix [DecidableEq α] : ∀ (l₁ l₂ : List α), Decidable (l₁ <+: l₂)
| [], l₂ => is_true ⟨l₂, rfl⟩
| a :: l₁, [] => is_false$ fun ⟨t, te⟩ => List.noConfusion te
| a :: l₁, b :: l₂ =>
  if h : a = b then
    @decidableOfIff _ _
      (by 
        rw [←h, prefix_cons_inj])
      (decidable_prefix l₁ l₂)
  else
    is_false$
      fun ⟨t, te⟩ =>
        h$
          by 
            injection te

instance decidable_suffix [DecidableEq α] : ∀ (l₁ l₂ : List α), Decidable (l₁ <:+ l₂)
| [], l₂ => is_true ⟨l₂, append_nil _⟩
| a :: l₁, [] =>
  is_false$
    mt (length_le_of_sublist ∘ is_suffix.sublist)
      (by 
        decide)
| l₁, l₂ =>
  let len1 := length l₁ 
  let len2 := length l₂ 
  if hl : len1 ≤ len2 then decidableOfIff' (l₁ = drop (len2 - len1) l₂) suffix_iff_eq_drop else
    is_false$ fun h => hl$ length_le_of_sublist$ h.sublist

theorem prefix_take_le_iff {L : List (List (Option α))} {m n : ℕ} (hm : m < L.length) : take m L <+: take n L ↔ m ≤ n :=
  by 
    simp only [prefix_iff_eq_take, length_take]
    induction' m with m IH generalizing L n
    ·
      simp only [min_eq_leftₓ, eq_self_iff_true, Nat.zero_leₓ, take]
    ·
      cases n
      ·
        simp only [Nat.nat_zero_eq_zero, nonpos_iff_eq_zero, take, take_nil]
        split 
        ·
          cases L
          ·
            exact absurd hm (not_lt_of_le m.succ.zero_le)
          ·
            simp only [forall_prop_of_false, not_false_iff, take]
        ·
          intro h 
          contradiction
      ·
        cases' L with l ls
        ·
          exact absurd hm (not_lt_of_le m.succ.zero_le)
        ·
          simp only [length] at hm 
          specialize IH ls n (Nat.lt_of_succ_lt_succₓ hm)
          simp only [le_of_ltₓ (Nat.lt_of_succ_lt_succₓ hm), min_eq_leftₓ] at IH 
          simp only [le_of_ltₓ hm, IH, true_andₓ, min_eq_leftₓ, eq_self_iff_true, length, take]
          exact ⟨Nat.succ_le_succₓ, Nat.le_of_succ_le_succₓ⟩

theorem cons_prefix_iff {l l' : List α} {x y : α} : x :: l <+: y :: l' ↔ x = y ∧ l <+: l' :=
  by 
    split 
    ·
      rintro ⟨L, hL⟩
      simp only [cons_append] at hL 
      exact ⟨hL.left, ⟨L, hL.right⟩⟩
    ·
      rintro ⟨rfl, h⟩
      rwa [prefix_cons_inj]

theorem map_prefix {l l' : List α} (f : α → β) (h : l <+: l') : l.map f <+: l'.map f :=
  by 
    induction' l with hd tl hl generalizing l'
    ·
      simp only [nil_prefix, map_nil]
    ·
      cases' l' with hd' tl'
      ·
        simpa only using eq_nil_of_prefix_nil h
      ·
        rw [cons_prefix_iff] at h 
        simp only [h, prefix_cons_inj, hl, map]

theorem is_prefix.filter_map {l l' : List α} (h : l <+: l') (f : α → Option β) : l.filter_map f <+: l'.filter_map f :=
  by 
    induction' l with hd tl hl generalizing l'
    ·
      simp only [nil_prefix, filter_map_nil]
    ·
      cases' l' with hd' tl'
      ·
        simpa only using eq_nil_of_prefix_nil h
      ·
        rw [cons_prefix_iff] at h 
        rw [←@singleton_append _ hd _, ←@singleton_append _ hd' _, filter_map_append, filter_map_append, h.left,
          prefix_append_right_inj]
        exact hl h.right

theorem is_prefix.reduce_option {l l' : List (Option α)} (h : l <+: l') : l.reduce_option <+: l'.reduce_option :=
  h.filter_map id

theorem is_prefix.filter (p : α → Prop) [DecidablePred p] ⦃l l' : List α⦄ (h : l <+: l') : filter p l <+: filter p l' :=
  by 
    obtain ⟨xs, rfl⟩ := h 
    rw [filter_append]
    exact prefix_append _ _

theorem is_suffix.filter (p : α → Prop) [DecidablePred p] ⦃l l' : List α⦄ (h : l <:+ l') : filter p l <:+ filter p l' :=
  by 
    obtain ⟨xs, rfl⟩ := h 
    rw [filter_append]
    exact suffix_append _ _

theorem is_infix.filter (p : α → Prop) [DecidablePred p] ⦃l l' : List α⦄ (h : l <:+: l') :
  filter p l <:+: filter p l' :=
  by 
    obtain ⟨xs, ys, rfl⟩ := h 
    rw [filter_append, filter_append]
    exact infix_append _ _ _

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp] theorem mem_inits : ∀ s t : list α, «expr ↔ »(«expr ∈ »(s, inits t), «expr <+: »(s, t))
| s, «expr[ , ]»([]) := suffices «expr ↔ »(«expr = »(s, nil), «expr <+: »(s, nil)), by simpa [] [] ["only"] ["[", expr inits, ",", expr mem_singleton, "]"] [] [],
⟨λ h, «expr ▸ »(h.symm, prefix_refl «expr[ , ]»([])), eq_nil_of_prefix_nil⟩
| s, «expr :: »(a, t) := suffices «expr ↔ »(«expr ∨ »(«expr = »(s, nil), «expr∃ , »((l «expr ∈ » inits t), «expr = »(«expr :: »(a, l), s))), «expr <+: »(s, «expr :: »(a, t))), by simpa [] [] [] [] [] [],
⟨λ o, match s, o with
 | ._, or.inl rfl := ⟨_, rfl⟩
 | s, or.inr ⟨r, hr, hs⟩ := let ⟨s, ht⟩ := (mem_inits _ _).1 hr in
 by rw ["[", "<-", expr hs, ",", "<-", expr ht, "]"] []; exact [expr ⟨s, rfl⟩]
 end, λ mi, match s, mi with
 | «expr[ , ]»([]), ⟨._, rfl⟩ := or.inl rfl
 | «expr :: »(b, s), ⟨r, hr⟩ := «expr $ »(list.no_confusion hr, λ
  (ba)
  (st : «expr = »(«expr ++ »(s, r), t)), «expr $ »(or.inr, by rw [expr ba] []; exact [expr ⟨_, (mem_inits _ _).2 ⟨_, st⟩, rfl⟩]))
 end⟩

@[simp]
theorem mem_tails : ∀ (s t : List α), s ∈ tails t ↔ s <:+ t
| s, [] =>
  by 
    simp only [tails, mem_singleton] <;>
      exact
        ⟨fun h =>
            by 
              rw [h] <;> exact suffix_refl [],
          eq_nil_of_suffix_nil⟩
| s, a :: t =>
  by 
    simp only [tails, mem_cons_iff, mem_tails s t] <;>
      exact
        show s = a :: t ∨ s <:+ t ↔ s <:+ a :: t from
          ⟨fun o =>
              match s, t, o with 
              | _, t, Or.inl rfl => suffix_refl _
              | s, _, Or.inr ⟨l, rfl⟩ => ⟨a :: l, rfl⟩,
            fun e =>
              match s, t, e with 
              | _, t, ⟨[], rfl⟩ => Or.inl rfl
              | s, t, ⟨b :: l, he⟩ => List.noConfusion he fun ab lt => Or.inr ⟨l, lt⟩⟩

theorem inits_cons (a : α) (l : List α) : inits (a :: l) = [] :: l.inits.map fun t => a :: t :=
  by 
    simp 

theorem tails_cons (a : α) (l : List α) : tails (a :: l) = (a :: l) :: l.tails :=
  by 
    simp 

@[simp]
theorem inits_append : ∀ (s t : List α), inits (s ++ t) = s.inits ++ t.inits.tail.map fun l => s ++ l
| [], [] =>
  by 
    simp 
| [], a :: t =>
  by 
    simp 
| a :: s, t =>
  by 
    simp [inits_append s t]

@[simp]
theorem tails_append : ∀ (s t : List α), tails (s ++ t) = (s.tails.map fun l => l ++ t) ++ t.tails.tail
| [], [] =>
  by 
    simp 
| [], a :: t =>
  by 
    simp 
| a :: s, t =>
  by 
    simp [tails_append s t]

theorem inits_eq_tails : ∀ (l : List α), l.inits = (reverse$ map reverse$ tails$ reverse l)
| [] =>
  by 
    simp 
| a :: l =>
  by 
    simp [inits_eq_tails l, map_eq_map_iff]

theorem tails_eq_inits : ∀ (l : List α), l.tails = (reverse$ map reverse$ inits$ reverse l)
| [] =>
  by 
    simp 
| a :: l =>
  by 
    simp [tails_eq_inits l, append_left_inj]

theorem inits_reverse (l : List α) : inits (reverse l) = reverse (map reverse l.tails) :=
  by 
    rw [tails_eq_inits l]
    simp [reverse_involutive.comp_self]

theorem tails_reverse (l : List α) : tails (reverse l) = reverse (map reverse l.inits) :=
  by 
    rw [inits_eq_tails l]
    simp [reverse_involutive.comp_self]

theorem map_reverse_inits (l : List α) : map reverse l.inits = (reverse$ tails$ reverse l) :=
  by 
    rw [inits_eq_tails l]
    simp [reverse_involutive.comp_self]

theorem map_reverse_tails (l : List α) : map reverse l.tails = (reverse$ inits$ reverse l) :=
  by 
    rw [tails_eq_inits l]
    simp [reverse_involutive.comp_self]

@[simp]
theorem length_tails (l : List α) : length (tails l) = length l+1 :=
  by 
    induction' l with x l IH
    ·
      simp 
    ·
      simpa using IH

@[simp]
theorem length_inits (l : List α) : length (inits l) = length l+1 :=
  by 
    simp [inits_eq_tails]

@[simp]
theorem nth_le_tails (l : List α) (n : ℕ) (hn : n < length (tails l)) : nth_le (tails l) n hn = l.drop n :=
  by 
    induction' l with x l IH generalizing n
    ·
      simp 
    ·
      cases n
      ·
        simp 
      ·
        simpa using IH n _

@[simp]
theorem nth_le_inits (l : List α) (n : ℕ) (hn : n < length (inits l)) : nth_le (inits l) n hn = l.take n :=
  by 
    induction' l with x l IH generalizing n
    ·
      simp 
    ·
      cases n
      ·
        simp 
      ·
        simpa using IH n _

instance decidable_infix [DecidableEq α] : ∀ (l₁ l₂ : List α), Decidable (l₁ <:+: l₂)
| [], l₂ => is_true ⟨[], l₂, rfl⟩
| a :: l₁, [] =>
  is_false$
    fun ⟨s, t, te⟩ =>
      absurd te$ append_ne_nil_of_ne_nil_left _ _$ append_ne_nil_of_ne_nil_right _ _$ fun h => List.noConfusion h
| l₁, l₂ =>
  decidableOfDecidableOfIff (List.decidableBex (fun t => l₁ <+: t) (tails l₂))$
    by 
      refine' (exists_congr fun t => _).trans (infix_iff_prefix_suffix _ _).symm <;>
        exact ⟨fun ⟨h1, h2⟩ => ⟨h2, (mem_tails _ _).1 h1⟩, fun ⟨h2, h1⟩ => ⟨(mem_tails _ _).2 h1, h2⟩⟩

/-! ### insert -/


section Insert

variable[DecidableEq α]

@[simp]
theorem insert_nil (a : α) : insert a nil = [a] :=
  rfl

theorem insert.def (a : α) (l : List α) : insert a l = if a ∈ l then l else a :: l :=
  rfl

@[simp]
theorem insert_of_mem {a : α} {l : List α} (h : a ∈ l) : insert a l = l :=
  by 
    simp only [insert.def, if_pos h]

@[simp]
theorem insert_of_not_mem {a : α} {l : List α} (h : a ∉ l) : insert a l = a :: l :=
  by 
    simp only [insert.def, if_neg h] <;> split  <;> rfl

@[simp]
theorem mem_insert_iff {a b : α} {l : List α} : a ∈ insert b l ↔ a = b ∨ a ∈ l :=
  by 
    byCases' h' : b ∈ l
    ·
      simp only [insert_of_mem h']
      apply (or_iff_right_of_imp _).symm 
      exact fun e => e.symm ▸ h' 
    simp only [insert_of_not_mem h', mem_cons_iff]

@[simp]
theorem suffix_insert (a : α) (l : List α) : l <:+ insert a l :=
  by 
    byCases' a ∈ l <;> [simp only [insert_of_mem h], simp only [insert_of_not_mem h, suffix_cons]]

theorem infix_insert (a : α) (l : List α) : l <:+: insert a l :=
  (suffix_insert a l).IsInfix

theorem sublist_insert (a : α) (l : List α) : l <+ insert a l :=
  (suffix_insert a l).Sublist

theorem subset_insert (a : α) (l : List α) : l ⊆ insert a l :=
  (sublist_insert a l).Subset

@[simp]
theorem mem_insert_self (a : α) (l : List α) : a ∈ insert a l :=
  mem_insert_iff.2 (Or.inl rfl)

theorem mem_insert_of_mem {a b : α} {l : List α} (h : a ∈ l) : a ∈ insert b l :=
  mem_insert_iff.2 (Or.inr h)

theorem eq_or_mem_of_mem_insert {a b : α} {l : List α} (h : a ∈ insert b l) : a = b ∨ a ∈ l :=
  mem_insert_iff.1 h

@[simp]
theorem length_insert_of_mem {a : α} {l : List α} (h : a ∈ l) : length (insert a l) = length l :=
  by 
    rw [insert_of_mem h]

@[simp]
theorem length_insert_of_not_mem {a : α} {l : List α} (h : a ∉ l) : length (insert a l) = length l+1 :=
  by 
    rw [insert_of_not_mem h] <;> rfl

end Insert

/-! ### erasep -/


section Erasep

variable{p : α → Prop}[DecidablePred p]

@[simp]
theorem erasep_nil : [].erasep p = [] :=
  rfl

theorem erasep_cons (a : α) (l : List α) : (a :: l).erasep p = if p a then l else a :: l.erasep p :=
  rfl

@[simp]
theorem erasep_cons_of_pos {a : α} {l : List α} (h : p a) : (a :: l).erasep p = l :=
  by 
    simp [erasep_cons, h]

@[simp]
theorem erasep_cons_of_neg {a : α} {l : List α} (h : ¬p a) : (a :: l).erasep p = a :: l.erasep p :=
  by 
    simp [erasep_cons, h]

theorem erasep_of_forall_not {l : List α} (h : ∀ a (_ : a ∈ l), ¬p a) : l.erasep p = l :=
  by 
    induction' l with _ _ ih <;> [rfl, simp [h _ (Or.inl rfl), ih (forall_mem_of_forall_mem_cons h)]]

theorem exists_of_erasep {l : List α} {a} (al : a ∈ l) (pa : p a) :
  ∃ a l₁ l₂, (∀ b (_ : b ∈ l₁), ¬p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ :=
  by 
    induction' l with b l IH
    ·
      cases al 
    byCases' pb : p b
    ·
      exact
        ⟨b, [], l, forall_mem_nil _, pb,
          by 
            simp [pb]⟩
    ·
      rcases al with (rfl | al)
      ·
        exact pb.elim pa 
      rcases IH al with ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩
      exact
        ⟨c, b :: l₁, l₂, forall_mem_cons.2 ⟨pb, h₁⟩, h₂,
          by 
            rw [h₃] <;> rfl,
          by 
            simp [pb, h₄]⟩

theorem exists_or_eq_self_of_erasep (p : α → Prop) [DecidablePred p] (l : List α) :
  l.erasep p = l ∨ ∃ a l₁ l₂, (∀ b (_ : b ∈ l₁), ¬p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ :=
  by 
    byCases' h : ∃ (a : _)(_ : a ∈ l), p a
    ·
      rcases h with ⟨a, ha, pa⟩
      exact Or.inr (exists_of_erasep ha pa)
    ·
      simp  at h 
      exact Or.inl (erasep_of_forall_not h)

@[simp]
theorem length_erasep_of_mem {l : List α} {a} (al : a ∈ l) (pa : p a) : length (l.erasep p) = pred (length l) :=
  by 
    rcases exists_of_erasep al pa with ⟨_, l₁, l₂, _, _, e₁, e₂⟩ <;> rw [e₂] <;> simp [-add_commₓ, e₁] <;> rfl

theorem erasep_append_left {a : α} (pa : p a) : ∀ {l₁ : List α} l₂, a ∈ l₁ → (l₁ ++ l₂).erasep p = l₁.erasep p ++ l₂
| x :: xs, l₂, h =>
  by 
    byCases' h' : p x <;> simp [h']
    rw [erasep_append_left l₂ (mem_of_ne_of_mem (mt _ h') h)]
    rintro rfl 
    exact pa

theorem erasep_append_right : ∀ {l₁ : List α} l₂, (∀ b (_ : b ∈ l₁), ¬p b) → (l₁ ++ l₂).erasep p = l₁ ++ l₂.erasep p
| [], l₂, h => rfl
| x :: xs, l₂, h =>
  by 
    simp [(forall_mem_cons.1 h).1, erasep_append_right _ (forall_mem_cons.1 h).2]

theorem erasep_sublist (l : List α) : l.erasep p <+ l :=
  by 
    rcases exists_or_eq_self_of_erasep p l with (h | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩) <;> [rw [h],
      ·
        rw [h₄, h₃]
        simp ]

theorem erasep_subset (l : List α) : l.erasep p ⊆ l :=
  (erasep_sublist l).Subset

theorem sublist.erasep {l₁ l₂ : List α} (s : l₁ <+ l₂) : l₁.erasep p <+ l₂.erasep p :=
  by 
    induction s 
    case list.sublist.slnil => 
      rfl 
    case list.sublist.cons l₁ l₂ a s IH => 
      byCases' h : p a <;> simp [h]
      exacts[IH.trans (erasep_sublist _), IH.cons _ _ _]
    case list.sublist.cons2 l₁ l₂ a s IH => 
      byCases' h : p a <;> simp [h]
      exacts[s, IH.cons2 _ _ _]

theorem mem_of_mem_erasep {a : α} {l : List α} : a ∈ l.erasep p → a ∈ l :=
  @erasep_subset _ _ _ _ _

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem mem_erasep_of_neg
{a : α}
{l : list α}
(pa : «expr¬ »(p a)) : «expr ↔ »(«expr ∈ »(a, l.erasep p), «expr ∈ »(a, l)) :=
⟨mem_of_mem_erasep, λ al, begin
   rcases [expr exists_or_eq_self_of_erasep p l, "with", ident h, "|", "⟨", ident c, ",", ident l₁, ",", ident l₂, ",", ident h₁, ",", ident h₂, ",", ident h₃, ",", ident h₄, "⟩"],
   { rwa [expr h] [] },
   { rw [expr h₄] [],
     rw [expr h₃] ["at", ident al],
     have [] [":", expr «expr ≠ »(a, c)] [],
     { rintro [ident rfl],
       exact [expr pa.elim h₂] },
     simpa [] [] [] ["[", expr this, "]"] [] ["using", expr al] }
 end⟩

theorem erasep_map (f : β → α) : ∀ (l : List β), (map f l).erasep p = map f (l.erasep (p ∘ f))
| [] => rfl
| b :: l =>
  by 
    byCases' p (f b) <;> simp [h, erasep_map l]

@[simp]
theorem extractp_eq_find_erasep : ∀ (l : List α), extractp p l = (find p l, erasep p l)
| [] => rfl
| a :: l =>
  by 
    byCases' pa : p a <;> simp [extractp, pa, extractp_eq_find_erasep l]

end Erasep

/-! ### erase -/


section Erase

variable[DecidableEq α]

@[simp]
theorem erase_nil (a : α) : [].erase a = [] :=
  rfl

theorem erase_cons (a b : α) (l : List α) : (b :: l).erase a = if b = a then l else b :: l.erase a :=
  rfl

@[simp]
theorem erase_cons_head (a : α) (l : List α) : (a :: l).erase a = l :=
  by 
    simp only [erase_cons, if_pos rfl]

@[simp]
theorem erase_cons_tail {a b : α} (l : List α) (h : b ≠ a) : (b :: l).erase a = b :: l.erase a :=
  by 
    simp only [erase_cons, if_neg h] <;> split  <;> rfl

theorem erase_eq_erasep (a : α) (l : List α) : l.erase a = l.erasep (Eq a) :=
  by 
    induction' l with b l
    ·
      rfl 
    byCases' a = b <;> [simp [h], simp [h, Ne.symm h]]

@[simp]
theorem erase_of_not_mem {a : α} {l : List α} (h : a ∉ l) : l.erase a = l :=
  by 
    rw [erase_eq_erasep, erasep_of_forall_not] <;> rintro b h' rfl <;> exact h h'

theorem exists_erase_eq {a : α} {l : List α} (h : a ∈ l) : ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l.erase a = l₁ ++ l₂ :=
  by 
    rcases exists_of_erasep h rfl with ⟨_, l₁, l₂, h₁, rfl, h₂, h₃⟩ <;>
      rw [erase_eq_erasep] <;> exact ⟨l₁, l₂, fun h => h₁ _ h rfl, h₂, h₃⟩

@[simp]
theorem length_erase_of_mem {a : α} {l : List α} (h : a ∈ l) : length (l.erase a) = pred (length l) :=
  by 
    rw [erase_eq_erasep] <;> exact length_erasep_of_mem h rfl

theorem erase_append_left {a : α} {l₁ : List α} l₂ (h : a ∈ l₁) : (l₁ ++ l₂).erase a = l₁.erase a ++ l₂ :=
  by 
    simp [erase_eq_erasep] <;>
      exact
        erasep_append_left
          (by 
            rfl)
          l₂ h

theorem erase_append_right {a : α} {l₁ : List α} l₂ (h : a ∉ l₁) : (l₁ ++ l₂).erase a = l₁ ++ l₂.erase a :=
  by 
    rw [erase_eq_erasep, erase_eq_erasep, erasep_append_right] <;> rintro b h' rfl <;> exact h h'

theorem erase_sublist (a : α) (l : List α) : l.erase a <+ l :=
  by 
    rw [erase_eq_erasep] <;> apply erasep_sublist

theorem erase_subset (a : α) (l : List α) : l.erase a ⊆ l :=
  (erase_sublist a l).Subset

theorem sublist.erase (a : α) {l₁ l₂ : List α} (h : l₁ <+ l₂) : l₁.erase a <+ l₂.erase a :=
  by 
    simp [erase_eq_erasep] <;> exact sublist.erasep h

theorem mem_of_mem_erase {a b : α} {l : List α} : a ∈ l.erase b → a ∈ l :=
  @erase_subset _ _ _ _ _

@[simp]
theorem mem_erase_of_ne {a b : α} {l : List α} (ab : a ≠ b) : a ∈ l.erase b ↔ a ∈ l :=
  by 
    rw [erase_eq_erasep] <;> exact mem_erasep_of_neg ab.symm

theorem erase_comm (a b : α) (l : List α) : (l.erase a).erase b = (l.erase b).erase a :=
  if ab : a = b then
    by 
      rw [ab]
  else
    if ha : a ∈ l then
      if hb : b ∈ l then
        match l, l.erase a, exists_erase_eq ha, hb with 
        | _, _, ⟨l₁, l₂, ha', rfl, rfl⟩, hb =>
          if h₁ : b ∈ l₁ then
            by 
              rw [erase_append_left _ h₁, erase_append_left _ h₁, erase_append_right _ (mt mem_of_mem_erase ha'),
                erase_cons_head]
          else
            by 
              rw [erase_append_right _ h₁, erase_append_right _ h₁, erase_append_right _ ha', erase_cons_tail _ ab,
                erase_cons_head]
      else
        by 
          simp only [erase_of_not_mem hb, erase_of_not_mem (mt mem_of_mem_erase hb)]
    else
      by 
        simp only [erase_of_not_mem ha, erase_of_not_mem (mt mem_of_mem_erase ha)]

theorem map_erase [DecidableEq β] {f : α → β} (finj : injective f) {a : α} (l : List α) :
  map f (l.erase a) = (map f l).erase (f a) :=
  by 
    rw [erase_eq_erasep, erase_eq_erasep, erasep_map] <;> congr <;> ext b <;> simp [finj.eq_iff]

theorem map_foldl_erase [DecidableEq β] {f : α → β} (finj : injective f) {l₁ l₂ : List α} :
  map f (foldl List.eraseₓ l₁ l₂) = foldl (fun l a => l.erase (f a)) (map f l₁) l₂ :=
  by 
    induction l₂ generalizing l₁ <;> [rfl, simp only [foldl_cons, map_erase finj]]

end Erase

/-! ### diff -/


section Diff

variable[DecidableEq α]

@[simp]
theorem diff_nil (l : List α) : l.diff [] = l :=
  rfl

@[simp]
theorem diff_cons (l₁ l₂ : List α) (a : α) : l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ :=
  if h : a ∈ l₁ then
    by 
      simp only [List.diff, if_pos h]
  else
    by 
      simp only [List.diff, if_neg h, erase_of_not_mem h]

theorem diff_cons_right (l₁ l₂ : List α) (a : α) : l₁.diff (a :: l₂) = (l₁.diff l₂).erase a :=
  by 
    induction' l₂ with b l₂ ih generalizing l₁ a
    ·
      simpRw [diff_cons, diff_nil]
    ·
      rw [diff_cons, diff_cons, erase_comm, ←diff_cons, ih, ←diff_cons]

theorem diff_erase (l₁ l₂ : List α) (a : α) : (l₁.diff l₂).erase a = (l₁.erase a).diff l₂ :=
  by 
    rw [←diff_cons_right, diff_cons]

@[simp]
theorem nil_diff (l : List α) : [].diff l = [] :=
  by 
    induction l <;> [rfl, simp only [diff_cons, erase_of_not_mem (not_mem_nil _)]]

theorem diff_eq_foldl : ∀ (l₁ l₂ : List α), l₁.diff l₂ = foldl List.eraseₓ l₁ l₂
| l₁, [] => rfl
| l₁, a :: l₂ => (diff_cons l₁ l₂ a).trans (diff_eq_foldl _ _)

@[simp]
theorem diff_append (l₁ l₂ l₃ : List α) : l₁.diff (l₂ ++ l₃) = (l₁.diff l₂).diff l₃ :=
  by 
    simp only [diff_eq_foldl, foldl_append]

@[simp]
theorem map_diff [DecidableEq β] {f : α → β} (finj : injective f) {l₁ l₂ : List α} :
  map f (l₁.diff l₂) = (map f l₁).diff (map f l₂) :=
  by 
    simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]

theorem diff_sublist : ∀ (l₁ l₂ : List α), l₁.diff l₂ <+ l₁
| l₁, [] => sublist.refl _
| l₁, a :: l₂ =>
  calc l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ := diff_cons _ _ _ 
    _ <+ l₁.erase a := diff_sublist _ _ 
    _ <+ l₁ := List.erase_sublist _ _
    

theorem diff_subset (l₁ l₂ : List α) : l₁.diff l₂ ⊆ l₁ :=
  (diff_sublist _ _).Subset

theorem mem_diff_of_mem {a : α} : ∀ {l₁ l₂ : List α}, a ∈ l₁ → a ∉ l₂ → a ∈ l₁.diff l₂
| l₁, [], h₁, h₂ => h₁
| l₁, b :: l₂, h₁, h₂ =>
  by 
    rw [diff_cons] <;>
      exact mem_diff_of_mem ((mem_erase_of_ne (ne_of_not_mem_cons h₂)).2 h₁) (not_mem_of_not_mem_cons h₂)

theorem sublist.diff_right : ∀ {l₁ l₂ l₃ : List α}, l₁ <+ l₂ → l₁.diff l₃ <+ l₂.diff l₃
| l₁, l₂, [], h => h
| l₁, l₂, a :: l₃, h =>
  by 
    simp only [diff_cons, (h.erase _).diff_right]

theorem erase_diff_erase_sublist_of_sublist {a : α} :
  ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → (l₂.erase a).diff (l₁.erase a) <+ l₂.diff l₁
| [], l₂, h => erase_sublist _ _
| b :: l₁, l₂, h =>
  if heq : b = a then
    by 
      simp only [HEq, erase_cons_head, diff_cons]
  else
    by 
      simpa only [erase_cons_head, erase_cons_tail _ HEq, diff_cons, erase_comm a b l₂] using
        erase_diff_erase_sublist_of_sublist (h.erase b)

end Diff

/-! ### enum -/


theorem length_enum_from : ∀ n (l : List α), length (enum_from n l) = length l
| n, [] => rfl
| n, a :: l => congr_argₓ Nat.succ (length_enum_from _ _)

theorem length_enum : ∀ (l : List α), length (enum l) = length l :=
  length_enum_from _

@[simp]
theorem enum_from_nth : ∀ n (l : List α) m, nth (enum_from n l) m = (fun a => (n+m, a)) <$> nth l m
| n, [], m => rfl
| n, a :: l, 0 => rfl
| n, a :: l, m+1 =>
  (enum_from_nth (n+1) l m).trans$
    by 
      rw [add_right_commₓ] <;> rfl

@[simp]
theorem enum_nth : ∀ (l : List α) n, nth (enum l) n = (fun a => (n, a)) <$> nth l n :=
  by 
    simp only [enum, enum_from_nth, zero_addₓ] <;> intros  <;> rfl

@[simp]
theorem enum_from_map_snd : ∀ n (l : List α), map Prod.snd (enum_from n l) = l
| n, [] => rfl
| n, a :: l => congr_argₓ (cons _) (enum_from_map_snd _ _)

@[simp]
theorem enum_map_snd : ∀ (l : List α), map Prod.snd (enum l) = l :=
  enum_from_map_snd _

theorem mem_enum_from {x : α} {i : ℕ} :
  ∀ {j : ℕ} (xs : List α), (i, x) ∈ xs.enum_from j → j ≤ i ∧ (i < j+xs.length) ∧ x ∈ xs
| j, [] =>
  by 
    simp [enum_from]
| j, y :: ys =>
  suffices i = j ∧ x = y ∨ (i, x) ∈ enum_from (j+1) ys → j ≤ i ∧ (i < j+length ys+1) ∧ (x = y ∨ x ∈ ys)by 
    simpa [enum_from, mem_enum_from ys]
  by 
    rintro (h | h)
    ·
      refine' ⟨le_of_eqₓ h.1.symm, h.1 ▸ _, Or.inl h.2⟩
      apply Nat.lt_add_of_pos_rightₓ <;> simp 
    ·
      obtain ⟨hji, hijlen, hmem⟩ := mem_enum_from _ h 
      refine' ⟨_, _, _⟩
      ·
        exact le_transₓ (Nat.le_succₓ _) hji
      ·
        convert hijlen using 1
        acRfl
      ·
        simp [hmem]

section Choose

variable(p : α → Prop)[DecidablePred p](l : List α)

theorem choose_spec (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (choose_x p l hp).property

theorem choose_mem (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1

theorem choose_property (hp : ∃ a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2

end Choose

/-! ### map₂_left' -/


section Map₂Left'

@[simp]
theorem map₂_left'_nil_right (f : α → Option β → γ) as : map₂_left' f as [] = (as.map fun a => f a none, []) :=
  by 
    cases as <;> rfl

end Map₂Left'

/-! ### map₂_right' -/


section Map₂Right'

variable(f : Option α → β → γ)(a : α)(as : List α)(b : β)(bs : List β)

@[simp]
theorem map₂_right'_nil_left : map₂_right' f [] bs = (bs.map (f none), []) :=
  by 
    cases bs <;> rfl

@[simp]
theorem map₂_right'_nil_right : map₂_right' f as [] = ([], as) :=
  rfl

@[simp]
theorem map₂_right'_nil_cons : map₂_right' f [] (b :: bs) = (f none b :: bs.map (f none), []) :=
  rfl

@[simp]
theorem map₂_right'_cons_cons :
  map₂_right' f (a :: as) (b :: bs) =
    let rec := map₂_right' f as bs
    (f (some a) b :: rec.fst, rec.snd) :=
  rfl

end Map₂Right'

/-! ### zip_left' -/


section ZipLeft'

variable(a : α)(as : List α)(b : β)(bs : List β)

@[simp]
theorem zip_left'_nil_right : zip_left' as ([] : List β) = (as.map fun a => (a, none), []) :=
  by 
    cases as <;> rfl

@[simp]
theorem zip_left'_nil_left : zip_left' ([] : List α) bs = ([], bs) :=
  rfl

@[simp]
theorem zip_left'_cons_nil : zip_left' (a :: as) ([] : List β) = ((a, none) :: as.map fun a => (a, none), []) :=
  rfl

@[simp]
theorem zip_left'_cons_cons :
  zip_left' (a :: as) (b :: bs) =
    let rec := zip_left' as bs
    ((a, some b) :: rec.fst, rec.snd) :=
  rfl

end ZipLeft'

/-! ### zip_right' -/


section ZipRight'

variable(a : α)(as : List α)(b : β)(bs : List β)

@[simp]
theorem zip_right'_nil_left : zip_right' ([] : List α) bs = (bs.map fun b => (none, b), []) :=
  by 
    cases bs <;> rfl

@[simp]
theorem zip_right'_nil_right : zip_right' as ([] : List β) = ([], as) :=
  rfl

@[simp]
theorem zip_right'_nil_cons : zip_right' ([] : List α) (b :: bs) = ((none, b) :: bs.map fun b => (none, b), []) :=
  rfl

@[simp]
theorem zip_right'_cons_cons :
  zip_right' (a :: as) (b :: bs) =
    let rec := zip_right' as bs
    ((some a, b) :: rec.fst, rec.snd) :=
  rfl

end ZipRight'

/-! ### map₂_left -/


section Map₂Left

variable(f : α → Option β → γ)(as : List α)

@[simp]
theorem map₂_left_nil_right : map₂_left f as [] = as.map fun a => f a none :=
  by 
    cases as <;> rfl

theorem map₂_left_eq_map₂_left' : ∀ as bs, map₂_left f as bs = (map₂_left' f as bs).fst
| [], bs =>
  by 
    simp 
| a :: as, [] =>
  by 
    simp 
| a :: as, b :: bs =>
  by 
    simp 

theorem map₂_left_eq_map₂ : ∀ as bs, length as ≤ length bs → map₂_left f as bs = map₂ (fun a b => f a (some b)) as bs
| [], [], h =>
  by 
    simp 
| [], b :: bs, h =>
  by 
    simp 
| a :: as, [], h =>
  by 
    simp  at h 
    contradiction
| a :: as, b :: bs, h =>
  by 
    simp  at h 
    simp 

end Map₂Left

/-! ### map₂_right -/


section Map₂Right

variable(f : Option α → β → γ)(a : α)(as : List α)(b : β)(bs : List β)

@[simp]
theorem map₂_right_nil_left : map₂_right f [] bs = bs.map (f none) :=
  by 
    cases bs <;> rfl

@[simp]
theorem map₂_right_nil_right : map₂_right f as [] = [] :=
  rfl

@[simp]
theorem map₂_right_nil_cons : map₂_right f [] (b :: bs) = f none b :: bs.map (f none) :=
  rfl

@[simp]
theorem map₂_right_cons_cons : map₂_right f (a :: as) (b :: bs) = f (some a) b :: map₂_right f as bs :=
  rfl

theorem map₂_right_eq_map₂_right' : map₂_right f as bs = (map₂_right' f as bs).fst :=
  by 
    simp only [map₂_right, map₂_right', map₂_left_eq_map₂_left']

-- error in Data.List.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map₂_right_eq_map₂
(h : «expr ≤ »(length bs, length as)) : «expr = »(map₂_right f as bs, map₂ (λ a b, f (some a) b) as bs) :=
begin
  have [] [":", expr «expr = »(λ a b, flip f a (some b), flip (λ a b, f (some a) b))] [":=", expr rfl],
  simp [] [] ["only"] ["[", expr map₂_right, ",", expr map₂_left_eq_map₂, ",", expr map₂_flip, ",", "*", "]"] [] []
end

end Map₂Right

/-! ### zip_left -/


section ZipLeft

variable(a : α)(as : List α)(b : β)(bs : List β)

@[simp]
theorem zip_left_nil_right : zip_left as ([] : List β) = as.map fun a => (a, none) :=
  by 
    cases as <;> rfl

@[simp]
theorem zip_left_nil_left : zip_left ([] : List α) bs = [] :=
  rfl

@[simp]
theorem zip_left_cons_nil : zip_left (a :: as) ([] : List β) = (a, none) :: as.map fun a => (a, none) :=
  rfl

@[simp]
theorem zip_left_cons_cons : zip_left (a :: as) (b :: bs) = (a, some b) :: zip_left as bs :=
  rfl

theorem zip_left_eq_zip_left' : zip_left as bs = (zip_left' as bs).fst :=
  by 
    simp only [zip_left, zip_left', map₂_left_eq_map₂_left']

end ZipLeft

/-! ### zip_right -/


section ZipRight

variable(a : α)(as : List α)(b : β)(bs : List β)

@[simp]
theorem zip_right_nil_left : zip_right ([] : List α) bs = bs.map fun b => (none, b) :=
  by 
    cases bs <;> rfl

@[simp]
theorem zip_right_nil_right : zip_right as ([] : List β) = [] :=
  rfl

@[simp]
theorem zip_right_nil_cons : zip_right ([] : List α) (b :: bs) = (none, b) :: bs.map fun b => (none, b) :=
  rfl

@[simp]
theorem zip_right_cons_cons : zip_right (a :: as) (b :: bs) = (some a, b) :: zip_right as bs :=
  rfl

theorem zip_right_eq_zip_right' : zip_right as bs = (zip_right' as bs).fst :=
  by 
    simp only [zip_right, zip_right', map₂_right_eq_map₂_right']

end ZipRight

/-! ### to_chunks -/


section ToChunks

@[simp]
theorem to_chunks_nil n : @to_chunks α n [] = [] :=
  by 
    cases n <;> rfl

theorem to_chunks_aux_eq n : ∀ xs i, @to_chunks_aux α n xs i = (xs.take i, (xs.drop i).toChunks (n+1))
| [], i =>
  by 
    cases i <;> rfl
| x :: xs, 0 =>
  by 
    rw [to_chunks_aux, drop, to_chunks] <;> cases to_chunks_aux n xs n <;> rfl
| x :: xs, i+1 =>
  by 
    rw [to_chunks_aux, to_chunks_aux_eq] <;> rfl

theorem to_chunks_eq_cons' n :
  ∀ {xs : List α} (h : xs ≠ []), xs.to_chunks (n+1) = xs.take (n+1) :: (xs.drop (n+1)).toChunks (n+1)
| [], e => (e rfl).elim
| x :: xs, _ =>
  by 
    rw [to_chunks, to_chunks_aux_eq] <;> rfl

theorem to_chunks_eq_cons :
  ∀ {n} {xs : List α} (n0 : n ≠ 0) (x0 : xs ≠ []), xs.to_chunks n = xs.take n :: (xs.drop n).toChunks n
| 0, _, e => (e rfl).elim
| n+1, xs, _ => to_chunks_eq_cons' _

theorem to_chunks_aux_join {n} : ∀ {xs i l L}, @to_chunks_aux α n xs i = (l, L) → l ++ L.join = xs
| [], _, _, _, rfl => rfl
| x :: xs, i, l, L, e =>
  by 
    cases i <;> [cases' e' : to_chunks_aux n xs n with l L, cases' e' : to_chunks_aux n xs i with l L] <;>
      ·
        rw [to_chunks_aux, e', to_chunks_aux] at e 
        cases e 
        exact (congr_argₓ (cons x) (to_chunks_aux_join e') : _)

@[simp]
theorem to_chunks_join : ∀ n xs, (@to_chunks α n xs).join = xs
| n, [] =>
  by 
    cases n <;> rfl
| 0, x :: xs =>
  by 
    simp only [to_chunks, join] <;> rw [append_nil]
| n+1, x :: xs =>
  by 
    rw [to_chunks]
    cases' e : to_chunks_aux n xs n with l L 
    exact (congr_argₓ (cons x) (to_chunks_aux_join e) : _)

theorem to_chunks_length_le : ∀ n xs, n ≠ 0 → ∀ (l : List α), l ∈ @to_chunks α n xs → l.length ≤ n
| 0, _, e, _ => (e rfl).elim
| n+1, xs, _, l =>
  by 
    refine' (measure_wf length).induction xs _ 
    intro xs IH h 
    byCases' x0 : xs = []
    ·
      subst xs 
      cases h 
    rw [to_chunks_eq_cons' _ x0] at h 
    rcases h with (rfl | h)
    ·
      apply length_take_le
    ·
      refine' IH _ _ h 
      simp only [Measureₓ, InvImage, length_drop]
      exact tsub_lt_self (length_pos_iff_ne_nil.2 x0) (succ_pos _)

end ToChunks

/-! ### Retroattributes

The list definitions happen earlier than `to_additive`, so here we tag the few multiplicative
definitions that couldn't be tagged earlier.
-/


attribute [toAdditive] List.prod

attribute [toAdditive] alternating_prod

/-! ### Miscellaneous lemmas -/


theorem ilast'_mem : ∀ a l, @ilast' α a l ∈ a :: l
| a, [] => Or.inl rfl
| a, b :: l => Or.inr (ilast'_mem b l)

@[simp]
theorem nth_le_attach (L : List α) i (H : i < L.attach.length) :
  (L.attach.nth_le i H).1 = L.nth_le i (length_attach L ▸ H) :=
  calc
    (L.attach.nth_le i H).1 =
      (L.attach.map Subtype.val).nthLe i
        (by 
          simpa using H) :=
    by 
      rw [nth_le_map']
    _ = L.nth_le i _ :=
    by 
      congr <;> apply attach_map_val
    

@[simp]
theorem mem_map_swap (x : α) (y : β) (xs : List (α × β)) : (y, x) ∈ map Prod.swap xs ↔ (x, y) ∈ xs :=
  by 
    induction' xs with x xs
    ·
      simp only [not_mem_nil, map_nil]
    ·
      cases' x with a b 
      simp only [mem_cons_iff, Prod.mk.inj_iffₓ, map, Prod.swap_prod_mkₓ, Prod.exists, xs_ih, and_comm]

theorem slice_eq (xs : List α) (n m : ℕ) : slice n m xs = xs.take n ++ xs.drop (n+m) :=
  by 
    induction n generalizing xs
    ·
      simp [slice]
    ·
      cases xs <;> simp [slice, Nat.succ_add]

theorem sizeof_slice_lt [SizeOf α] (i j : ℕ) (hj : 0 < j) (xs : List α) (hi : i < xs.length) :
  sizeof (List.slice i j xs) < sizeof xs :=
  by 
    induction xs generalizing i j 
    case list.nil i j h => 
      cases hi 
    case list.cons x xs xs_ih i j h => 
      cases i <;> simp only [-slice_eq, List.slice]
      ·
        cases j 
        cases h 
        dsimp only [drop]
        unfoldWf 
        apply @lt_of_le_of_ltₓ _ _ _ xs.sizeof
        ·
          clear * - 
          induction xs generalizing j <;> unfoldWf 
          case list.nil j => 
            rfl 
          case list.cons xs_hd xs_tl xs_ih j => 
            cases j <;> unfoldWf 
            rfl 
            trans 
            apply xs_ih 
            simp 
        unfoldWf 
        apply zero_lt_one_add
      ·
        unfoldWf 
        apply xs_ih _ _ h 
        apply lt_of_succ_lt_succ hi

end List

