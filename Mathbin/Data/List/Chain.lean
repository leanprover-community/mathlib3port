import Mathbin.Data.List.Pairwise 
import Mathbin.Logic.Relation

/-!
# Relation chain

This file provides basic results about `list.chain` (definition in `data.list.defs`).
A list `[a₂, ..., aₙ]` is a `chain` starting at `a₁` with respect to the relation `r` if `r a₁ a₂`
and `r a₂ a₃` and ... and `r aₙ₋₁ aₙ`. We write it `chain r a₁ [a₂, ..., aₙ]`.
A graph-specialized version is in development and will hopefully be added under `combinatorics.`
sometime soon.
-/


universe u v

open Nat

namespace List

variable {α : Type u} {β : Type v} {R : α → α → Prop}

mk_iff_of_inductive_prop List.Chain List.chain_iff

theorem rel_of_chain_cons {a b : α} {l : List α} (p : chain R a (b :: l)) : R a b :=
  (chain_cons.1 p).1

theorem chain_of_chain_cons {a b : α} {l : List α} (p : chain R a (b :: l)) : chain R b l :=
  (chain_cons.1 p).2

theorem chain.imp' {S : α → α → Prop} (HRS : ∀ ⦃a b⦄, R a b → S a b) {a b : α} (Hab : ∀ ⦃c⦄, R a c → S b c) {l : List α}
  (p : chain R a l) : chain S b l :=
  by 
    induction' p with _ a c l r p IH generalizing b <;> constructor <;> [exact Hab r, exact IH (@HRS _)]

theorem chain.imp {S : α → α → Prop} (H : ∀ a b, R a b → S a b) {a : α} {l : List α} (p : chain R a l) : chain S a l :=
  p.imp' H (H a)

theorem chain.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {a : α} {l : List α} : chain R a l ↔ chain S a l :=
  ⟨chain.imp fun a b => (H a b).1, chain.imp fun a b => (H a b).2⟩

theorem chain.iff_mem {a : α} {l : List α} : chain R a l ↔ chain (fun x y => x ∈ a :: l ∧ y ∈ l ∧ R x y) a l :=
  ⟨fun p =>
      by 
        induction' p with _ a b l r p IH <;>
          constructor <;> [exact ⟨mem_cons_self _ _, mem_cons_self _ _, r⟩,
            exact IH.imp fun a b ⟨am, bm, h⟩ => ⟨mem_cons_of_mem _ am, mem_cons_of_mem _ bm, h⟩],
    chain.imp fun a b h => h.2.2⟩

theorem chain_singleton {a b : α} : chain R a [b] ↔ R a b :=
  by 
    simp only [chain_cons, chain.nil, and_trueₓ]

theorem chain_split {a b : α} {l₁ l₂ : List α} : chain R a (l₁ ++ b :: l₂) ↔ chain R a (l₁ ++ [b]) ∧ chain R b l₂ :=
  by 
    induction' l₁ with x l₁ IH generalizing a <;>
      simp only [nil_append, cons_append, chain.nil, chain_cons, and_trueₓ, and_assoc]

theorem chain_map (f : β → α) {b : β} {l : List β} :
  chain R (f b) (map f l) ↔ chain (fun a b : β => R (f a) (f b)) b l :=
  by 
    induction l generalizing b <;> simp only [map, chain.nil, chain_cons]

theorem chain_of_chain_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b) {a : α} {l : List α}
  (p : chain S (f a) (map f l)) : chain R a l :=
  ((chain_map f).1 p).imp H

theorem chain_map_of_chain {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b)) {a : α} {l : List α}
  (p : chain R a l) : chain S (f a) (map f l) :=
  (chain_map f).2$ p.imp H

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » l)
theorem chain_pmap_of_chain {S : β → β → Prop} {p : α → Prop} {f : ∀ a, p a → β}
  (H : ∀ a b ha hb, R a b → S (f a ha) (f b hb)) {a : α} {l : List α} (hl₁ : chain R a l) (ha : p a)
  (hl₂ : ∀ a _ : a ∈ l, p a) : chain S (f a ha) (List.pmap f l hl₂) :=
  by 
    induction' l with lh lt l_ih generalizing a
    ·
      simp 
    ·
      simp [H _ _ _ _ (rel_of_chain_cons hl₁), l_ih _ (chain_of_chain_cons hl₁)]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » l)
theorem chain_of_chain_pmap {S : β → β → Prop} {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (hl₁ : ∀ a _ : a ∈ l, p a)
  {a : α} (ha : p a) (hl₂ : chain S (f a ha) (List.pmap f l hl₁)) (H : ∀ a b ha hb, S (f a ha) (f b hb) → R a b) :
  chain R a l :=
  by 
    induction' l with lh lt l_ih generalizing a
    ·
      simp 
    ·
      simp [H _ _ _ _ (rel_of_chain_cons hl₂), l_ih _ _ (chain_of_chain_cons hl₂)]

theorem chain_of_pairwise {a : α} {l : List α} (p : Pairwise R (a :: l)) : chain R a l :=
  by 
    cases' pairwise_cons.1 p with r p' 
    clear p 
    induction' p' with b l r' p IH generalizing a
    ·
      exact chain.nil 
    simp only [chain_cons, forall_mem_cons] at r 
    exact chain_cons.2 ⟨r.1, IH r'⟩

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l)
theorem chain_iff_pairwise (tr : Transitive R) {a : α} {l : List α} : chain R a l ↔ Pairwise R (a :: l) :=
  ⟨fun c =>
      by 
        induction' c with b b c l r p IH
        ·
          exact pairwise_singleton _ _ 
        apply IH.cons _ 
        simp only [mem_cons_iff, forall_eq_or_imp, r, true_andₓ]
        show ∀ x _ : x ∈ l, R b x 
        exact fun x m => tr r (rel_of_pairwise_cons IH m),
    chain_of_pairwise⟩

theorem chain_iff_nth_le {R} :
  ∀ {a : α} {l : List α},
    chain R a l ↔
      (∀ h : 0 < length l, R a (nth_le l 0 h)) ∧
        ∀ i h : i < length l - 1, R (nth_le l i (lt_of_lt_pred h)) (nth_le l (i+1) (lt_pred_iff.mp h))
| a, [] =>
  by 
    simp 
| a, b :: t =>
  by 
    rw [chain_cons, chain_iff_nth_le]
    constructor
    ·
      rintro ⟨R, ⟨h0, h⟩⟩
      constructor
      ·
        intro w 
        exact R 
      intro i w 
      cases i
      ·
        apply h0 
      convert h i _ using 1
      simp only [succ_eq_add_one, add_succ_sub_one, add_zeroₓ, length, add_lt_add_iff_right] at w 
      exact lt_pred_iff.mpr w 
    rintro ⟨h0, h⟩
    constructor
    ·
      apply h0 
      simp 
    constructor
    ·
      apply h 0
    intro i w 
    convert h (i+1) _ using 1 
    exact lt_pred_iff.mp w

theorem chain'.imp {S : α → α → Prop} (H : ∀ a b, R a b → S a b) {l : List α} (p : chain' R l) : chain' S l :=
  by 
    cases l <;> [trivial, exact p.imp H]

theorem chain'.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} : chain' R l ↔ chain' S l :=
  ⟨chain'.imp fun a b => (H a b).1, chain'.imp fun a b => (H a b).2⟩

theorem chain'.iff_mem : ∀ {l : List α}, chain' R l ↔ chain' (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l
| [] => Iff.rfl
| x :: l =>
  ⟨fun h => (chain.iff_mem.1 h).imp$ fun a b ⟨h₁, h₂, h₃⟩ => ⟨h₁, Or.inr h₂, h₃⟩, chain'.imp$ fun a b h => h.2.2⟩

@[simp]
theorem chain'_nil : chain' R [] :=
  trivialₓ

@[simp]
theorem chain'_singleton (a : α) : chain' R [a] :=
  chain.nil

theorem chain'_split {a : α} : ∀ {l₁ l₂ : List α}, chain' R (l₁ ++ a :: l₂) ↔ chain' R (l₁ ++ [a]) ∧ chain' R (a :: l₂)
| [], l₂ => (and_iff_right (chain'_singleton a)).symm
| b :: l₁, l₂ => chain_split

theorem chain'_map (f : β → α) {l : List β} : chain' R (map f l) ↔ chain' (fun a b : β => R (f a) (f b)) l :=
  by 
    cases l <;> [rfl, exact chain_map _]

theorem chain'_of_chain'_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b) {l : List α}
  (p : chain' S (map f l)) : chain' R l :=
  ((chain'_map f).1 p).imp H

theorem chain'_map_of_chain' {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b)) {l : List α}
  (p : chain' R l) : chain' S (map f l) :=
  (chain'_map f).2$ p.imp H

theorem pairwise.chain' : ∀ {l : List α}, Pairwise R l → chain' R l
| [], _ => trivialₓ
| a :: l, h => chain_of_pairwise h

theorem chain'_iff_pairwise (tr : Transitive R) : ∀ {l : List α}, chain' R l ↔ Pairwise R l
| [] => (iff_true_intro pairwise.nil).symm
| a :: l => chain_iff_pairwise tr

@[simp]
theorem chain'_cons {x y l} : chain' R (x :: y :: l) ↔ R x y ∧ chain' R (y :: l) :=
  chain_cons

theorem chain'.cons {x y l} (h₁ : R x y) (h₂ : chain' R (y :: l)) : chain' R (x :: y :: l) :=
  chain'_cons.2 ⟨h₁, h₂⟩

theorem chain'.tail : ∀ {l} h : chain' R l, chain' R l.tail
| [], _ => trivialₓ
| [x], _ => trivialₓ
| x :: y :: l, h => (chain'_cons.mp h).right

theorem chain'.rel_head {x y l} (h : chain' R (x :: y :: l)) : R x y :=
  rel_of_chain_cons h

theorem chain'.rel_head' {x l} (h : chain' R (x :: l)) ⦃y⦄ (hy : y ∈ head' l) : R x y :=
  by 
    rw [←cons_head'_tail hy] at h 
    exact h.rel_head

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » l.head')
theorem chain'.cons' {x} : ∀ {l : List α}, chain' R l → (∀ y _ : y ∈ l.head', R x y) → chain' R (x :: l)
| [], _, _ => chain'_singleton x
| a :: l, hl, H => hl.cons$ H _ rfl

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » head' l)
theorem chain'_cons' {x l} : chain' R (x :: l) ↔ (∀ y _ : y ∈ head' l, R x y) ∧ chain' R l :=
  ⟨fun h => ⟨h.rel_head', h.tail⟩, fun ⟨h₁, h₂⟩ => h₂.cons' h₁⟩

theorem chain'.drop : ∀ n {l} h : chain' R l, chain' R (drop n l)
| 0, _, h => h
| _, [], _ =>
  by 
    rw [drop_nil]
    exact chain'_nil
| n+1, [a], _ =>
  by 
    unfold drop 
    rw [drop_nil]
    exact chain'_nil
| n+1, a :: b :: l, h => chain'.drop n (chain'_cons'.mp h).right

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » l₁.last')
-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (y «expr ∈ » l₂.head')
theorem chain'.append :
  ∀ {l₁ l₂ : List α} h₁ : chain' R l₁ h₂ : chain' R l₂ h : ∀ x _ : x ∈ l₁.last' y _ : y ∈ l₂.head', R x y,
    chain' R (l₁ ++ l₂)
| [], l₂, h₁, h₂, h => h₂
| [a], l₂, h₁, h₂, h => h₂.cons'$ h _ rfl
| a :: b :: l, l₂, h₁, h₂, h =>
  by 
    simp only [last'] at h 
    have  : chain' R (b :: l) := h₁.tail 
    exact (this.append h₂ h).cons h₁.rel_head

theorem chain'_pair {x y} : chain' R [x, y] ↔ R x y :=
  by 
    simp only [chain'_singleton, chain'_cons, and_trueₓ]

theorem chain'.imp_head {x y} (h : ∀ {z}, R x z → R y z) {l} (hl : chain' R (x :: l)) : chain' R (y :: l) :=
  hl.tail.cons'$ fun z hz => h$ hl.rel_head' hz

theorem chain'_reverse : ∀ {l}, chain' R (reverse l) ↔ chain' (flip R) l
| [] => Iff.rfl
| [a] =>
  by 
    simp only [chain'_singleton, reverse_singleton]
| a :: b :: l =>
  by 
    rw [chain'_cons, reverse_cons, reverse_cons, append_assoc, cons_append, nil_append, chain'_split, ←reverse_cons,
      @chain'_reverse (b :: l), and_comm, chain'_pair, flip]

theorem chain'_iff_nth_le {R} :
  ∀ {l : List α},
    chain' R l ↔ ∀ i h : i < length l - 1, R (nth_le l i (lt_of_lt_pred h)) (nth_le l (i+1) (lt_pred_iff.mp h))
| [] =>
  by 
    simp 
| [a] =>
  by 
    simp 
| a :: b :: t =>
  by 
    rw [chain'_cons, chain'_iff_nth_le]
    constructor
    ·
      rintro ⟨R, h⟩ i w 
      cases i
      ·
        exact R
      ·
        convert h i _ using 1
        simp only [succ_eq_add_one, add_succ_sub_one, add_zeroₓ, length, add_lt_add_iff_right] at w 
        simpa using w
    ·
      rintro h 
      constructor
      ·
        apply h 0
        simp 
      ·
        intro i w 
        convert h (i+1) _ using 1
        simp only [add_zeroₓ, length, add_succ_sub_one] at w 
        simpa using w

/-- If `l₁ l₂` and `l₃` are lists and `l₁ ++ l₂` and `l₂ ++ l₃` both satisfy
  `chain' R`, then so does `l₁ ++ l₂ ++ l₃` provided `l₂ ≠ []` -/
theorem chain'.append_overlap :
  ∀ {l₁ l₂ l₃ : List α} h₁ : chain' R (l₁ ++ l₂) h₂ : chain' R (l₂ ++ l₃) hn : l₂ ≠ [], chain' R (l₁ ++ l₂ ++ l₃)
| [], l₂, l₃, h₁, h₂, hn => h₂
| l₁, [], l₃, h₁, h₂, hn => (hn rfl).elim
| [a], b :: l₂, l₃, h₁, h₂, hn =>
  by 
    simp  at *
    tauto
| a :: b :: l₁, c :: l₂, l₃, h₁, h₂, hn =>
  by 
    simp only [cons_append, chain'_cons] at h₁ h₂⊢
    simp only [←cons_append] at h₁ h₂⊢
    exact ⟨h₁.1, chain'.append_overlap h₁.2 h₂ (cons_ne_nil _ _)⟩

variable {r : α → α → Prop} {a b : α}

/--
If `a` and `b` are related by the reflexive transitive closure of `r`, then there is a `r`-chain
starting from `a` and ending on `b`.
The converse of `relation_refl_trans_gen_of_exists_chain`.
-/
theorem exists_chain_of_relation_refl_trans_gen (h : Relation.ReflTransGen r a b) :
  ∃ l, chain r a l ∧ last (a :: l) (cons_ne_nil _ _) = b :=
  by 
    apply Relation.ReflTransGen.head_induction_on h
    ·
      exact ⟨[], chain.nil, rfl⟩
    ·
      intro c d e t ih 
      obtain ⟨l, hl₁, hl₂⟩ := ih 
      refine' ⟨d :: l, chain.cons e hl₁, _⟩
      rwa [last_cons_cons]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (i «expr ∈ » «expr :: »(a, l))
/--
Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true everywhere in the chain and at `a`.
That is, we can propagate the predicate up the chain.
-/
theorem chain.induction (p : α → Prop) (l : List α) (h : chain r a l) (hb : last (a :: l) (cons_ne_nil _ _) = b)
  (carries : ∀ ⦃x y : α⦄, r x y → p y → p x) (final : p b) : ∀ i _ : i ∈ a :: l, p i :=
  by 
    induction l generalizing a
    ·
      cases hb 
      simp [final]
    ·
      rw [chain_cons] at h 
      rintro _ (rfl | _)
      apply carries h.1 (l_ih h.2 hb _ (Or.inl rfl))
      apply l_ih h.2 hb _ H

/--
Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true at `a`.
That is, we can propagate the predicate all the way up the chain.
-/
@[elab_as_eliminator]
theorem chain.induction_head (p : α → Prop) (l : List α) (h : chain r a l) (hb : last (a :: l) (cons_ne_nil _ _) = b)
  (carries : ∀ ⦃x y : α⦄, r x y → p y → p x) (final : p b) : p a :=
  (chain.induction p l h hb carries final) _ (mem_cons_self _ _)

/--
If there is an `r`-chain starting from `a` and ending at `b`, then `a` and `b` are related by the
reflexive transitive closure of `r`. The converse of `exists_chain_of_relation_refl_trans_gen`.
-/
theorem relation_refl_trans_gen_of_exists_chain l (hl₁ : chain r a l) (hl₂ : last (a :: l) (cons_ne_nil _ _) = b) :
  Relation.ReflTransGen r a b :=
  chain.induction_head _ l hl₁ hl₂ (fun x y => Relation.ReflTransGen.head) Relation.ReflTransGen.refl

end List

