import Mathbin.Data.List.Lattice 
import Mathbin.Data.List.Pairwise 
import Mathbin.Data.List.Forall2

/-!
# Lists with no duplicates

`list.nodup` is defined in `data/list/defs`. In this file we prove various properties of this
predicate.
-/


universe u v

open Nat Function

variable {α : Type u} {β : Type v}

namespace List

@[simp]
theorem forall_mem_ne {a : α} {l : List α} : (∀ a' : α, a' ∈ l → ¬a = a') ↔ a ∉ l :=
  ⟨fun h m => h _ m rfl, fun h a' m e => h (e.symm ▸ m)⟩

@[simp]
theorem nodup_nil : @nodup α [] :=
  pairwise.nil

@[simp]
theorem nodup_cons {a : α} {l : List α} : nodup (a :: l) ↔ a ∉ l ∧ nodup l :=
  by 
    simp only [nodup, pairwise_cons, forall_mem_ne]

protected theorem pairwise.nodup {l : List α} {r : α → α → Prop} [IsIrrefl α r] (h : Pairwise r l) : nodup l :=
  h.imp$ fun a b => ne_of_irrefl

theorem rel_nodup {r : α → β → Prop} (hr : Relator.BiUnique r) : (forall₂ r⇒(· ↔ ·)) nodup nodup
| _, _, forall₂.nil =>
  by 
    simp only [nodup_nil]
| _, _, forall₂.cons hab h =>
  by 
    simpa only [nodup_cons] using Relator.rel_and (Relator.rel_not (rel_mem hr hab h)) (rel_nodup h)

theorem nodup_cons_of_nodup {a : α} {l : List α} (m : a ∉ l) (n : nodup l) : nodup (a :: l) :=
  nodup_cons.2 ⟨m, n⟩

theorem nodup_singleton (a : α) : nodup [a] :=
  nodup_cons_of_nodup (not_mem_nil a) nodup_nil

theorem nodup_of_nodup_cons {a : α} {l : List α} (h : nodup (a :: l)) : nodup l :=
  (nodup_cons.1 h).2

theorem not_mem_of_nodup_cons {a : α} {l : List α} (h : nodup (a :: l)) : a ∉ l :=
  (nodup_cons.1 h).1

theorem not_nodup_cons_of_mem {a : α} {l : List α} : a ∈ l → ¬nodup (a :: l) :=
  imp_not_comm.1 not_mem_of_nodup_cons

theorem nodup_of_sublist {l₁ l₂ : List α} : l₁ <+ l₂ → nodup l₂ → nodup l₁ :=
  pairwise_of_sublist

theorem not_nodup_pair (a : α) : ¬nodup [a, a] :=
  not_nodup_cons_of_mem$ mem_singleton_self _

theorem nodup_iff_sublist {l : List α} : nodup l ↔ ∀ a, ¬[a, a] <+ l :=
  ⟨fun d a h => not_nodup_pair a (nodup_of_sublist h d),
    by 
      induction' l with a l IH <;> intro h
      ·
        exact nodup_nil 
      exact
        nodup_cons_of_nodup (fun al => h a$ (singleton_sublist.2 al).cons_cons _)
          (IH$ fun a s => h a$ sublist_cons_of_sublist _ s)⟩

theorem nodup_iff_nth_le_inj {l : List α} : nodup l ↔ ∀ i j h₁ h₂, nth_le l i h₁ = nth_le l j h₂ → i = j :=
  pairwise_iff_nth_le.trans
    ⟨fun H i j h₁ h₂ h =>
        ((lt_trichotomyₓ _ _).resolve_left fun h' => H _ _ h₂ h' h).resolve_right fun h' => H _ _ h₁ h' h.symm,
      fun H i j h₁ h₂ h => ne_of_ltₓ h₂ (H _ _ _ _ h)⟩

-- error in Data.List.Nodup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nodup.nth_le_inj_iff
{α : Type*}
{l : list α}
(h : nodup l)
{i j : exprℕ()}
(hi : «expr < »(i, l.length))
(hj : «expr < »(j, l.length)) : «expr ↔ »(«expr = »(l.nth_le i hi, l.nth_le j hj), «expr = »(i, j)) :=
⟨nodup_iff_nth_le_inj.mp h _ _ _ _, by simp [] [] [] [] [] [] { contextual := tt }⟩

-- error in Data.List.Nodup: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nodup.ne_singleton_iff
{l : list α}
(h : nodup l)
(x : α) : «expr ↔ »(«expr ≠ »(l, «expr[ , ]»([x])), «expr ∨ »(«expr = »(l, «expr[ , ]»([])), «expr∃ , »((y «expr ∈ » l), «expr ≠ »(y, x)))) :=
begin
  induction [expr l] [] ["with", ident hd, ident tl, ident hl] [],
  { simp [] [] [] [] [] [] },
  { specialize [expr hl (nodup_of_nodup_cons h)],
    by_cases [expr hx, ":", expr «expr = »(tl, «expr[ , ]»([x]))],
    { simpa [] [] [] ["[", expr hx, ",", expr and.comm, ",", expr and_or_distrib_left, "]"] [] ["using", expr h] },
    { rw ["[", "<-", expr ne.def, ",", expr hl, "]"] ["at", ident hx],
      rcases [expr hx, "with", ident rfl, "|", "⟨", ident y, ",", ident hy, ",", ident hx, "⟩"],
      { simp [] [] [] [] [] [] },
      { have [] [":", expr «expr ≠ »(tl, «expr[ , ]»([]))] [":=", expr ne_nil_of_mem hy],
        suffices [] [":", expr «expr∃ , »((y : α) (H : «expr ∈ »(y, «expr :: »(hd, tl))), «expr ≠ »(y, x))],
        { simpa [] [] [] ["[", expr ne_nil_of_mem hy, "]"] [] [] },
        exact [expr ⟨y, mem_cons_of_mem _ hy, hx⟩] } } }
end

theorem nth_le_eq_of_ne_imp_not_nodup (xs : List α) (n m : ℕ) (hn : n < xs.length) (hm : m < xs.length)
  (h : xs.nth_le n hn = xs.nth_le m hm) (hne : n ≠ m) : ¬nodup xs :=
  by 
    rw [nodup_iff_nth_le_inj]
    simp only [exists_prop, exists_and_distrib_right, not_forall]
    exact ⟨n, m, ⟨hn, hm, h⟩, hne⟩

@[simp]
theorem nth_le_index_of [DecidableEq α] {l : List α} (H : nodup l) n h : index_of (nth_le l n h) l = n :=
  nodup_iff_nth_le_inj.1 H _ _ _ h$ index_of_nth_le$ index_of_lt_length.2$ nth_le_mem _ _ _

theorem nodup_iff_count_le_one [DecidableEq α] {l : List α} : nodup l ↔ ∀ a, count a l ≤ 1 :=
  nodup_iff_sublist.trans$
    forall_congrₓ$
      fun a =>
        have  : [a, a] <+ l ↔ 1 < count a l := (@le_count_iff_repeat_sublist _ _ a l 2).symm
        (not_congr this).trans not_ltₓ

theorem nodup_repeat (a : α) : ∀ {n : ℕ}, nodup (repeat a n) ↔ n ≤ 1
| 0 =>
  by 
    simp [Nat.zero_leₓ]
| 1 =>
  by 
    simp 
| n+2 =>
  iff_of_false (fun H => nodup_iff_sublist.1 H a ((repeat_sublist_repeat _).2 (Nat.le_add_leftₓ 2 n)))
    (not_le_of_lt$ Nat.le_add_leftₓ 2 n)

@[simp]
theorem count_eq_one_of_mem [DecidableEq α] {a : α} {l : List α} (d : nodup l) (h : a ∈ l) : count a l = 1 :=
  le_antisymmₓ (nodup_iff_count_le_one.1 d a) (count_pos.2 h)

theorem nodup_of_nodup_append_left {l₁ l₂ : List α} : nodup (l₁ ++ l₂) → nodup l₁ :=
  nodup_of_sublist (sublist_append_left l₁ l₂)

theorem nodup_of_nodup_append_right {l₁ l₂ : List α} : nodup (l₁ ++ l₂) → nodup l₂ :=
  nodup_of_sublist (sublist_append_right l₁ l₂)

theorem nodup_append {l₁ l₂ : List α} : nodup (l₁ ++ l₂) ↔ nodup l₁ ∧ nodup l₂ ∧ Disjoint l₁ l₂ :=
  by 
    simp only [nodup, pairwise_append, disjoint_iff_ne]

theorem disjoint_of_nodup_append {l₁ l₂ : List α} (d : nodup (l₁ ++ l₂)) : Disjoint l₁ l₂ :=
  (nodup_append.1 d).2.2

theorem nodup_append_of_nodup {l₁ l₂ : List α} (d₁ : nodup l₁) (d₂ : nodup l₂) (dj : Disjoint l₁ l₂) :
  nodup (l₁ ++ l₂) :=
  nodup_append.2 ⟨d₁, d₂, dj⟩

theorem nodup_append_comm {l₁ l₂ : List α} : nodup (l₁ ++ l₂) ↔ nodup (l₂ ++ l₁) :=
  by 
    simp only [nodup_append, And.left_comm, disjoint_comm]

theorem nodup_middle {a : α} {l₁ l₂ : List α} : nodup (l₁ ++ a :: l₂) ↔ nodup (a :: (l₁ ++ l₂)) :=
  by 
    simp only [nodup_append, not_or_distrib, And.left_comm, and_assoc, nodup_cons, mem_append, disjoint_cons_right]

theorem nodup_of_nodup_map (f : α → β) {l : List α} : nodup (map f l) → nodup l :=
  pairwise_of_pairwise_map f$ fun a b => mt$ congr_argₓ f

theorem nodup_map_on {f : α → β} {l : List α} (H : ∀ x _ : x ∈ l, ∀ y _ : y ∈ l, f x = f y → x = y) (d : nodup l) :
  nodup (map f l) :=
  pairwise_map_of_pairwise _
    (by 
      exact fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e))
    (pairwise.and_mem.1 d)

theorem inj_on_of_nodup_map {f : α → β} {l : List α} (d : nodup (map f l)) :
  ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y :=
  by 
    induction' l with hd tl ih
    ·
      simp 
    ·
      simp only [map, nodup_cons, mem_map, not_exists, not_and, ←Ne.def] at d 
      rintro _ (rfl | h₁) _ (rfl | h₂) h₃
      ·
        rfl
      ·
        apply (d.1 _ h₂ h₃.symm).elim
      ·
        apply (d.1 _ h₁ h₃).elim
      ·
        apply ih d.2 h₁ h₂ h₃

theorem nodup_map_iff_inj_on {f : α → β} {l : List α} (d : nodup l) :
  nodup (map f l) ↔ ∀ x _ : x ∈ l y _ : y ∈ l, f x = f y → x = y :=
  ⟨inj_on_of_nodup_map, fun h => nodup_map_on h d⟩

theorem nodup_map {f : α → β} {l : List α} (hf : injective f) : nodup l → nodup (map f l) :=
  nodup_map_on fun x _ y _ h => hf h

theorem nodup_map_iff {f : α → β} {l : List α} (hf : injective f) : nodup (map f l) ↔ nodup l :=
  ⟨nodup_of_nodup_map _, nodup_map hf⟩

@[simp]
theorem nodup_attach {l : List α} : nodup (attach l) ↔ nodup l :=
  ⟨fun h => attach_map_val l ▸ nodup_map (fun a b => Subtype.eq) h,
    fun h => nodup_of_nodup_map Subtype.val ((attach_map_val l).symm ▸ h)⟩

theorem nodup_pmap {p : α → Prop} {f : ∀ a, p a → β} {l : List α} {H} (hf : ∀ a ha b hb, f a ha = f b hb → a = b)
  (h : nodup l) : nodup (pmap f l H) :=
  by 
    rw [pmap_eq_map_attach] <;>
      exact
        nodup_map
          (fun ⟨a, ha⟩ ⟨b, hb⟩ h =>
            by 
              congr <;> exact hf a (H _ ha) b (H _ hb) h)
          (nodup_attach.2 h)

theorem nodup_filter (p : α → Prop) [DecidablePred p] {l} : nodup l → nodup (filter p l) :=
  pairwise_filter_of_pairwise p

@[simp]
theorem nodup_reverse {l : List α} : nodup (reverse l) ↔ nodup l :=
  pairwise_reverse.trans$
    by 
      simp only [nodup, Ne.def, eq_comm]

theorem nodup_erase_eq_filter [DecidableEq α] (a : α) {l} (d : nodup l) : l.erase a = filter (· ≠ a) l :=
  by 
    induction' d with b l m d IH
    ·
      rfl 
    byCases' b = a
    ·
      subst h 
      rw [erase_cons_head, filter_cons_of_neg]
      symm 
      rw [filter_eq_self]
      simpa only [Ne.def, eq_comm] using m 
      exact not_not_intro rfl
    ·
      rw [erase_cons_tail _ h, filter_cons_of_pos, IH]
      exact h

theorem nodup_erase_of_nodup [DecidableEq α] (a : α) {l} : nodup l → nodup (l.erase a) :=
  nodup_of_sublist (erase_sublist _ _)

theorem nodup_diff [DecidableEq α] : ∀ {l₁ l₂ : List α} h : l₁.nodup, (l₁.diff l₂).Nodup
| l₁, [], h => h
| l₁, a :: l₂, h =>
  by 
    rw [diff_cons] <;> exact nodup_diff (nodup_erase_of_nodup _ h)

theorem mem_erase_iff_of_nodup [DecidableEq α] {a b : α} {l} (d : nodup l) : a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l :=
  by 
    rw [nodup_erase_eq_filter b d] <;> simp only [mem_filter, and_comm]

theorem mem_erase_of_nodup [DecidableEq α] {a : α} {l} (h : nodup l) : a ∉ l.erase a :=
  fun H => ((mem_erase_iff_of_nodup h).1 H).1 rfl

theorem nodup_join {L : List (List α)} : nodup (join L) ↔ (∀ l _ : l ∈ L, nodup l) ∧ Pairwise Disjoint L :=
  by 
    simp only [nodup, pairwise_join, disjoint_left.symm, forall_mem_ne]

theorem nodup_bind {l₁ : List α} {f : α → List β} :
  nodup (l₁.bind f) ↔ (∀ x _ : x ∈ l₁, nodup (f x)) ∧ Pairwise (fun a b : α => Disjoint (f a) (f b)) l₁ :=
  by 
    simp only [List.bind, nodup_join, pairwise_map, and_comm, And.left_comm, mem_map, exists_imp_distrib, and_imp] <;>
      rw
        [show (∀ l : List β x : α, f x = l → x ∈ l₁ → nodup l) ↔ ∀ x : α, x ∈ l₁ → nodup (f x) from
          forall_swap.trans$ forall_congrₓ$ fun _ => forall_eq']

theorem nodup_product {l₁ : List α} {l₂ : List β} (d₁ : nodup l₁) (d₂ : nodup l₂) : nodup (product l₁ l₂) :=
  nodup_bind.2
    ⟨fun a ma => nodup_map (left_inverse.injective fun b => (rfl : (a, b).2 = b)) d₂,
      d₁.imp$
        fun a₁ a₂ n x h₁ h₂ =>
          by 
            rcases mem_map.1 h₁ with ⟨b₁, mb₁, rfl⟩
            rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
            exact n rfl⟩

theorem nodup_sigma {σ : α → Type _} {l₁ : List α} {l₂ : ∀ a, List (σ a)} (d₁ : nodup l₁) (d₂ : ∀ a, nodup (l₂ a)) :
  nodup (l₁.sigma l₂) :=
  nodup_bind.2
    ⟨fun a ma =>
        nodup_map
          (fun b b' h =>
            by 
              injection h with _ h <;> exact eq_of_heq h)
          (d₂ a),
      d₁.imp$
        fun a₁ a₂ n x h₁ h₂ =>
          by 
            rcases mem_map.1 h₁ with ⟨b₁, mb₁, rfl⟩
            rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
            exact n rfl⟩

theorem nodup_filter_map {f : α → Option β} {l : List α} (H : ∀ a a' : α b : β, b ∈ f a → b ∈ f a' → a = a') :
  nodup l → nodup (filter_map f l) :=
  pairwise_filter_map_of_pairwise f$ fun a a' n b bm b' bm' e => n$ H a a' b' (e ▸ bm) bm'

theorem nodup_concat {a : α} {l : List α} (h : a ∉ l) (h' : nodup l) : nodup (concat l a) :=
  by 
    rw [concat_eq_append] <;> exact nodup_append_of_nodup h' (nodup_singleton _) (disjoint_singleton.2 h)

theorem nodup_insert [DecidableEq α] {a : α} {l : List α} (h : nodup l) : nodup (insert a l) :=
  if h' : a ∈ l then
    by 
      rw [insert_of_mem h'] <;> exact h
  else
    by 
      rw [insert_of_not_mem h', nodup_cons] <;> split  <;> assumption

theorem nodup_union [DecidableEq α] (l₁ : List α) {l₂ : List α} (h : nodup l₂) : nodup (l₁ ∪ l₂) :=
  by 
    induction' l₁ with a l₁ ih generalizing l₂
    ·
      exact h 
    apply nodup_insert 
    exact ih h

theorem nodup_inter_of_nodup [DecidableEq α] {l₁ : List α} l₂ : nodup l₁ → nodup (l₁ ∩ l₂) :=
  nodup_filter _

@[simp]
theorem nodup_sublists {l : List α} : nodup (sublists l) ↔ nodup l :=
  ⟨fun h => nodup_of_nodup_map _ (nodup_of_sublist (map_ret_sublist_sublists _) h),
    fun h => (pairwise_sublists h).imp fun _ _ h => mt reverse_inj.2 h.to_ne⟩

@[simp]
theorem nodup_sublists' {l : List α} : nodup (sublists' l) ↔ nodup l :=
  by 
    rw [sublists'_eq_sublists, nodup_map_iff reverse_injective, nodup_sublists, nodup_reverse]

theorem nodup_sublists_len {α : Type _} n {l : List α} (nd : nodup l) : (sublists_len n l).Nodup :=
  nodup_of_sublist (sublists_len_sublist_sublists' _ _) (nodup_sublists'.2 nd)

theorem diff_eq_filter_of_nodup [DecidableEq α] : ∀ {l₁ l₂ : List α} hl₁ : l₁.nodup, l₁.diff l₂ = l₁.filter (· ∉ l₂)
| l₁, [], hl₁ =>
  by 
    simp 
| l₁, a :: l₂, hl₁ =>
  by 
    rw [diff_cons, diff_eq_filter_of_nodup (nodup_erase_of_nodup _ hl₁), nodup_erase_eq_filter _ hl₁, filter_filter]
    simp only [mem_cons_iff, not_or_distrib, And.comm]
    congr

theorem mem_diff_iff_of_nodup [DecidableEq α] {l₁ l₂ : List α} (hl₁ : l₁.nodup) {a : α} :
  a ∈ l₁.diff l₂ ↔ a ∈ l₁ ∧ a ∉ l₂ :=
  by 
    rw [diff_eq_filter_of_nodup hl₁, mem_filter]

theorem nodup_update_nth : ∀ {l : List α} {n : ℕ} {a : α} hl : l.nodup ha : a ∉ l, (l.update_nth n a).Nodup
| [], n, a, hl, ha => nodup_nil
| b :: l, 0, a, hl, ha => nodup_cons.2 ⟨mt (mem_cons_of_mem _) ha, (nodup_cons.1 hl).2⟩
| b :: l, n+1, a, hl, ha =>
  nodup_cons.2
    ⟨fun h => (mem_or_eq_of_mem_update_nth h).elim (nodup_cons.1 hl).1 fun hba => ha (hba ▸ mem_cons_self _ _),
      nodup_update_nth (nodup_cons.1 hl).2 (mt (mem_cons_of_mem _) ha)⟩

theorem nodup.map_update [DecidableEq α] {l : List α} (hl : l.nodup) (f : α → β) (x : α) (y : β) :
  l.map (Function.update f x y) = if x ∈ l then (l.map f).updateNth (l.index_of x) y else l.map f :=
  by 
    induction' l with hd tl ihl
    ·
      simp 
    rw [nodup_cons] at hl 
    simp only [mem_cons_iff, map, ihl hl.2]
    byCases' H : hd = x
    ·
      subst hd 
      simp [update_nth, hl.1]
    ·
      simp [Ne.symm H, H, update_nth, ←apply_ite (cons (f hd))]

theorem nodup.pairwise_of_forall_ne {l : List α} {r : α → α → Prop} (hl : l.nodup)
  (h : ∀ a _ : a ∈ l b _ : b ∈ l, a ≠ b → r a b) : l.pairwise r :=
  by 
    classical 
    refine' pairwise_of_reflexive_on_dupl_of_forall_ne _ h 
    intro x hx 
    rw [nodup_iff_count_le_one] at hl 
    exact absurd (hl x) hx.not_le

theorem nodup.pairwise_of_set_pairwise {l : List α} {r : α → α → Prop} (hl : l.nodup) (h : { x | x ∈ l }.Pairwise r) :
  l.pairwise r :=
  hl.pairwise_of_forall_ne h

end List

theorem Option.to_list_nodup {α} : ∀ o : Option α, o.to_list.nodup
| none => List.nodup_nil
| some x => List.nodup_singleton x

