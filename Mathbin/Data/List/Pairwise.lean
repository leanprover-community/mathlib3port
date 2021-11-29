import Mathbin.Data.List.Count 
import Mathbin.Data.List.Lex 
import Mathbin.Data.List.Sublists 
import Mathbin.Data.Set.Pairwise

/-!
# Pairwise relations on a list

This file provides basic results about `list.pairwise` and `list.pw_filter` (definitions are in
`data.list.defs`).
`pairwise r [a 0, ..., a (n - 1)]` means `∀ i j, i < j → r (a i) (a j)`. For example,
`pairwise (≠) l` means that all elements of `l` are distinct, and `pairwise (<) l` means that `l`
is strictly increasing.
`pw_filter r l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`pairwise r l'`.

## Tags

sorted, nodup
-/


open Nat Function

namespace List

variable{α β : Type _}{R : α → α → Prop}

mk_iff_of_inductive_prop List.Pairwise List.pairwise_iff

/-! ### Pairwise -/


theorem rel_of_pairwise_cons {a : α} {l : List α} (p : Pairwise R (a :: l)) : ∀ {a'}, a' ∈ l → R a a' :=
  (pairwise_cons.1 p).1

theorem pairwise_of_pairwise_cons {a : α} {l : List α} (p : Pairwise R (a :: l)) : Pairwise R l :=
  (pairwise_cons.1 p).2

theorem pairwise.tail : ∀ {l : List α} (p : Pairwise R l), Pairwise R l.tail
| [], h => h
| a :: l, h => pairwise_of_pairwise_cons h

theorem pairwise.drop : ∀ {l : List α} {n : ℕ}, List.Pairwise R l → List.Pairwise R (l.drop n)
| _, 0, h => h
| [], n+1, h => List.Pairwise.nil
| a :: l, n+1, h => pairwise.drop (pairwise_cons.mp h).right

theorem pairwise.imp_of_mem {S : α → α → Prop} {l : List α} (H : ∀ {a b}, a ∈ l → b ∈ l → R a b → S a b)
  (p : Pairwise R l) : Pairwise S l :=
  by 
    induction' p with a l r p IH generalizing H <;> constructor
    ·
      exact Ball.imp_right (fun x h => H (mem_cons_self _ _) (mem_cons_of_mem _ h)) r
    ·
      exact IH fun a b m m' => H (mem_cons_of_mem _ m) (mem_cons_of_mem _ m')

theorem pairwise.imp {S : α → α → Prop} (H : ∀ a b, R a b → S a b) {l : List α} : Pairwise R l → Pairwise S l :=
  pairwise.imp_of_mem fun a b _ _ => H a b

theorem pairwise.and {S : α → α → Prop} {l : List α} :
  Pairwise (fun a b => R a b ∧ S a b) l ↔ Pairwise R l ∧ Pairwise S l :=
  ⟨fun h => ⟨h.imp fun a b h => h.1, h.imp fun a b h => h.2⟩,
    fun ⟨hR, hS⟩ =>
      by 
        clear_ 
        induction' hR with a l R1 R2 IH <;> simp only [pairwise.nil, pairwise_cons] at *
        exact ⟨fun b bl => ⟨R1 b bl, hS.1 b bl⟩, IH hS.2⟩⟩

theorem pairwise.imp₂ {S : α → α → Prop} {T : α → α → Prop} (H : ∀ a b, R a b → S a b → T a b) {l : List α}
  (hR : Pairwise R l) (hS : Pairwise S l) : Pairwise T l :=
  (pairwise.and.2 ⟨hR, hS⟩).imp$ fun a b => And.ndrec (H a b)

theorem pairwise.iff_of_mem {S : α → α → Prop} {l : List α} (H : ∀ {a b}, a ∈ l → b ∈ l → (R a b ↔ S a b)) :
  Pairwise R l ↔ Pairwise S l :=
  ⟨pairwise.imp_of_mem fun a b m m' => (H m m').1, pairwise.imp_of_mem fun a b m m' => (H m m').2⟩

theorem pairwise.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} : Pairwise R l ↔ Pairwise S l :=
  pairwise.iff_of_mem fun a b _ _ => H a b

theorem pairwise_of_forall {l : List α} (H : ∀ x y, R x y) : Pairwise R l :=
  by 
    induction l <;> [exact pairwise.nil, simp only [pairwise_cons, forall_2_true_iff, and_trueₓ]]

-- error in Data.List.Pairwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pairwise.and_mem
{l : list α} : «expr ↔ »(pairwise R l, pairwise (λ
  x y, «expr ∧ »(«expr ∈ »(x, l), «expr ∧ »(«expr ∈ »(y, l), R x y))) l) :=
pairwise.iff_of_mem (by simp [] [] ["only"] ["[", expr true_and, ",", expr iff_self, ",", expr forall_2_true_iff, "]"] [] [] { contextual := tt })

-- error in Data.List.Pairwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pairwise.imp_mem
{l : list α} : «expr ↔ »(pairwise R l, pairwise (λ x y, «expr ∈ »(x, l) → «expr ∈ »(y, l) → R x y) l) :=
pairwise.iff_of_mem (by simp [] [] ["only"] ["[", expr forall_prop_of_true, ",", expr iff_self, ",", expr forall_2_true_iff, "]"] [] [] { contextual := tt })

theorem pairwise_of_sublist : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → Pairwise R l₂ → Pairwise R l₁
| _, _, sublist.slnil, h => h
| _, _, sublist.cons l₁ l₂ a s, pairwise.cons i n => pairwise_of_sublist s n
| _, _, sublist.cons2 l₁ l₂ a s, pairwise.cons i n => (pairwise_of_sublist s n).cons (Ball.imp_left s.subset i)

theorem forall_of_forall_of_pairwise (H : Symmetric R) {l : List α} (H₁ : ∀ x (_ : x ∈ l), R x x) (H₂ : Pairwise R l) :
  ∀ x (_ : x ∈ l) y (_ : y ∈ l), R x y :=
  by 
    induction' l with a l IH
    ·
      exact forall_mem_nil _ 
    cases' forall_mem_cons.1 H₁ with H₁₁ H₁₂ 
    cases' pairwise_cons.1 H₂ with H₂₁ H₂₂ 
    rintro x (rfl | hx) y (rfl | hy)
    exacts[H₁₁, H₂₁ _ hy, H (H₂₁ _ hx), IH H₁₂ H₂₂ _ hx _ hy]

theorem forall_of_pairwise (H : Symmetric R) {l : List α} (hl : Pairwise R l) :
  ∀ a (_ : a ∈ l), ∀ b (_ : b ∈ l), a ≠ b → R a b :=
  forall_of_forall_of_pairwise (fun a b h hne => H (h hne.symm)) (fun _ _ h => (h rfl).elim)
    (pairwise.imp (fun _ _ h _ => h) hl)

theorem pairwise_singleton R (a : α) : Pairwise R [a] :=
  by 
    simp only [pairwise_cons, mem_singleton, forall_prop_of_false (not_mem_nil _), forall_true_iff, pairwise.nil,
      and_trueₓ]

theorem pairwise_pair {a b : α} : Pairwise R [a, b] ↔ R a b :=
  by 
    simp only [pairwise_cons, mem_singleton, forall_eq, forall_prop_of_false (not_mem_nil _), forall_true_iff,
      pairwise.nil, and_trueₓ]

theorem pairwise_append {l₁ l₂ : List α} :
  Pairwise R (l₁ ++ l₂) ↔ Pairwise R l₁ ∧ Pairwise R l₂ ∧ ∀ x (_ : x ∈ l₁), ∀ y (_ : y ∈ l₂), R x y :=
  by 
    induction' l₁ with x l₁ IH <;>
      [simp only [List.Pairwise.nil, forall_prop_of_false (not_mem_nil _), forall_true_iff, and_trueₓ, true_andₓ,
        nil_append],
      simp only [cons_append, pairwise_cons, forall_mem_append, IH, forall_mem_cons, forall_and_distrib, and_assoc,
        And.left_comm]]

theorem pairwise_append_comm (s : Symmetric R) {l₁ l₂ : List α} : Pairwise R (l₁ ++ l₂) ↔ Pairwise R (l₂ ++ l₁) :=
  have  :
    ∀ (l₁ l₂ : List α),
      (∀ (x : α), x ∈ l₁ → ∀ (y : α), y ∈ l₂ → R x y) → ∀ (x : α), x ∈ l₂ → ∀ (y : α), y ∈ l₁ → R x y :=
    fun l₁ l₂ a x xm y ym => s (a y ym x xm)
  by 
    simp only [pairwise_append, And.left_comm] <;> rw [Iff.intro (this l₁ l₂) (this l₂ l₁)]

theorem pairwise_middle (s : Symmetric R) {a : α} {l₁ l₂ : List α} :
  Pairwise R (l₁ ++ a :: l₂) ↔ Pairwise R (a :: (l₁ ++ l₂)) :=
  show Pairwise R (l₁ ++ ([a] ++ l₂)) ↔ Pairwise R ([a] ++ l₁ ++ l₂)by 
    rw [←append_assoc, pairwise_append, @pairwise_append _ _ ([a] ++ l₁), pairwise_append_comm s] <;>
      simp only [mem_append, or_comm]

-- error in Data.List.Pairwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem pairwise_map
(f : β → α) : ∀ {l : list β}, «expr ↔ »(pairwise R (map f l), pairwise (λ a b : β, R (f a) (f b)) l)
| «expr[ , ]»([]) := by simp [] [] ["only"] ["[", expr map, ",", expr pairwise.nil, "]"] [] []
| «expr :: »(b, l) := have «expr ↔ »(∀
 a
 b', «expr ∈ »(b', l) → «expr = »(f b', a) → R (f b) a, ∀
 b' : β, «expr ∈ »(b', l) → R (f b) (f b')), from «expr $ »(forall_swap.trans, «expr $ »(forall_congr, λ
  a, «expr $ »(forall_swap.trans, by simp [] [] ["only"] ["[", expr forall_eq', "]"] [] []))),
by simp [] [] ["only"] ["[", expr map, ",", expr pairwise_cons, ",", expr mem_map, ",", expr exists_imp_distrib, ",", expr and_imp, ",", expr this, ",", expr pairwise_map, "]"] [] []

theorem pairwise_of_pairwise_map {S : β → β → Prop} (f : α → β) (H : ∀ (a b : α), S (f a) (f b) → R a b) {l : List α}
  (p : Pairwise S (map f l)) : Pairwise R l :=
  ((pairwise_map f).1 p).imp H

theorem pairwise_map_of_pairwise {S : β → β → Prop} (f : α → β) (H : ∀ (a b : α), R a b → S (f a) (f b)) {l : List α}
  (p : Pairwise R l) : Pairwise S (map f l) :=
  (pairwise_map f).2$ p.imp H

-- error in Data.List.Pairwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem pairwise_filter_map
(f : β → option α)
{l : list β} : «expr ↔ »(pairwise R (filter_map f l), pairwise (λ
  a a' : β, ∀ (b «expr ∈ » f a) (b' «expr ∈ » f a'), R b b') l) :=
let S (a a' : β) := ∀ (b «expr ∈ » f a) (b' «expr ∈ » f a'), R b b' in
begin
  simp [] [] ["only"] ["[", expr option.mem_def, "]"] [] [],
  induction [expr l] [] ["with", ident a, ident l, ident IH] [],
  { simp [] [] ["only"] ["[", expr filter_map, ",", expr pairwise.nil, "]"] [] [] },
  cases [expr e, ":", expr f a] ["with", ident b],
  { rw ["[", expr filter_map_cons_none _ _ e, ",", expr IH, ",", expr pairwise_cons, "]"] [],
    simp [] [] ["only"] ["[", expr e, ",", expr forall_prop_of_false not_false, ",", expr forall_3_true_iff, ",", expr true_and, "]"] [] [] },
  rw ["[", expr filter_map_cons_some _ _ _ e, "]"] [],
  simp [] [] ["only"] ["[", expr pairwise_cons, ",", expr mem_filter_map, ",", expr exists_imp_distrib, ",", expr and_imp, ",", expr IH, ",", expr e, ",", expr forall_eq', "]"] [] [],
  show [expr «expr ↔ »(«expr ∧ »(∀
     (a' : α)
     (x : β), «expr ∈ »(x, l) → «expr = »(f x, some a') → R b a', pairwise S l), «expr ∧ »(∀
     a' : β, «expr ∈ »(a', l) → ∀ b' : α, «expr = »(f a', some b') → R b b', pairwise S l))],
  from [expr and_congr ⟨λ h b mb a ma, h a b mb ma, λ h a b mb ma, h b mb a ma⟩ iff.rfl]
end

theorem pairwise_filter_map_of_pairwise {S : β → β → Prop} (f : α → Option β)
  (H : ∀ (a a' : α), R a a' → ∀ b (_ : b ∈ f a) b' (_ : b' ∈ f a'), S b b') {l : List α} (p : Pairwise R l) :
  Pairwise S (filter_map f l) :=
  (pairwise_filter_map _).2$ p.imp H

theorem pairwise_filter (p : α → Prop) [DecidablePred p] {l : List α} :
  Pairwise R (filter p l) ↔ Pairwise (fun x y => p x → p y → R x y) l :=
  by 
    rw [←filter_map_eq_filter, pairwise_filter_map]
    apply pairwise.iff 
    intros 
    simp only [Option.mem_def, Option.guard_eq_some, and_imp, forall_eq']

theorem pairwise_filter_of_pairwise (p : α → Prop) [DecidablePred p] {l : List α} :
  Pairwise R l → Pairwise R (filter p l) :=
  pairwise_of_sublist (filter_sublist _)

theorem pairwise_pmap {p : β → Prop} {f : ∀ b, p b → α} {l : List β} (h : ∀ x (_ : x ∈ l), p x) :
  Pairwise R (l.pmap f h) ↔ Pairwise (fun b₁ b₂ => ∀ (h₁ : p b₁) (h₂ : p b₂), R (f b₁ h₁) (f b₂ h₂)) l :=
  by 
    induction' l with a l ihl
    ·
      simp 
    obtain ⟨ha, hl⟩ : p a ∧ ∀ b, b ∈ l → p b
    ·
      simpa using h 
    simp only [ihl hl, pairwise_cons, bex_imp_distrib, pmap, And.congr_left_iff, mem_pmap]
    refine' fun _ => ⟨fun H b hb hpa hpb => H _ _ hb rfl, _⟩
    rintro H _ b hb rfl 
    exact H b hb _ _

theorem pairwise.pmap {l : List α} (hl : Pairwise R l) {p : α → Prop} {f : ∀ a, p a → β} (h : ∀ x (_ : x ∈ l), p x)
  {S : β → β → Prop} (hS : ∀ ⦃x⦄ (hx : p x) ⦃y⦄ (hy : p y), R x y → S (f x hx) (f y hy)) : Pairwise S (l.pmap f h) :=
  by 
    refine' (pairwise_pmap h).2 (pairwise.imp_of_mem _ hl)
    intros 
    apply hS 
    assumption

-- error in Data.List.Pairwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pairwise_join
{L : list (list α)} : «expr ↔ »(pairwise R (join L), «expr ∧ »(∀
  l «expr ∈ » L, pairwise R l, pairwise (λ l₁ l₂, ∀ (x «expr ∈ » l₁) (y «expr ∈ » l₂), R x y) L)) :=
begin
  induction [expr L] [] ["with", ident l, ident L, ident IH] [],
  { simp [] [] ["only"] ["[", expr join, ",", expr pairwise.nil, ",", expr forall_prop_of_false (not_mem_nil _), ",", expr forall_const, ",", expr and_self, "]"] [] [] },
  have [] [":", expr «expr ↔ »(∀
    x : α, «expr ∈ »(x, l) → ∀
    (y : α)
    (x_1 : list α), «expr ∈ »(x_1, L) → «expr ∈ »(y, x_1) → R x y, ∀
    a' : list α, «expr ∈ »(a', L) → ∀
    x : α, «expr ∈ »(x, l) → ∀
    y : α, «expr ∈ »(y, a') → R x y)] [":=", expr ⟨λ h a b c d e, h c d e a b, λ h c d e a b, h a b c d e⟩],
  simp [] [] ["only"] ["[", expr join, ",", expr pairwise_append, ",", expr IH, ",", expr mem_join, ",", expr exists_imp_distrib, ",", expr and_imp, ",", expr this, ",", expr forall_mem_cons, ",", expr pairwise_cons, "]"] [] [],
  simp [] [] ["only"] ["[", expr and_assoc, ",", expr and_comm, ",", expr and.left_comm, "]"] [] []
end

@[simp]
theorem pairwise_reverse : ∀ {R} {l : List α}, Pairwise R (reverse l) ↔ Pairwise (fun x y => R y x) l :=
  suffices ∀ {R l}, @Pairwise α R l → Pairwise (fun x y => R y x) (reverse l) from
    fun R l => ⟨fun p => reverse_reverse l ▸ this p, this⟩
  fun R l p =>
    by 
      induction' p with a l h p IH <;> [apply pairwise.nil,
        simpa only [reverse_cons, pairwise_append, IH, pairwise_cons, forall_prop_of_false (not_mem_nil _),
          forall_true_iff, pairwise.nil, mem_reverse, mem_singleton, forall_eq, true_andₓ] using h]

theorem Pairwise.set_pairwise {l : List α} (h : Pairwise R l) (hr : Symmetric R) : Set.Pairwise { x | x ∈ l } R :=
  by 
    induction' h with hd tl imp h IH
    ·
      simp 
    ·
      intro x hx y hy hxy 
      simp only [mem_cons_iff, Set.mem_set_of_eq] at hx hy 
      rcases hx with (rfl | hx) <;> rcases hy with (rfl | hy)
      ·
        contradiction
      ·
        exact imp y hy
      ·
        exact hr (imp x hx)
      ·
        exact IH x hx y hy hxy

theorem pairwise_of_reflexive_on_dupl_of_forall_ne [DecidableEq α] {l : List α} {r : α → α → Prop}
  (hr : ∀ a, 1 < count a l → r a a) (h : ∀ a (_ : a ∈ l) b (_ : b ∈ l), a ≠ b → r a b) : l.pairwise r :=
  by 
    induction' l with hd tl IH
    ·
      simp 
    ·
      rw [List.pairwise_consₓ]
      split 
      ·
        intro x hx 
        byCases' H : hd = x
        ·
          rw [H]
          refine' hr _ _ 
          simpa [count_cons, H, Nat.succ_lt_succ_iff, count_pos] using hx
        ·
          exact h hd (mem_cons_self _ _) x (mem_cons_of_mem _ hx) H
      ·
        refine' IH _ _
        ·
          intro x hx 
          refine' hr _ _ 
          rw [count_cons]
          splitIfs
          ·
            exact hx.trans (Nat.lt_succ_selfₓ _)
          ·
            exact hx
        ·
          intro x hx y hy 
          exact h x (mem_cons_of_mem _ hx) y (mem_cons_of_mem _ hy)

theorem pairwise_of_reflexive_of_forall_ne {l : List α} {r : α → α → Prop} (hr : Reflexive r)
  (h : ∀ a (_ : a ∈ l) b (_ : b ∈ l), a ≠ b → r a b) : l.pairwise r :=
  by 
    classical 
    refine' pairwise_of_reflexive_on_dupl_of_forall_ne _ h 
    exact fun _ _ => hr _

theorem pairwise_iff_nth_le {R} :
  ∀ {l : List α},
    Pairwise R l ↔ ∀ i j (h₁ : j < length l) (h₂ : i < j), R (nth_le l i (lt_transₓ h₂ h₁)) (nth_le l j h₁)
| [] =>
  by 
    simp only [pairwise.nil, true_iffₓ] <;> exact fun i j h => (Nat.not_lt_zeroₓ j).elim h
| a :: l =>
  by 
    rw [pairwise_cons, pairwise_iff_nth_le]
    refine' ⟨fun H i j h₁ h₂ => _, fun H => ⟨fun a' m => _, fun i j h₁ h₂ => H _ _ (succ_lt_succ h₁) (succ_lt_succ h₂)⟩⟩
    ·
      cases' j with j
      ·
        exact (Nat.not_lt_zeroₓ _).elim h₂ 
      cases' i with i
      ·
        exact H.1 _ (nth_le_mem l _ _)
      ·
        exact H.2 _ _ (lt_of_succ_lt_succ h₁) (lt_of_succ_lt_succ h₂)
    ·
      rcases nth_le_of_mem m with ⟨n, h, rfl⟩
      exact H _ _ (succ_lt_succ h) (succ_pos _)

-- error in Data.List.Pairwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pairwise_sublists' {R} : ∀ {l : list α}, pairwise R l → pairwise (lex (swap R)) (sublists' l)
| _, pairwise.nil := pairwise_singleton _ _
| _, @pairwise.cons _ _ a l H₁ H₂ := begin
  simp [] [] ["only"] ["[", expr sublists'_cons, ",", expr pairwise_append, ",", expr pairwise_map, ",", expr mem_sublists', ",", expr mem_map, ",", expr exists_imp_distrib, ",", expr and_imp, "]"] [] [],
  have [ident IH] [] [":=", expr pairwise_sublists' H₂],
  refine [expr ⟨IH, IH.imp (λ l₁ l₂, lex.cons), _⟩],
  intros [ident l₁, ident sl₁, ident x, ident l₂, ident sl₂, ident e],
  subst [expr e],
  cases [expr l₁] ["with", ident b, ident l₁],
  { constructor },
  exact [expr lex.rel «expr $ »(H₁ _, «expr $ »(sl₁.subset, mem_cons_self _ _))]
end

-- error in Data.List.Pairwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pairwise_sublists
{R}
{l : list α}
(H : pairwise R l) : pairwise (λ l₁ l₂, lex R (reverse l₁) (reverse l₂)) (sublists l) :=
by have [] [] [":=", expr pairwise_sublists' (pairwise_reverse.2 H)]; rwa ["[", expr sublists'_reverse, ",", expr pairwise_map, "]"] ["at", ident this]

/-! ### Pairwise filtering -/


variable[DecidableRel R]

@[simp]
theorem pw_filter_nil : pw_filter R [] = [] :=
  rfl

@[simp]
theorem pw_filter_cons_of_pos {a : α} {l : List α} (h : ∀ b (_ : b ∈ pw_filter R l), R a b) :
  pw_filter R (a :: l) = a :: pw_filter R l :=
  if_pos h

@[simp]
theorem pw_filter_cons_of_neg {a : α} {l : List α} (h : ¬∀ b (_ : b ∈ pw_filter R l), R a b) :
  pw_filter R (a :: l) = pw_filter R l :=
  if_neg h

-- error in Data.List.Pairwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem pw_filter_map
(f : β → α) : ∀ l : list β, «expr = »(pw_filter R (map f l), map f (pw_filter (λ x y, R (f x) (f y)) l))
| «expr[ , ]»([]) := rfl
| «expr :: »(x, xs) := if h : ∀
b «expr ∈ » pw_filter R (map f xs), R (f x) b then have h' : ∀
b : β, «expr ∈ »(b, pw_filter (λ
  x
  y : β, R (f x) (f y)) xs) → R (f x) (f b), from λ
b hb, h _ (by rw ["[", expr pw_filter_map, "]"] []; apply [expr mem_map_of_mem _ hb]),
by rw ["[", expr map, ",", expr pw_filter_cons_of_pos h, ",", expr pw_filter_cons_of_pos h', ",", expr pw_filter_map, ",", expr map, "]"] [] else have h' : «expr¬ »(∀
 b : β, «expr ∈ »(b, pw_filter (λ
   x
   y : β, R (f x) (f y)) xs) → R (f x) (f b)), from λ
hh, «expr $ »(h, λ a ha, by { rw ["[", expr pw_filter_map, ",", expr mem_map, "]"] ["at", ident ha],
   rcases [expr ha, "with", "⟨", ident b, ",", ident hb₀, ",", ident hb₁, "⟩"],
   subst [expr a],
   exact [expr hh _ hb₀] }),
by rw ["[", expr map, ",", expr pw_filter_cons_of_neg h, ",", expr pw_filter_cons_of_neg h', ",", expr pw_filter_map, "]"] []

theorem pw_filter_sublist : ∀ (l : List α), pw_filter R l <+ l
| [] => nil_sublist _
| x :: l =>
  by 
    byCases' ∀ y (_ : y ∈ pw_filter R l), R x y
    ·
      rw [pw_filter_cons_of_pos h]
      exact (pw_filter_sublist l).cons_cons _
    ·
      rw [pw_filter_cons_of_neg h]
      exact sublist_cons_of_sublist _ (pw_filter_sublist l)

theorem pw_filter_subset (l : List α) : pw_filter R l ⊆ l :=
  (pw_filter_sublist _).Subset

theorem pairwise_pw_filter : ∀ (l : List α), Pairwise R (pw_filter R l)
| [] => pairwise.nil
| x :: l =>
  by 
    byCases' ∀ y (_ : y ∈ pw_filter R l), R x y
    ·
      rw [pw_filter_cons_of_pos h]
      exact pairwise_cons.2 ⟨h, pairwise_pw_filter l⟩
    ·
      rw [pw_filter_cons_of_neg h]
      exact pairwise_pw_filter l

theorem pw_filter_eq_self {l : List α} : pw_filter R l = l ↔ Pairwise R l :=
  ⟨fun e => e ▸ pairwise_pw_filter l,
    fun p =>
      by 
        induction' l with x l IH
        ·
          rfl 
        cases' pairwise_cons.1 p with al p 
        rw [pw_filter_cons_of_pos (Ball.imp_left (pw_filter_subset l) al), IH p]⟩

@[simp]
theorem pw_filter_idempotent {l : List α} : pw_filter R (pw_filter R l) = pw_filter R l :=
  pw_filter_eq_self.mpr (pairwise_pw_filter l)

-- error in Data.List.Pairwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem forall_mem_pw_filter
(neg_trans : ∀ {x y z}, R x z → «expr ∨ »(R x y, R y z))
(a : α)
(l : list α) : «expr ↔ »(∀ b «expr ∈ » pw_filter R l, R a b, ∀ b «expr ∈ » l, R a b) :=
⟨begin
   induction [expr l] [] ["with", ident x, ident l, ident IH] [],
   { exact [expr λ _ _, false.elim] },
   simp [] [] ["only"] ["[", expr forall_mem_cons, "]"] [] [],
   by_cases [expr ∀ y «expr ∈ » pw_filter R l, R x y]; dsimp [] [] [] ["at", ident h],
   { simp [] [] ["only"] ["[", expr pw_filter_cons_of_pos h, ",", expr forall_mem_cons, ",", expr and_imp, "]"] [] [],
     exact [expr λ r H, ⟨r, IH H⟩] },
   { rw ["[", expr pw_filter_cons_of_neg h, "]"] [],
     refine [expr λ H, ⟨_, IH H⟩],
     cases [expr e, ":", expr find (λ y, «expr¬ »(R x y)) (pw_filter R l)] ["with", ident k],
     { refine [expr h.elim (ball.imp_right _ (find_eq_none.1 e))],
       exact [expr λ y _, not_not.1] },
     { have [] [] [":=", expr find_some e],
       exact [expr (neg_trans (H k (find_mem e))).resolve_right this] } }
 end, ball.imp_left (pw_filter_subset l)⟩

end List

