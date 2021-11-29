import Mathbin.Data.Multiset.Sort 
import Mathbin.Data.Fintype.List 
import Mathbin.Data.List.Rotate

/-!
# Cycles of a list

Lists have an equivalence relation of whether they are rotational permutations of one another.
This relation is defined as `is_rotated`.

Based on this, we define the quotient of lists by the rotation relation, called `cycle`.

We also define a representation of concrete cycles, available when viewing them in a goal state or
via `#eval`, when over representatble types. For example, the cycle `(2 1 4 3)` will be shown
as `c[1, 4, 3, 2]`. The representation of the cycle sorts the elements by the string value of the
underlying element. This representation also supports cycles that can contain duplicates.

-/


namespace List

variable{α : Type _}[DecidableEq α]

/-- Return the `z` such that `x :: z :: _` appears in `xs`, or `default` if there is no such `z`. -/
def next_or : ∀ (xs : List α) (x default : α), α
| [], x, default => default
| [y], x, default => default
| y :: z :: xs, x, default => if x = y then z else next_or (z :: xs) x default

@[simp]
theorem next_or_nil (x d : α) : next_or [] x d = d :=
  rfl

@[simp]
theorem next_or_singleton (x y d : α) : next_or [y] x d = d :=
  rfl

@[simp]
theorem next_or_self_cons_cons (xs : List α) (x y d : α) : next_or (x :: y :: xs) x d = y :=
  if_pos rfl

theorem next_or_cons_of_ne (xs : List α) (y x d : α) (h : x ≠ y) : next_or (y :: xs) x d = next_or xs x d :=
  by 
    cases' xs with z zs
    ·
      rfl
    ·
      exact if_neg h

/-- `next_or` does not depend on the default value, if the next value appears. -/
theorem next_or_eq_next_or_of_mem_of_ne (xs : List α) (x d d' : α) (x_mem : x ∈ xs)
  (x_ne : x ≠ xs.last (ne_nil_of_mem x_mem)) : next_or xs x d = next_or xs x d' :=
  by 
    induction' xs with y ys IH
    ·
      cases x_mem 
    cases' ys with z zs
    ·
      simp  at x_mem x_ne 
      contradiction 
    byCases' h : x = y
    ·
      rw [h, next_or_self_cons_cons, next_or_self_cons_cons]
    ·
      rw [next_or, next_or, IH] <;> simpa [h] using x_mem

theorem mem_of_next_or_ne {xs : List α} {x d : α} (h : next_or xs x d ≠ d) : x ∈ xs :=
  by 
    induction' xs with y ys IH
    ·
      simpa using h 
    cases' ys with z zs
    ·
      simpa using h
    ·
      byCases' hx : x = y
      ·
        simp [hx]
      ·
        rw [next_or_cons_of_ne _ _ _ _ hx] at h 
        simpa [hx] using IH h

theorem next_or_concat {xs : List α} {x : α} (d : α) (h : x ∉ xs) : next_or (xs ++ [x]) x d = d :=
  by 
    induction' xs with z zs IH
    ·
      simp 
    ·
      obtain ⟨hz, hzs⟩ := not_or_distrib.mp (mt (mem_cons_iff _ _ _).mp h)
      rw [cons_append, next_or_cons_of_ne _ _ _ _ hz, IH hzs]

theorem next_or_mem {xs : List α} {x d : α} (hd : d ∈ xs) : next_or xs x d ∈ xs :=
  by 
    revert hd 
    suffices  : ∀ (xs' : List α) (h : ∀ x (_ : x ∈ xs), x ∈ xs') (hd : d ∈ xs'), next_or xs x d ∈ xs'
    ·
      exact this xs fun _ => id 
    intro xs' hxs' hd 
    induction' xs with y ys ih
    ·
      exact hd 
    cases' ys with z zs
    ·
      exact hd 
    rw [next_or]
    splitIfs with h
    ·
      exact hxs' _ (mem_cons_of_mem _ (mem_cons_self _ _))
    ·
      exact ih fun _ h => hxs' _ (mem_cons_of_mem _ h)

/--
Given an element `x : α` of `l : list α` such that `x ∈ l`, get the next
element of `l`. This works from head to tail, (including a check for last element)
so it will match on first hit, ignoring later duplicates.

For example:
 * `next [1, 2, 3] 2 _ = 3`
 * `next [1, 2, 3] 3 _ = 1`
 * `next [1, 2, 3, 2, 4] 2 _ = 3`
 * `next [1, 2, 3, 2] 2 _ = 3`
 * `next [1, 1, 2, 3, 2] 1 _ = 1`
-/
def next (l : List α) (x : α) (h : x ∈ l) : α :=
  next_or l x (l.nth_le 0 (length_pos_of_mem h))

/--
Given an element `x : α` of `l : list α` such that `x ∈ l`, get the previous
element of `l`. This works from head to tail, (including a check for last element)
so it will match on first hit, ignoring later duplicates.

 * `prev [1, 2, 3] 2 _ = 1`
 * `prev [1, 2, 3] 1 _ = 3`
 * `prev [1, 2, 3, 2, 4] 2 _ = 1`
 * `prev [1, 2, 3, 4, 2] 2 _ = 1`
 * `prev [1, 1, 2] 1 _ = 2`
-/
def prev : ∀ (l : List α) (x : α) (h : x ∈ l), α
| [], _, h =>
  by 
    simpa using h
| [y], _, _ => y
| y :: z :: xs, x, h =>
  if hx : x = y then last (z :: xs) (cons_ne_nil _ _) else
    if x = z then y else
      prev (z :: xs) x
        (by 
          simpa [hx] using h)

variable(l : List α)(x : α)(h : x ∈ l)

@[simp]
theorem next_singleton (x y : α) (h : x ∈ [y]) : next [y] x h = y :=
  rfl

@[simp]
theorem prev_singleton (x y : α) (h : x ∈ [y]) : prev [y] x h = y :=
  rfl

theorem next_cons_cons_eq' (y z : α) (h : x ∈ y :: z :: l) (hx : x = y) : next (y :: z :: l) x h = z :=
  by 
    rw [next, next_or, if_pos hx]

@[simp]
theorem next_cons_cons_eq (z : α) (h : x ∈ x :: z :: l) : next (x :: z :: l) x h = z :=
  next_cons_cons_eq' l x x z h rfl

theorem next_ne_head_ne_last (y : α) (h : x ∈ y :: l) (hy : x ≠ y) (hx : x ≠ last (y :: l) (cons_ne_nil _ _)) :
  next (y :: l) x h =
    next l x
      (by 
        simpa [hy] using h) :=
  by 
    rw [next, next, next_or_cons_of_ne _ _ _ _ hy, next_or_eq_next_or_of_mem_of_ne]
    ·
      rwa [last_cons] at hx
    ·
      simpa [hy] using h

theorem next_cons_concat (y : α) (hy : x ≠ y) (hx : x ∉ l)
  (h : x ∈ y :: l ++ [x] := mem_append_right _ (mem_singleton_self x)) : next (y :: l ++ [x]) x h = y :=
  by 
    rw [next, next_or_concat]
    ·
      rfl
    ·
      simp [hy, hx]

theorem next_last_cons (y : α) (h : x ∈ y :: l) (hy : x ≠ y) (hx : x = last (y :: l) (cons_ne_nil _ _)) (hl : nodup l) :
  next (y :: l) x h = y :=
  by 
    rw [next, nth_le, ←init_append_last (cons_ne_nil y l), hx, next_or_concat]
    subst hx 
    intro H 
    obtain ⟨_ | k, hk, hk'⟩ := nth_le_of_mem H
    ·
      simpa [init_eq_take, nth_le_take', hy.symm] using hk' 
    suffices  : k.succ = l.length
    ·
      simpa [this] using hk 
    cases' l with hd tl
    ·
      simpa using hk
    ·
      rw [nodup_iff_nth_le_inj] at hl 
      rw [length, Nat.succ_inj']
      apply hl 
      simpa [init_eq_take, nth_le_take', last_eq_nth_le] using hk'

theorem prev_last_cons' (y : α) (h : x ∈ y :: l) (hx : x = y) : prev (y :: l) x h = last (y :: l) (cons_ne_nil _ _) :=
  by 
    cases l <;> simp [prev, hx]

@[simp]
theorem prev_last_cons (h : x ∈ x :: l) : prev (x :: l) x h = last (x :: l) (cons_ne_nil _ _) :=
  prev_last_cons' l x x h rfl

theorem prev_cons_cons_eq' (y z : α) (h : x ∈ y :: z :: l) (hx : x = y) :
  prev (y :: z :: l) x h = last (z :: l) (cons_ne_nil _ _) :=
  by 
    rw [prev, dif_pos hx]

@[simp]
theorem prev_cons_cons_eq (z : α) (h : x ∈ x :: z :: l) : prev (x :: z :: l) x h = last (z :: l) (cons_ne_nil _ _) :=
  prev_cons_cons_eq' l x x z h rfl

theorem prev_cons_cons_of_ne' (y z : α) (h : x ∈ y :: z :: l) (hy : x ≠ y) (hz : x = z) : prev (y :: z :: l) x h = y :=
  by 
    cases l
    ·
      simp [prev, hy, hz]
    ·
      rw [prev, dif_neg hy, if_pos hz]

theorem prev_cons_cons_of_ne (y : α) (h : x ∈ y :: x :: l) (hy : x ≠ y) : prev (y :: x :: l) x h = y :=
  prev_cons_cons_of_ne' _ _ _ _ _ hy rfl

theorem prev_ne_cons_cons (y z : α) (h : x ∈ y :: z :: l) (hy : x ≠ y) (hz : x ≠ z) :
  prev (y :: z :: l) x h =
    prev (z :: l) x
      (by 
        simpa [hy] using h) :=
  by 
    cases l
    ·
      simpa [hy, hz] using h
    ·
      rw [prev, dif_neg hy, if_neg hz]

include h

theorem next_mem : l.next x h ∈ l :=
  next_or_mem (nth_le_mem _ _ _)

theorem prev_mem : l.prev x h ∈ l :=
  by 
    cases' l with hd tl
    ·
      simpa using h 
    induction' tl with hd' tl hl generalizing hd
    ·
      simp 
    ·
      byCases' hx : x = hd
      ·
        simp only [hx, prev_cons_cons_eq]
        exact mem_cons_of_mem _ (last_mem _)
      ·
        rw [prev, dif_neg hx]
        splitIfs with hm
        ·
          exact mem_cons_self _ _
        ·
          exact mem_cons_of_mem _ (hl _ _)

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem next_nth_le
(l : list α)
(h : nodup l)
(n : exprℕ())
(hn : «expr < »(n, l.length)) : «expr = »(next l (l.nth_le n hn) (nth_le_mem _ _ _), l.nth_le «expr % »(«expr + »(n, 1), l.length) (nat.mod_lt _ (n.zero_le.trans_lt hn))) :=
begin
  cases [expr l] ["with", ident x, ident l],
  { simpa [] [] [] [] [] ["using", expr hn] },
  induction [expr l] [] ["with", ident y, ident l, ident hl] ["generalizing", ident x, ident n],
  { simp [] [] [] [] [] [] },
  { cases [expr n] [],
    { simp [] [] [] [] [] [] },
    { have [ident hn'] [":", expr «expr ≤ »(n.succ, l.length.succ)] [],
      { refine [expr nat.succ_le_of_lt _],
        simpa [] [] [] ["[", expr nat.succ_lt_succ_iff, "]"] [] ["using", expr hn] },
      have [ident hx'] [":", expr «expr ≠ »([«expr :: »/«expr :: »/«expr :: »](x, [«expr :: »/«expr :: »/«expr :: »](y, l)).nth_le n.succ hn, x)] [],
      { intro [ident H],
        suffices [] [":", expr «expr = »(n.succ, 0)],
        { simpa [] [] [] [] [] [] },
        rw [expr nodup_iff_nth_le_inj] ["at", ident h],
        refine [expr h _ _ hn nat.succ_pos' _],
        simpa [] [] [] [] [] ["using", expr H] },
      rcases [expr hn'.eq_or_lt, "with", ident hn'', "|", ident hn''],
      { rw ["[", expr next_last_cons, "]"] [],
        { simp [] [] [] ["[", expr hn'', "]"] [] [] },
        { exact [expr hx'] },
        { simp [] [] [] ["[", expr last_eq_nth_le, ",", expr hn'', "]"] [] [] },
        { exact [expr nodup_of_nodup_cons h] } },
      { have [] [":", expr «expr < »(n, l.length)] [":=", expr by simpa [] [] [] ["[", expr nat.succ_lt_succ_iff, "]"] [] ["using", expr hn'']],
        rw ["[", expr next_ne_head_ne_last _ _ _ _ hx', "]"] [],
        { simp [] [] [] ["[", expr nat.mod_eq_of_lt (nat.succ_lt_succ (nat.succ_lt_succ this)), ",", expr hl _ _ (nodup_of_nodup_cons h), ",", expr nat.mod_eq_of_lt (nat.succ_lt_succ this), "]"] [] [] },
        { rw [expr last_eq_nth_le] [],
          intro [ident H],
          suffices [] [":", expr «expr = »(n.succ, l.length.succ)],
          { exact [expr absurd hn'' this.ge.not_lt] },
          rw [expr nodup_iff_nth_le_inj] ["at", ident h],
          refine [expr h _ _ hn _ _],
          { simp [] [] [] [] [] [] },
          { simpa [] [] [] [] [] ["using", expr H] } } } } }
end

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prev_nth_le
(l : list α)
(h : nodup l)
(n : exprℕ())
(hn : «expr < »(n, l.length)) : «expr = »(prev l (l.nth_le n hn) (nth_le_mem _ _ _), l.nth_le «expr % »(«expr + »(n, «expr - »(l.length, 1)), l.length) (nat.mod_lt _ (n.zero_le.trans_lt hn))) :=
begin
  cases [expr l] ["with", ident x, ident l],
  { simpa [] [] [] [] [] ["using", expr hn] },
  induction [expr l] [] ["with", ident y, ident l, ident hl] ["generalizing", ident n, ident x],
  { simp [] [] [] [] [] [] },
  { rcases [expr n, "with", "_", "|", "_", "|", ident n],
    { simpa [] [] [] ["[", expr last_eq_nth_le, ",", expr nat.mod_eq_of_lt (nat.succ_lt_succ l.length.lt_succ_self), "]"] [] [] },
    { simp [] [] ["only"] ["[", expr mem_cons_iff, ",", expr nodup_cons, "]"] [] ["at", ident h],
      push_neg ["at", ident h],
      simp [] [] [] ["[", expr add_comm, ",", expr prev_cons_cons_of_ne, ",", expr h.left.left.symm, "]"] [] [] },
    { rw ["[", expr prev_ne_cons_cons, "]"] [],
      { convert [] [expr hl _ _ (nodup_of_nodup_cons h) _] ["using", 1],
        have [] [":", expr ∀
         k
         hk, «expr = »([«expr :: »/«expr :: »/«expr :: »](y, l).nth_le k hk, [«expr :: »/«expr :: »/«expr :: »](x, [«expr :: »/«expr :: »/«expr :: »](y, l)).nth_le «expr + »(k, 1) (nat.succ_lt_succ hk))] [],
        { intros [],
          simpa [] [] [] [] [] [] },
        rw ["[", expr this, "]"] [],
        congr,
        simp [] [] ["only"] ["[", expr nat.add_succ_sub_one, ",", expr add_zero, ",", expr length, "]"] [] [],
        simp [] [] ["only"] ["[", expr length, ",", expr nat.succ_lt_succ_iff, "]"] [] ["at", ident hn],
        set [] [ident k] [] [":="] [expr l.length] [],
        rw ["[", expr nat.succ_add, ",", "<-", expr nat.add_succ, ",", expr nat.add_mod_right, ",", expr nat.succ_add, ",", "<-", expr nat.add_succ _ k, ",", expr nat.add_mod_right, ",", expr nat.mod_eq_of_lt, ",", expr nat.mod_eq_of_lt, "]"] [],
        { exact [expr nat.lt_succ_of_lt hn] },
        { exact [expr nat.succ_lt_succ (nat.lt_succ_of_lt hn)] } },
      { intro [ident H],
        suffices [] [":", expr «expr = »(n.succ.succ, 0)],
        { simpa [] [] [] [] [] [] },
        rw [expr nodup_iff_nth_le_inj] ["at", ident h],
        refine [expr h _ _ hn nat.succ_pos' _],
        simpa [] [] [] [] [] ["using", expr H] },
      { intro [ident H],
        suffices [] [":", expr «expr = »(n.succ.succ, 1)],
        { simpa [] [] [] [] [] [] },
        rw [expr nodup_iff_nth_le_inj] ["at", ident h],
        refine [expr h _ _ hn (nat.succ_lt_succ nat.succ_pos') _],
        simpa [] [] [] [] [] ["using", expr H] } } }
end

theorem pmap_next_eq_rotate_one (h : nodup l) : (l.pmap l.next fun _ h => h) = l.rotate 1 :=
  by 
    apply List.ext_le
    ·
      simp 
    ·
      intros 
      rw [nth_le_pmap, nth_le_rotate, next_nth_le _ h]

theorem pmap_prev_eq_rotate_length_sub_one (h : nodup l) : (l.pmap l.prev fun _ h => h) = l.rotate (l.length - 1) :=
  by 
    apply List.ext_le
    ·
      simp 
    ·
      intro n hn hn' 
      rw [nth_le_rotate, nth_le_pmap, prev_nth_le _ h]

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prev_next
(l : list α)
(h : nodup l)
(x : α)
(hx : «expr ∈ »(x, l)) : «expr = »(prev l (next l x hx) (next_mem _ _ _), x) :=
begin
  obtain ["⟨", ident n, ",", ident hn, ",", ident rfl, "⟩", ":=", expr nth_le_of_mem hx],
  simp [] [] ["only"] ["[", expr next_nth_le, ",", expr prev_nth_le, ",", expr h, ",", expr nat.mod_add_mod, "]"] [] [],
  cases [expr l] ["with", ident hd, ident tl],
  { simp [] [] [] [] [] [] },
  { have [] [":", expr «expr < »(n, «expr + »(1, tl.length))] [":=", expr by simpa [] [] [] ["[", expr add_comm, "]"] [] ["using", expr hn]],
    simp [] [] [] ["[", expr add_left_comm, ",", expr add_comm, ",", expr add_assoc, ",", expr nat.mod_eq_of_lt this, "]"] [] [] }
end

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem next_prev
(l : list α)
(h : nodup l)
(x : α)
(hx : «expr ∈ »(x, l)) : «expr = »(next l (prev l x hx) (prev_mem _ _ _), x) :=
begin
  obtain ["⟨", ident n, ",", ident hn, ",", ident rfl, "⟩", ":=", expr nth_le_of_mem hx],
  simp [] [] ["only"] ["[", expr next_nth_le, ",", expr prev_nth_le, ",", expr h, ",", expr nat.mod_add_mod, "]"] [] [],
  cases [expr l] ["with", ident hd, ident tl],
  { simp [] [] [] [] [] [] },
  { have [] [":", expr «expr < »(n, «expr + »(1, tl.length))] [":=", expr by simpa [] [] [] ["[", expr add_comm, "]"] [] ["using", expr hn]],
    simp [] [] [] ["[", expr add_left_comm, ",", expr add_comm, ",", expr add_assoc, ",", expr nat.mod_eq_of_lt this, "]"] [] [] }
end

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prev_reverse_eq_next
(l : list α)
(h : nodup l)
(x : α)
(hx : «expr ∈ »(x, l)) : «expr = »(prev l.reverse x (mem_reverse.mpr hx), next l x hx) :=
begin
  obtain ["⟨", ident k, ",", ident hk, ",", ident rfl, "⟩", ":=", expr nth_le_of_mem hx],
  have [ident lpos] [":", expr «expr < »(0, l.length)] [":=", expr k.zero_le.trans_lt hk],
  have [ident key] [":", expr «expr < »(«expr - »(«expr - »(l.length, 1), k), l.length)] [":=", expr (nat.sub_le _ _).trans_lt (tsub_lt_self lpos nat.succ_pos')],
  rw ["<-", expr nth_le_pmap l.next (λ _ h, h) (by simpa [] [] [] [] [] ["using", expr hk])] [],
  simp_rw ["[", "<-", expr nth_le_reverse l k (key.trans_le (by simp [] [] [] [] [] [])), ",", expr pmap_next_eq_rotate_one _ h, "]"] [],
  rw ["<-", expr nth_le_pmap l.reverse.prev (λ _ h, h)] [],
  { simp_rw ["[", expr pmap_prev_eq_rotate_length_sub_one _ (nodup_reverse.mpr h), ",", expr rotate_reverse, ",", expr length_reverse, ",", expr nat.mod_eq_of_lt (tsub_lt_self lpos nat.succ_pos'), ",", expr tsub_tsub_cancel_of_le (nat.succ_le_of_lt lpos), "]"] [],
    rw ["<-", expr nth_le_reverse] [],
    { simp [] [] [] ["[", expr tsub_tsub_cancel_of_le (nat.le_pred_of_lt hk), "]"] [] [] },
    { simpa [] [] [] [] [] ["using", expr (nat.sub_le _ _).trans_lt (tsub_lt_self lpos nat.succ_pos')] } },
  { simpa [] [] [] [] [] ["using", expr (nat.sub_le _ _).trans_lt (tsub_lt_self lpos nat.succ_pos')] }
end

theorem next_reverse_eq_prev (l : List α) (h : nodup l) (x : α) (hx : x ∈ l) :
  next l.reverse x (mem_reverse.mpr hx) = prev l x hx :=
  by 
    convert (prev_reverse_eq_next l.reverse (nodup_reverse.mpr h) x (mem_reverse.mpr hx)).symm 
    exact (reverse_reverse l).symm

theorem is_rotated_next_eq {l l' : List α} (h : l ~r l') (hn : nodup l) {x : α} (hx : x ∈ l) :
  l.next x hx = l'.next x (h.mem_iff.mp hx) :=
  by 
    obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx 
    obtain ⟨n, rfl⟩ := id h 
    rw [next_nth_le _ hn]
    simpRw [←nth_le_rotate' _ n k]
    rw [next_nth_le _ (h.nodup_iff.mp hn), ←nth_le_rotate' _ n]
    simp [add_assocₓ]

theorem is_rotated_prev_eq {l l' : List α} (h : l ~r l') (hn : nodup l) {x : α} (hx : x ∈ l) :
  l.prev x hx = l'.prev x (h.mem_iff.mp hx) :=
  by 
    rw [←next_reverse_eq_prev _ hn, ←next_reverse_eq_prev _ (h.nodup_iff.mp hn)]
    exact is_rotated_next_eq h.reverse (nodup_reverse.mpr hn) _

end List

open List

/--
`cycle α` is the quotient of `list α` by cyclic permutation.
Duplicates are allowed.
-/
def Cycle (α : Type _) : Type _ :=
  Quotientₓ (is_rotated.setoid α)

namespace Cycle

variable{α : Type _}

instance  : Coe (List α) (Cycle α) :=
  ⟨Quot.mk _⟩

@[simp]
theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Cycle α) = l₂ ↔ l₁ ~r l₂ :=
  @Quotientₓ.eq _ (is_rotated.setoid _) _ _

@[simp]
theorem mk_eq_coe (l : List α) : Quot.mk _ l = (l : Cycle α) :=
  rfl

@[simp]
theorem mk'_eq_coe (l : List α) : Quotientₓ.mk' l = (l : Cycle α) :=
  rfl

instance  : Inhabited (Cycle α) :=
  ⟨(([] : List α) : Cycle α)⟩

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
For `x : α`, `s : cycle α`, `x ∈ s` indicates that `x` occurs at least once in `s`.
-/ def mem (a : α) (s : cycle α) : exprProp() :=
quot.lift_on s (λ l, «expr ∈ »(a, l)) (λ (l₁ l₂) (e : «expr ~r »(l₁, l₂)), «expr $ »(propext, e.mem_iff))

instance  : HasMem α (Cycle α) :=
  ⟨mem⟩

@[simp]
theorem mem_coe_iff {a : α} {l : List α} : a ∈ (l : Cycle α) ↔ a ∈ l :=
  Iff.rfl

instance  [DecidableEq α] : DecidableEq (Cycle α) :=
  fun s₁ s₂ => Quotientₓ.recOnSubsingleton₂' s₁ s₂ fun l₁ l₂ => decidableOfIff' _ Quotientₓ.eq'

instance  [DecidableEq α] (x : α) (s : Cycle α) : Decidable (x ∈ s) :=
  Quotientₓ.recOnSubsingleton' s fun l => List.decidableMemₓ x l

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
Reverse a `s : cycle α` by reversing the underlying `list`.
-/ def reverse (s : cycle α) : cycle α :=
quot.map reverse (λ (l₁ l₂) (e : «expr ~r »(l₁, l₂)), e.reverse) s

@[simp]
theorem reverse_coe (l : List α) : (l : Cycle α).reverse = l.reverse :=
  rfl

@[simp]
theorem mem_reverse_iff {a : α} {s : Cycle α} : a ∈ s.reverse ↔ a ∈ s :=
  Quot.induction_on s fun _ => mem_reverse

@[simp]
theorem reverse_reverse (s : Cycle α) : s.reverse.reverse = s :=
  Quot.induction_on s
    fun _ =>
      by 
        simp 

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
The length of the `s : cycle α`, which is the number of elements, counting duplicates.
-/ def length (s : cycle α) : exprℕ() :=
quot.lift_on s length (λ (l₁ l₂) (e : «expr ~r »(l₁, l₂)), e.perm.length_eq)

@[simp]
theorem length_coe (l : List α) : length (l : Cycle α) = l.length :=
  rfl

@[simp]
theorem length_reverse (s : Cycle α) : s.reverse.length = s.length :=
  Quot.induction_on s length_reverse

/--
A `s : cycle α` that is at most one element.
-/
def Subsingleton (s : Cycle α) : Prop :=
  s.length ≤ 1

theorem length_subsingleton_iff {s : Cycle α} : Subsingleton s ↔ length s ≤ 1 :=
  Iff.rfl

@[simp]
theorem subsingleton_reverse_iff {s : Cycle α} : s.reverse.subsingleton ↔ s.subsingleton :=
  by 
    simp [length_subsingleton_iff]

theorem subsingleton.congr {s : Cycle α} (h : Subsingleton s) : ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), x = y :=
  by 
    induction' s using Quot.induction_on with l 
    simp only [length_subsingleton_iff, length_coe, mk_eq_coe, le_iff_lt_or_eqₓ, Nat.lt_add_one_iff, length_eq_zero,
      length_eq_one, Nat.not_lt_zeroₓ, false_orₓ] at h 
    rcases h with (rfl | ⟨z, rfl⟩) <;> simp 

/--
A `s : cycle α` that is made up of at least two unique elements.
-/
def Nontrivial (s : Cycle α) : Prop :=
  ∃ (x y : α)(h : x ≠ y), x ∈ s ∧ y ∈ s

@[simp]
theorem nontrivial_coe_nodup_iff {l : List α} (hl : l.nodup) : Nontrivial (l : Cycle α) ↔ 2 ≤ l.length :=
  by 
    rw [Nontrivial]
    rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
    ·
      simp 
    ·
      simp 
    ·
      simp only [mem_cons_iff, exists_prop, mem_coe_iff, List.length, Ne.def, Nat.succ_le_succ_iff, zero_le, iff_trueₓ]
      refine'
        ⟨hd, hd', _,
          by 
            simp ⟩
      simp only [not_or_distrib, mem_cons_iff, nodup_cons] at hl 
      exact hl.left.left

@[simp]
theorem nontrivial_reverse_iff {s : Cycle α} : s.reverse.nontrivial ↔ s.nontrivial :=
  by 
    simp [Nontrivial]

theorem length_nontrivial {s : Cycle α} (h : Nontrivial s) : 2 ≤ length s :=
  by 
    obtain ⟨x, y, hxy, hx, hy⟩ := h 
    induction' s using Quot.induction_on with l 
    rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩)
    ·
      simpa using hx
    ·
      simp only [mem_coe_iff, mk_eq_coe, mem_singleton] at hx hy 
      simpa [hx, hy] using hxy
    ·
      simp [bit0]

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
The `s : cycle α` contains no duplicates.
-/ def nodup (s : cycle α) : exprProp() :=
quot.lift_on s nodup (λ (l₁ l₂) (e : «expr ~r »(l₁, l₂)), «expr $ »(propext, e.nodup_iff))

@[simp]
theorem nodup_coe_iff {l : List α} : nodup (l : Cycle α) ↔ l.nodup :=
  Iff.rfl

@[simp]
theorem nodup_reverse_iff {s : Cycle α} : s.reverse.nodup ↔ s.nodup :=
  Quot.induction_on s fun _ => nodup_reverse

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem subsingleton.nodup {s : cycle α} (h : subsingleton s) : nodup s :=
begin
  induction [expr s] ["using", ident quot.induction_on] ["with", ident l] [],
  cases [expr l] ["with", ident hd, ident tl],
  { simp [] [] [] [] [] [] },
  { have [] [":", expr «expr = »(tl, «expr[ , ]»([]))] [":=", expr by simpa [] [] [] ["[", expr subsingleton, ",", expr length_eq_zero, "]"] [] ["using", expr h]],
    simp [] [] [] ["[", expr this, "]"] [] [] }
end

theorem nodup.nontrivial_iff {s : Cycle α} (h : nodup s) : Nontrivial s ↔ ¬Subsingleton s :=
  by 
    rw [length_subsingleton_iff]
    induction s using Quotientₓ.induction_on' 
    simp only [mk'_eq_coe, nodup_coe_iff] at h 
    simp [h, Nat.succ_le_iff]

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
The `s : cycle α` as a `multiset α`.
-/ def to_multiset (s : cycle α) : multiset α :=
quotient.lift_on' s (λ l, (l : multiset α)) (λ (l₁ l₂) (h : «expr ~r »(l₁, l₂)), multiset.coe_eq_coe.mpr h.perm)

/--
The lift of `list.map`.
-/
def map {β : Type _} (f : α → β) : Cycle α → Cycle β :=
  Quotientₓ.map' (List.map f)$ fun l₁ l₂ h => h.map _

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/--
The `multiset` of lists that can make the cycle.
-/ def lists (s : cycle α) : multiset (list α) :=
«expr $ »(quotient.lift_on' s (λ
  l, (l.cyclic_permutations : multiset (list α))), λ
 (l₁ l₂)
 (h : «expr ~r »(l₁, l₂)), by simpa [] [] [] [] [] ["using", expr h.cyclic_permutations.perm])

@[simp]
theorem mem_lists_iff_coe_eq {s : Cycle α} {l : List α} : l ∈ s.lists ↔ (l : Cycle α) = s :=
  by 
    induction s using Quotientₓ.induction_on' 
    rw [lists, Quotientₓ.lift_on'_mk']
    simp 

section Decidable

variable[DecidableEq α]

/--
Auxiliary decidability algorithm for lists that contain at least two unique elements.
-/
def decidable_nontrivial_coe : ∀ (l : List α), Decidable (Nontrivial (l : Cycle α))
| [] =>
  is_false
    (by 
      simp [Nontrivial])
| [x] =>
  is_false
    (by 
      simp [Nontrivial])
| x :: y :: l =>
  if h : x = y then
    @decidableOfIff' _ (Nontrivial (x :: l : Cycle α))
      (by 
        simp [h, Nontrivial])
      (decidable_nontrivial_coe (x :: l))
  else
    is_true
      ⟨x, y, h,
        by 
          simp ,
        by 
          simp ⟩

instance  {s : Cycle α} : Decidable (Nontrivial s) :=
  Quot.recOnSubsingletonₓ s decidable_nontrivial_coe

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance {s : cycle α} : decidable (nodup s) := quot.rec_on_subsingleton s (λ l : list α, list.nodup_decidable l)

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance fintype_nodup_cycle [fintype α] : fintype {s : cycle α // s.nodup} :=
fintype.of_surjective (λ
 l : {l : list α // l.nodup}, ⟨l.val, by simpa [] [] [] [] [] ["using", expr l.prop]⟩) (λ ⟨s, hs⟩, begin
   induction [expr s] ["using", ident quotient.induction_on'] [] [],
   exact [expr ⟨⟨s, hs⟩, by simp [] [] [] [] [] []⟩]
 end)

instance fintype_nodup_nontrivial_cycle [Fintype α] : Fintype { s : Cycle α // s.nodup ∧ s.nontrivial } :=
  Fintype.subtype
    (((Finset.univ : Finset { s : Cycle α // s.nodup }).map (Function.Embedding.subtype _)).filter Cycle.Nontrivial)
    (by 
      simp )

/--
The `s : cycle α` as a `finset α`.
-/
def to_finset (s : Cycle α) : Finset α :=
  s.to_multiset.to_finset

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Given a `s : cycle α` such that `nodup s`, retrieve the next element after `x ∈ s`. -/
def next : ∀ (s : cycle α) (hs : nodup s) (x : α) (hx : «expr ∈ »(x, s)), α :=
λ
s, quot.hrec_on s (λ
 l
 hn
 x
 hx, next l x hx) (λ
 (l₁ l₂)
 (h : «expr ~r »(l₁, l₂)), function.hfunext (propext h.nodup_iff) (λ
  h₁
  h₂
  he, function.hfunext rfl (λ
   x
   y
   hxy, function.hfunext (propext (by simpa [] [] [] ["[", expr eq_of_heq hxy, "]"] [] ["using", expr h.mem_iff])) (λ
    hm
    hm'
    he', heq_of_eq (by simpa [] [] [] ["[", expr eq_of_heq hxy, "]"] [] ["using", expr is_rotated_next_eq h h₁ _])))))

-- error in Data.List.Cycle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Given a `s : cycle α` such that `nodup s`, retrieve the previous element before `x ∈ s`. -/
def prev : ∀ (s : cycle α) (hs : nodup s) (x : α) (hx : «expr ∈ »(x, s)), α :=
λ
s, quot.hrec_on s (λ
 l
 hn
 x
 hx, prev l x hx) (λ
 (l₁ l₂)
 (h : «expr ~r »(l₁, l₂)), function.hfunext (propext h.nodup_iff) (λ
  h₁
  h₂
  he, function.hfunext rfl (λ
   x
   y
   hxy, function.hfunext (propext (by simpa [] [] [] ["[", expr eq_of_heq hxy, "]"] [] ["using", expr h.mem_iff])) (λ
    hm
    hm'
    he', heq_of_eq (by simpa [] [] [] ["[", expr eq_of_heq hxy, "]"] [] ["using", expr is_rotated_prev_eq h h₁ _])))))

@[simp]
theorem prev_reverse_eq_next (s : Cycle α) (hs : nodup s) (x : α) (hx : x ∈ s) :
  s.reverse.prev (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.next hs x hx :=
  (Quotientₓ.induction_on' s prev_reverse_eq_next) hs x hx

@[simp]
theorem next_reverse_eq_prev (s : Cycle α) (hs : nodup s) (x : α) (hx : x ∈ s) :
  s.reverse.next (nodup_reverse_iff.mpr hs) x (mem_reverse_iff.mpr hx) = s.prev hs x hx :=
  by 
    simp [←prev_reverse_eq_next]

@[simp]
theorem next_mem (s : Cycle α) (hs : nodup s) (x : α) (hx : x ∈ s) : s.next hs x hx ∈ s :=
  by 
    induction s using Quot.induction_on 
    exact next_mem _ _ _

theorem prev_mem (s : Cycle α) (hs : nodup s) (x : α) (hx : x ∈ s) : s.prev hs x hx ∈ s :=
  by 
    rw [←next_reverse_eq_prev, ←mem_reverse_iff]
    exact next_mem _ _ _ _

@[simp]
theorem prev_next (s : Cycle α) (hs : nodup s) (x : α) (hx : x ∈ s) :
  s.prev hs (s.next hs x hx) (next_mem s hs x hx) = x :=
  (Quotientₓ.induction_on' s prev_next) hs x hx

@[simp]
theorem next_prev (s : Cycle α) (hs : nodup s) (x : α) (hx : x ∈ s) :
  s.next hs (s.prev hs x hx) (prev_mem s hs x hx) = x :=
  (Quotientₓ.induction_on' s next_prev) hs x hx

end Decidable

/--
We define a representation of concrete cycles, available when viewing them in a goal state or
via `#eval`, when over representatble types. For example, the cycle `(2 1 4 3)` will be shown
as `c[1, 4, 3, 2]`. The representation of the cycle sorts the elements by the string value of the
underlying element. This representation also supports cycles that can contain duplicates.
-/
instance  [HasRepr α] : HasRepr (Cycle α) :=
  ⟨fun s => "c[" ++ Stringₓ.intercalate ", " ((s.map reprₓ).lists.sort (· ≤ ·)).head ++ "]"⟩

end Cycle

