import Mathbin.Data.List.Perm

/-!
# Sorting algorithms on lists

In this file we define `list.sorted r l` to be an alias for `pairwise r l`. This alias is preferred
in the case that `r` is a `<` or `≤`-like relation. Then we define two sorting algorithms:
`list.insertion_sort` and `list.merge_sort`, and prove their correctness.
-/


open List.Perm

universe uu

namespace List

/-!
### The predicate `list.sorted`
-/


section Sorted

variable{α : Type uu}{r : α → α → Prop}

/-- `sorted r l` is the same as `pairwise r l`, preferred in the case that `r`
  is a `<` or `≤`-like relation (transitive and antisymmetric or asymmetric) -/
def sorted :=
  @Pairwise

instance decidable_sorted [DecidableRel r] (l : List α) : Decidable (sorted r l) :=
  List.decidablePairwiseₓ _

@[simp]
theorem sorted_nil : sorted r [] :=
  pairwise.nil

theorem sorted_of_sorted_cons {a : α} {l : List α} : sorted r (a :: l) → sorted r l :=
  pairwise_of_pairwise_cons

theorem sorted.tail {r : α → α → Prop} {l : List α} (h : sorted r l) : sorted r l.tail :=
  h.tail

theorem rel_of_sorted_cons {a : α} {l : List α} : sorted r (a :: l) → ∀ b (_ : b ∈ l), r a b :=
  rel_of_pairwise_cons

@[simp]
theorem sorted_cons {a : α} {l : List α} : sorted r (a :: l) ↔ (∀ b (_ : b ∈ l), r a b) ∧ sorted r l :=
  pairwise_cons

protected theorem sorted.nodup {r : α → α → Prop} [IsIrrefl α r] {l : List α} (h : sorted r l) : nodup l :=
  h.nodup

-- error in Data.List.Sort: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_of_perm_of_sorted
[is_antisymm α r]
{l₁ l₂ : list α}
(p : «expr ~ »(l₁, l₂))
(s₁ : sorted r l₁)
(s₂ : sorted r l₂) : «expr = »(l₁, l₂) :=
begin
  induction [expr s₁] [] ["with", ident a, ident l₁, ident h₁, ident s₁, ident IH] ["generalizing", ident l₂],
  { exact [expr p.nil_eq] },
  { have [] [":", expr «expr ∈ »(a, l₂)] [":=", expr p.subset (mem_cons_self _ _)],
    rcases [expr mem_split this, "with", "⟨", ident u₂, ",", ident v₂, ",", ident rfl, "⟩"],
    have [ident p'] [] [":=", expr (perm_cons a).1 (p.trans perm_middle)],
    have [] [] [":=", expr IH p' (pairwise_of_sublist (by simp [] [] [] [] [] []) s₂)],
    subst [expr l₁],
    change [expr «expr = »(«expr ++ »(«expr :: »(a, u₂), v₂), «expr ++ »(u₂, «expr ++ »(«expr[ , ]»([a]), v₂)))] [] [],
    rw ["<-", expr append_assoc] [],
    congr,
    have [] [":", expr ∀
     (x : α)
     (h : «expr ∈ »(x, u₂)), «expr = »(x, a)] [":=", expr λ
     x
     m, antisymm ((pairwise_append.1 s₂).2.2 _ m a (mem_cons_self _ _)) (h₁ _ (by simp [] [] [] ["[", expr m, "]"] [] []))],
    rw ["[", expr (@eq_repeat _ a «expr + »(length u₂, 1) «expr :: »(a, u₂)).2, ",", expr (@eq_repeat _ a «expr + »(length u₂, 1) «expr ++ »(u₂, «expr[ , ]»([a]))).2, "]"] []; split; simp [] [] [] ["[", expr iff_true_intro this, ",", expr or_comm, "]"] [] [] }
end

@[simp]
theorem sorted_singleton (a : α) : sorted r [a] :=
  pairwise_singleton _ _

theorem sorted.rel_nth_le_of_lt {l : List α} (h : l.sorted r) {a b : ℕ} (ha : a < l.length) (hb : b < l.length)
  (hab : a < b) : r (l.nth_le a ha) (l.nth_le b hb) :=
  List.pairwise_iff_nth_le.1 h a b hb hab

theorem sorted.rel_nth_le_of_le [IsRefl α r] {l : List α} (h : l.sorted r) {a b : ℕ} (ha : a < l.length)
  (hb : b < l.length) (hab : a ≤ b) : r (l.nth_le a ha) (l.nth_le b hb) :=
  by 
    cases' eq_or_lt_of_le hab with H H
    ·
      subst H 
      exact refl _
    ·
      exact h.rel_nth_le_of_lt _ _ H

theorem sorted.rel_of_mem_take_of_mem_drop {l : List α} (h : List.Sorted r l) {k : ℕ} {x y : α}
  (hx : x ∈ List.takeₓ k l) (hy : y ∈ List.dropₓ k l) : r x y :=
  by 
    obtain ⟨iy, hiy, rfl⟩ := nth_le_of_mem hy 
    obtain ⟨ix, hix, rfl⟩ := nth_le_of_mem hx 
    rw [nth_le_take', nth_le_drop']
    rw [length_take] at hix 
    exact h.rel_nth_le_of_lt _ _ (ix.lt_add_right _ _ (lt_min_iff.mp hix).left)

end Sorted

section Sort

variable{α : Type uu}(r : α → α → Prop)[DecidableRel r]

local infixl:50 " ≼ " => r

/-! ### Insertion sort -/


section InsertionSort

/-- `ordered_insert a l` inserts `a` into `l` at such that
  `ordered_insert a l` is sorted if `l` is. -/
@[simp]
def ordered_insert (a : α) : List α → List α
| [] => [a]
| b :: l => if a ≼ b then a :: b :: l else b :: ordered_insert l

/-- `insertion_sort l` returns `l` sorted using the insertion sort algorithm. -/
@[simp]
def insertion_sort : List α → List α
| [] => []
| b :: l => ordered_insert r b (insertion_sort l)

@[simp]
theorem ordered_insert_nil (a : α) : [].orderedInsert r a = [a] :=
  rfl

theorem ordered_insert_length : ∀ (L : List α) (a : α), (L.ordered_insert r a).length = L.length+1
| [], a => rfl
| hd :: tl, a =>
  by 
    dsimp [ordered_insert]
    splitIfs <;> simp [ordered_insert_length]

/-- An alternative definition of `ordered_insert` using `take_while` and `drop_while`. -/
theorem ordered_insert_eq_take_drop (a : α) :
  ∀ (l : List α), l.ordered_insert r a = (l.take_while fun b => ¬a ≼ b) ++ a :: l.drop_while fun b => ¬a ≼ b
| [] => rfl
| b :: l =>
  by 
    dsimp only [ordered_insert]
    splitIfs <;> simp [take_while, drop_while]

theorem insertion_sort_cons_eq_take_drop (a : α) (l : List α) :
  insertion_sort r (a :: l) =
    ((insertion_sort r l).takeWhile fun b => ¬a ≼ b) ++ a :: (insertion_sort r l).dropWhile fun b => ¬a ≼ b :=
  ordered_insert_eq_take_drop r a _

section Correctness

open Perm

theorem perm_ordered_insert a : ∀ (l : List α), ordered_insert r a l ~ a :: l
| [] => perm.refl _
| b :: l =>
  by 
    byCases' a ≼ b <;> [simp [ordered_insert, h],
      simpa [ordered_insert, h] using ((perm_ordered_insert l).cons _).trans (perm.swap _ _ _)]

theorem ordered_insert_count [DecidableEq α] (L : List α) (a b : α) :
  count a (L.ordered_insert r b) = count a L+if a = b then 1 else 0 :=
  by 
    rw [(L.perm_ordered_insert r b).count_eq, count_cons]
    splitIfs <;> simp only [Nat.succ_eq_add_one, add_zeroₓ]

theorem perm_insertion_sort : ∀ (l : List α), insertion_sort r l ~ l
| [] => perm.nil
| b :: l =>
  by 
    simpa [insertion_sort] using (perm_ordered_insert _ _ _).trans ((perm_insertion_sort l).cons b)

variable{r}

/-- If `l` is already `list.sorted` with respect to `r`, then `insertion_sort` does not change
it. -/
theorem sorted.insertion_sort_eq : ∀ {l : List α} (h : sorted r l), insertion_sort r l = l
| [], _ => rfl
| [a], _ => rfl
| a :: b :: l, h =>
  by 
    rw [insertion_sort, sorted.insertion_sort_eq, ordered_insert, if_pos]
    exacts[rel_of_sorted_cons h _ (Or.inl rfl), h.tail]

section TotalAndTransitive

variable[IsTotal α r][IsTrans α r]

theorem sorted.ordered_insert (a : α) : ∀ l, sorted r l → sorted r (ordered_insert r a l)
| [], h => sorted_singleton a
| b :: l, h =>
  by 
    byCases' h' : a ≼ b
    ·
      simpa [ordered_insert, h', h] using fun b' bm => trans h' (rel_of_sorted_cons h _ bm)
    ·
      suffices  : ∀ (b' : α), b' ∈ ordered_insert r a l → r b b'
      ·
        simpa [ordered_insert, h', (sorted_of_sorted_cons h).orderedInsert l]
      intro b' bm 
      cases'
        show b' = a ∨ b' ∈ l by 
          simpa using (perm_ordered_insert _ _ _).Subset bm with
        be bm
      ·
        subst b' 
        exact (total_of r _ _).resolve_left h'
      ·
        exact rel_of_sorted_cons h _ bm

variable(r)

/-- The list `list.insertion_sort r l` is `list.sorted` with respect to `r`. -/
theorem sorted_insertion_sort : ∀ l, sorted r (insertion_sort r l)
| [] => sorted_nil
| a :: l => (sorted_insertion_sort l).orderedInsert a _

end TotalAndTransitive

end Correctness

end InsertionSort

/-! ### Merge sort -/


section MergeSort

/-- Split `l` into two lists of approximately equal length.

     split [1, 2, 3, 4, 5] = ([1, 3, 5], [2, 4]) -/
@[simp]
def split : List α → List α × List α
| [] => ([], [])
| a :: l =>
  let (l₁, l₂) := split l
  (a :: l₂, l₁)

theorem split_cons_of_eq (a : α) {l l₁ l₂ : List α} (h : split l = (l₁, l₂)) : split (a :: l) = (a :: l₂, l₁) :=
  by 
    rw [split, h] <;> rfl

theorem length_split_le : ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → length l₁ ≤ length l ∧ length l₂ ≤ length l
| [], _, _, rfl => ⟨Nat.le_reflₓ 0, Nat.le_reflₓ 0⟩
| a :: l, l₁', l₂', h =>
  by 
    cases' e : split l with l₁ l₂ 
    injection (split_cons_of_eq _ e).symm.trans h 
    substs l₁' l₂' 
    cases' length_split_le e with h₁ h₂ 
    exact ⟨Nat.succ_le_succₓ h₂, Nat.le_succ_of_leₓ h₁⟩

theorem length_split_lt {a b} {l l₁ l₂ : List α} (h : split (a :: b :: l) = (l₁, l₂)) :
  length l₁ < length (a :: b :: l) ∧ length l₂ < length (a :: b :: l) :=
  by 
    cases' e : split l with l₁' l₂' 
    injection (split_cons_of_eq _ (split_cons_of_eq _ e)).symm.trans h 
    substs l₁ l₂ 
    cases' length_split_le e with h₁ h₂ 
    exact ⟨Nat.succ_le_succₓ (Nat.succ_le_succₓ h₁), Nat.succ_le_succₓ (Nat.succ_le_succₓ h₂)⟩

theorem perm_split : ∀ {l l₁ l₂ : List α}, split l = (l₁, l₂) → l ~ l₁ ++ l₂
| [], _, _, rfl => perm.refl _
| a :: l, l₁', l₂', h =>
  by 
    cases' e : split l with l₁ l₂ 
    injection (split_cons_of_eq _ e).symm.trans h 
    substs l₁' l₂' 
    exact ((perm_split e).trans perm_append_comm).cons a

/-- Merge two sorted lists into one in linear time.

     merge [1, 2, 4, 5] [0, 1, 3, 4] = [0, 1, 1, 2, 3, 4, 4, 5] -/
def merge : List α → List α → List α
| [], l' => l'
| l, [] => l
| a :: l, b :: l' => if a ≼ b then a :: merge l (b :: l') else b :: merge (a :: l) l'

include r

/-- Implementation of a merge sort algorithm to sort a list. -/
def merge_sort : List α → List α
| [] => []
| [a] => [a]
| a :: b :: l =>
  by 
    cases' e : split (a :: b :: l) with l₁ l₂ 
    cases' length_split_lt e with h₁ h₂ 
    exact merge r (merge_sort l₁) (merge_sort l₂)

-- error in Data.List.Sort: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem merge_sort_cons_cons
{a b}
{l l₁ l₂ : list α}
(h : «expr = »(split «expr :: »(a, «expr :: »(b, l)), (l₁, l₂))) : «expr = »(merge_sort r «expr :: »(a, «expr :: »(b, l)), merge r (merge_sort r l₁) (merge_sort r l₂)) :=
begin
  suffices [] [":", expr ∀
   (L : list α)
   (h1), «expr = »(@@and.rec (λ
     (a a)
     (_ : «expr ∧ »(«expr < »(length l₁, «expr + »(«expr + »(length l, 1), 1)), «expr < »(length l₂, «expr + »(«expr + »(length l, 1), 1)))), L) h1 h1, L)],
  { simp [] [] [] ["[", expr merge_sort, ",", expr h, "]"] [] [],
    apply [expr this] },
  intros [],
  cases [expr h1] [],
  refl
end

section Correctness

theorem perm_merge : ∀ (l l' : List α), merge r l l' ~ l ++ l'
| [], [] =>
  by 
    simp [merge]
| [], b :: l' =>
  by 
    simp [merge]
| a :: l, [] =>
  by 
    simp [merge]
| a :: l, b :: l' =>
  by 
    byCases' a ≼ b
    ·
      simpa [merge, h] using perm_merge _ _
    ·
      suffices  : b :: merge r (a :: l) l' ~ a :: (l ++ b :: l')
      ·
        simpa [merge, h]
      exact ((perm_merge _ _).cons _).trans ((swap _ _ _).trans (perm_middle.symm.cons _))

theorem perm_merge_sort : ∀ (l : List α), merge_sort r l ~ l
| [] =>
  by 
    simp [merge_sort]
| [a] =>
  by 
    simp [merge_sort]
| a :: b :: l =>
  by 
    cases' e : split (a :: b :: l) with l₁ l₂ 
    cases' length_split_lt e with h₁ h₂ 
    rw [merge_sort_cons_cons r e]
    apply (perm_merge r _ _).trans 
    exact ((perm_merge_sort l₁).append (perm_merge_sort l₂)).trans (perm_split e).symm

@[simp]
theorem length_merge_sort (l : List α) : (merge_sort r l).length = l.length :=
  (perm_merge_sort r _).length_eq

section TotalAndTransitive

variable{r}[IsTotal α r][IsTrans α r]

-- error in Data.List.Sort: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sorted.merge : ∀ {l l' : list α}, sorted r l → sorted r l' → sorted r (merge r l l')
| «expr[ , ]»([]), «expr[ , ]»([]), h₁, h₂ := by simp [] [] [] ["[", expr merge, "]"] [] []
| «expr[ , ]»([]), «expr :: »(b, l'), h₁, h₂ := by simpa [] [] [] ["[", expr merge, "]"] [] ["using", expr h₂]
| «expr :: »(a, l), «expr[ , ]»([]), h₁, h₂ := by simpa [] [] [] ["[", expr merge, "]"] [] ["using", expr h₁]
| «expr :: »(a, l), «expr :: »(b, l'), h₁, h₂ := begin
  by_cases [expr «expr ≼ »(a, b)],
  { suffices [] [":", expr ∀ (b' : α) (_ : «expr ∈ »(b', merge r l «expr :: »(b, l'))), r a b'],
    { simpa [] [] [] ["[", expr merge, ",", expr h, ",", expr (sorted_of_sorted_cons h₁).merge h₂, "]"] [] [] },
    intros [ident b', ident bm],
    rcases [expr show «expr ∨ »(«expr = »(b', b), «expr ∨ »(«expr ∈ »(b', l), «expr ∈ »(b', l'))), by simpa [] [] [] ["[", expr or.left_comm, "]"] [] ["using", expr (perm_merge _ _ _).subset bm], "with", ident be, "|", ident bl, "|", ident bl'],
    { subst [expr b'],
      assumption },
    { exact [expr rel_of_sorted_cons h₁ _ bl] },
    { exact [expr trans h (rel_of_sorted_cons h₂ _ bl')] } },
  { suffices [] [":", expr ∀ (b' : α) (_ : «expr ∈ »(b', merge r «expr :: »(a, l) l')), r b b'],
    { simpa [] [] [] ["[", expr merge, ",", expr h, ",", expr h₁.merge (sorted_of_sorted_cons h₂), "]"] [] [] },
    intros [ident b', ident bm],
    have [ident ba] [":", expr «expr ≼ »(b, a)] [":=", expr (total_of r _ _).resolve_left h],
    rcases [expr show «expr ∨ »(«expr = »(b', a), «expr ∨ »(«expr ∈ »(b', l), «expr ∈ »(b', l'))), by simpa [] [] [] [] [] ["using", expr (perm_merge _ _ _).subset bm], "with", ident be, "|", ident bl, "|", ident bl'],
    { subst [expr b'],
      assumption },
    { exact [expr trans ba (rel_of_sorted_cons h₁ _ bl)] },
    { exact [expr rel_of_sorted_cons h₂ _ bl'] } }
end

variable(r)

theorem sorted_merge_sort : ∀ (l : List α), sorted r (merge_sort r l)
| [] =>
  by 
    simp [merge_sort]
| [a] =>
  by 
    simp [merge_sort]
| a :: b :: l =>
  by 
    cases' e : split (a :: b :: l) with l₁ l₂ 
    cases' length_split_lt e with h₁ h₂ 
    rw [merge_sort_cons_cons r e]
    exact (sorted_merge_sort l₁).merge (sorted_merge_sort l₂)

theorem merge_sort_eq_self [IsAntisymm α r] {l : List α} : sorted r l → merge_sort r l = l :=
  eq_of_perm_of_sorted (perm_merge_sort _ _) (sorted_merge_sort _ _)

theorem merge_sort_eq_insertion_sort [IsAntisymm α r] (l : List α) : merge_sort r l = insertion_sort r l :=
  eq_of_perm_of_sorted ((perm_merge_sort r l).trans (perm_insertion_sort r l).symm) (sorted_merge_sort r l)
    (sorted_insertion_sort r l)

end TotalAndTransitive

end Correctness

end MergeSort

end Sort

end List

