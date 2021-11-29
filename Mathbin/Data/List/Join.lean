import Mathbin.Data.List.BigOperators

/-!
# Join of a list of lists

This file proves basic properties of `list.join`, which concatenates a list of lists. It is defined
in [`data.list.defs`](./data/list/defs).
-/


variable{α β : Type _}

namespace List

attribute [simp] join

@[simp]
theorem join_nil : [([] : List α)].join = [] :=
  rfl

@[simp]
theorem join_eq_nil : ∀ {L : List (List α)}, join L = [] ↔ ∀ l (_ : l ∈ L), l = []
| [] => iff_of_true rfl (forall_mem_nil _)
| l :: L =>
  by 
    simp only [join, append_eq_nil, join_eq_nil, forall_mem_cons]

@[simp]
theorem join_append (L₁ L₂ : List (List α)) : join (L₁ ++ L₂) = join L₁ ++ join L₂ :=
  by 
    induction L₁ <;> [rfl, simp only [join, cons_append, append_assoc]]

-- error in Data.List.Join: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem join_filter_empty_eq_ff
[decidable_pred (λ
  l : list α, «expr = »(l.empty, ff))] : ∀
{L : list (list α)}, «expr = »(join (L.filter (λ l, «expr = »(l.empty, ff))), L.join)
| «expr[ , ]»([]) := rfl
| «expr :: »(«expr[ , ]»([]), L) := by simp [] [] [] ["[", expr @join_filter_empty_eq_ff L, "]"] [] []
| «expr :: »(«expr :: »(a, l), L) := by simp [] [] [] ["[", expr @join_filter_empty_eq_ff L, "]"] [] []

-- error in Data.List.Join: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem join_filter_ne_nil
[decidable_pred (λ l : list α, «expr ≠ »(l, «expr[ , ]»([])))]
{L : list (list α)} : «expr = »(join (L.filter (λ l, «expr ≠ »(l, «expr[ , ]»([])))), L.join) :=
by simp [] [] [] ["[", expr join_filter_empty_eq_ff, ",", "<-", expr empty_iff_eq_nil, "]"] [] []

theorem join_join (l : List (List (List α))) : l.join.join = (l.map join).join :=
  by 
    induction l 
    simp 
    simp [l_ih]

@[simp]
theorem length_join (L : List (List α)) : length (join L) = Sum (map length L) :=
  by 
    induction L <;> [rfl, simp only [join, map, sum_cons, length_append]]

@[simp]
theorem length_bind (l : List α) (f : α → List β) : length (List.bind l f) = Sum (map (length ∘ f) l) :=
  by 
    rw [List.bind, length_join, map_map]

/-- In a join, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join of the first `i` sublists. -/
theorem take_sum_join (L : List (List α)) (i : ℕ) : L.join.take ((L.map length).take i).Sum = (L.take i).join :=
  by 
    induction L generalizing i
    ·
      simp 
    cases i
    ·
      simp 
    simp [take_append, L_ih]

/-- In a join, dropping all the elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join after dropping the first `i` sublists. -/
theorem drop_sum_join (L : List (List α)) (i : ℕ) : L.join.drop ((L.map length).take i).Sum = (L.drop i).join :=
  by 
    induction L generalizing i
    ·
      simp 
    cases i
    ·
      simp 
    simp [drop_append, L_ih]

-- error in Data.List.Join: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
theorem drop_take_succ_eq_cons_nth_le
(L : list α)
{i : exprℕ()}
(hi : «expr < »(i, L.length)) : «expr = »((L.take «expr + »(i, 1)).drop i, «expr[ , ]»([nth_le L i hi])) :=
begin
  induction [expr L] [] [] ["generalizing", ident i],
  { simp [] [] ["only"] ["[", expr length, "]"] [] ["at", ident hi],
    exact [expr (nat.not_succ_le_zero i hi).elim] },
  cases [expr i] [],
  { simp [] [] [] [] [] [] },
  have [] [":", expr «expr < »(i, L_tl.length)] [],
  { simp [] [] [] [] [] ["at", ident hi],
    exact [expr nat.lt_of_succ_lt_succ hi] },
  simp [] [] [] ["[", expr L_ih this, "]"] [] [],
  refl
end

-- error in Data.List.Join: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a join of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lenghts of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`. -/
theorem drop_take_succ_join_eq_nth_le
(L : list (list α))
{i : exprℕ()}
(hi : «expr < »(i, L.length)) : «expr = »((L.join.take ((L.map length).take «expr + »(i, 1)).sum).drop ((L.map length).take i).sum, nth_le L i hi) :=
begin
  have [] [":", expr «expr = »((L.map length).take i, ((L.take «expr + »(i, 1)).map length).take i)] [],
  by simp [] [] [] ["[", expr map_take, ",", expr take_take, "]"] [] [],
  simp [] [] [] ["[", expr take_sum_join, ",", expr this, ",", expr drop_sum_join, ",", expr drop_take_succ_eq_cons_nth_le _ hi, "]"] [] []
end

/-- Auxiliary lemma to control elements in a join. -/
theorem sum_take_map_length_lt1 (L : List (List α)) {i j : ℕ} (hi : i < L.length) (hj : j < (nth_le L i hi).length) :
  (((L.map length).take i).Sum+j) < ((L.map length).take (i+1)).Sum :=
  by 
    simp [hi, sum_take_succ, hj]

-- error in Data.List.Join: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Auxiliary lemma to control elements in a join. -/
theorem sum_take_map_length_lt2
(L : list (list α))
{i j : exprℕ()}
(hi : «expr < »(i, L.length))
(hj : «expr < »(j, (nth_le L i hi).length)) : «expr < »(«expr + »(((L.map length).take i).sum, j), L.join.length) :=
begin
  convert [] [expr lt_of_lt_of_le (sum_take_map_length_lt1 L hi hj) (monotone_sum_take _ hi)] [],
  have [] [":", expr «expr = »(L.length, (L.map length).length)] [],
  by simp [] [] [] [] [] [],
  simp [] [] [] ["[", expr this, ",", "-", ident length_map, "]"] [] []
end

/-- The `n`-th element in a join of sublists is the `j`-th element of the `i`th sublist,
where `n` can be obtained in terms of `i` and `j` by adding the lengths of all the sublists
of index `< i`, and adding `j`. -/
theorem nth_le_join (L : List (List α)) {i j : ℕ} (hi : i < L.length) (hj : j < (nth_le L i hi).length) :
  nth_le L.join (((L.map length).take i).Sum+j) (sum_take_map_length_lt2 L hi hj) = nth_le (nth_le L i hi) j hj :=
  by 
    rw [nth_le_take L.join (sum_take_map_length_lt2 L hi hj) (sum_take_map_length_lt1 L hi hj), nth_le_drop,
      nth_le_of_eq (drop_take_succ_join_eq_nth_le L hi)]

-- error in Data.List.Join: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Two lists of sublists are equal iff their joins coincide, as well as the lengths of the
sublists. -/
theorem eq_iff_join_eq
(L
 L' : list (list α)) : «expr ↔ »(«expr = »(L, L'), «expr ∧ »(«expr = »(L.join, L'.join), «expr = »(map length L, map length L'))) :=
begin
  refine [expr ⟨λ H, by simp [] [] [] ["[", expr H, "]"] [] [], _⟩],
  rintros ["⟨", ident join_eq, ",", ident length_eq, "⟩"],
  apply [expr ext_le],
  { have [] [":", expr «expr = »(length (map length L), length (map length L'))] [],
    by rw [expr length_eq] [],
    simpa [] [] [] [] [] ["using", expr this] },
  { assume [binders (n h₁ h₂)],
    rw ["[", "<-", expr drop_take_succ_join_eq_nth_le, ",", "<-", expr drop_take_succ_join_eq_nth_le, ",", expr join_eq, ",", expr length_eq, "]"] [] }
end

end List

