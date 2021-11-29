import Mathbin.Data.List.Join

/-!
# Permutations of a list

In this file we prove properties about `list.permutations`, a list of all permutations of a list. It
is defined in `data.list.defs`.

## Order of the permutations

Designed for performance, the order in which the permutations appear in `list.permutations` is
rather intricate and not very amenable to induction. That's why we also provide `list.permutations'`
as a less efficient but more straightforward way of listing permutations.

### `list.permutations`

TODO. In the meantime, you can try decrypting the docstrings.

### `list.permutations'`

The list of partitions is built by recursion. The permutations of `[]` are `[[]]`. Then, the
permutations of `a :: l` are obtained by taking all permutations of `l` in order and adding `a` in
all positions. Hence, to build `[0, 1, 2, 3].permutations'`, it does
* `[[]]`
* `[[3]]`
* `[[2, 3], [3, 2]]]`
* `[[1, 2, 3], [2, 1, 3], [2, 3, 1], [1, 3, 2], [3, 1, 2], [3, 2, 1]]`
* `[[0, 1, 2, 3], [1, 0, 2, 3], [1, 2, 0, 3], [1, 2, 3, 0],`
   `[0, 2, 1, 3], [2, 0, 1, 3], [2, 1, 0, 3], [2, 1, 3, 0],`
   `[0, 2, 3, 1], [2, 0, 3, 1], [2, 3, 0, 1], [2, 3, 1, 0],`
   `[0, 1, 3, 2], [1, 0, 3, 2], [1, 3, 0, 2], [1, 3, 2, 0],`
   `[0, 3, 1, 2], [3, 0, 1, 2], [3, 1, 0, 2], [3, 1, 2, 0],`
   `[0, 3, 2, 1], [3, 0, 2, 1], [3, 2, 0, 1], [3, 2, 1, 0]]`

## TODO

Show that `l.nodup → l.permutations.nodup`. See `data.fintype.list`.
-/


open Nat

variable{α β : Type _}

namespace List

theorem permutations_aux2_fst (t : α) (ts : List α) (r : List β) :
  ∀ (ys : List α) (f : List α → β), (permutations_aux2 t ts r ys f).1 = ys ++ ts
| [], f => rfl
| y :: ys, f =>
  match _, permutations_aux2_fst ys _ with 
  | ⟨_, zs⟩, rfl => rfl

@[simp]
theorem permutations_aux2_snd_nil (t : α) (ts : List α) (r : List β) (f : List α → β) :
  (permutations_aux2 t ts r [] f).2 = r :=
  rfl

-- error in Data.List.Permutation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp]
theorem permutations_aux2_snd_cons
(t : α)
(ts : list α)
(r : list β)
(y : α)
(ys : list α)
(f : list α → β) : «expr = »((permutations_aux2 t ts r «expr :: »(y, ys) f).2, «expr :: »(f «expr ++ »(«expr :: »(t, «expr :: »(y, ys)), ts), (permutations_aux2 t ts r ys (λ
    x : list α, f «expr :: »(y, x))).2)) :=
match _, permutations_aux2_fst t ts r _ _ : ∀
o : «expr × »(list α, list β), «expr = »(o.1, «expr ++ »(ys, ts)) → «expr = »((permutations_aux2._match_1 t y f o).2, «expr :: »(f «expr ++ »(«expr :: »(t, «expr :: »(y, ys)), ts), o.2)) with
| ⟨_, zs⟩, rfl := rfl end

/-- The `r` argument to `permutations_aux2` is the same as appending. -/
theorem permutations_aux2_append (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α → β) :
  (permutations_aux2 t ts nil ys f).2 ++ r = (permutations_aux2 t ts r ys f).2 :=
  by 
    induction ys generalizing f <;> simp 

/-- The `ts` argument to `permutations_aux2` can be folded into the `f` argument. -/
theorem permutations_aux2_comp_append {t : α} {ts ys : List α} {r : List β} (f : List α → β) :
  (permutations_aux2 t [] r ys$ fun x => f (x ++ ts)).2 = (permutations_aux2 t ts r ys f).2 :=
  by 
    induction ys generalizing f
    ·
      simp 
    ·
      simp [ys_ih fun xs => f (ys_hd :: xs)]

theorem map_permutations_aux2' {α β α' β'} (g : α → α') (g' : β → β') (t : α) (ts ys : List α) (r : List β)
  (f : List α → β) (f' : List α' → β') (H : ∀ a, g' (f a) = f' (map g a)) :
  map g' (permutations_aux2 t ts r ys f).2 = (permutations_aux2 (g t) (map g ts) (map g' r) (map g ys) f').2 :=
  by 
    induction ys generalizing f f' <;> simp 
    apply ys_ih 
    simp [H]

/-- The `f` argument to `permutations_aux2` when `r = []` can be eliminated. -/
theorem map_permutations_aux2 (t : α) (ts : List α) (ys : List α) (f : List α → β) :
  (permutations_aux2 t ts [] ys id).2.map f = (permutations_aux2 t ts [] ys f).2 :=
  by 
    convert map_permutations_aux2' id _ _ _ _ _ _ _ _ <;> simp only [map_id, id.def]
    exact fun _ => rfl

/-- An expository lemma to show how all of `ts`, `r`, and `f` can be eliminated from
`permutations_aux2`.

`(permutations_aux2 t [] [] ys id).2`, which appears on the RHS, is a list whose elements are
produced by inserting `t` into every non-terminal position of `ys` in order. As an example:
```lean
#eval permutations_aux2 1 [] [] [2, 3, 4] id
-- [[1, 2, 3, 4], [2, 1, 3, 4], [2, 3, 1, 4]]
```
-/
theorem permutations_aux2_snd_eq (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α → β) :
  (permutations_aux2 t ts r ys f).2 = ((permutations_aux2 t [] [] ys id).2.map fun x => f (x ++ ts)) ++ r :=
  by 
    rw [←permutations_aux2_append, map_permutations_aux2, permutations_aux2_comp_append]

theorem map_map_permutations_aux2 {α α'} (g : α → α') (t : α) (ts ys : List α) :
  map (map g) (permutations_aux2 t ts [] ys id).2 = (permutations_aux2 (g t) (map g ts) [] (map g ys) id).2 :=
  map_permutations_aux2' _ _ _ _ _ _ _ _ fun _ => rfl

theorem map_map_permutations'_aux (f : α → β) (t : α) (ts : List α) :
  map (map f) (permutations'_aux t ts) = permutations'_aux (f t) (map f ts) :=
  by 
    induction' ts with a ts ih <;> [rfl,
      ·
        simp [←ih]
        rfl]

-- error in Data.List.Permutation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem permutations'_aux_eq_permutations_aux2
(t : α)
(ts : list α) : «expr = »(permutations'_aux t ts, (permutations_aux2 t «expr[ , ]»([]) «expr[ , ]»([«expr ++ »(ts, «expr[ , ]»([t]))]) ts id).2) :=
begin
  induction [expr ts] [] ["with", ident a, ident ts, ident ih] [],
  { refl },
  simp [] [] [] ["[", expr permutations'_aux, ",", expr permutations_aux2_snd_cons, ",", expr ih, "]"] [] [],
  simp [] [] ["only"] ["[", "<-", expr permutations_aux2_append, "]"] [] [] { single_pass := tt },
  simp [] [] [] ["[", expr map_permutations_aux2, "]"] [] []
end

-- error in Data.List.Permutation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem mem_permutations_aux2
{t : α}
{ts : list α}
{ys : list α}
{l
 l' : list α} : «expr ↔ »(«expr ∈ »(l', (permutations_aux2 t ts «expr[ , ]»([]) ys (append l)).2), «expr∃ , »((l₁
   l₂), «expr ∧ »(«expr ≠ »(l₂, «expr[ , ]»([])), «expr ∧ »(«expr = »(ys, «expr ++ »(l₁, l₂)), «expr = »(l', «expr ++ »(«expr ++ »(«expr ++ »(l, l₁), «expr :: »(t, l₂)), ts)))))) :=
begin
  induction [expr ys] [] ["with", ident y, ident ys, ident ih] ["generalizing", ident l],
  { simp [] [] [] [] [] [] { contextual := tt } },
  rw ["[", expr permutations_aux2_snd_cons, ",", expr show «expr = »(λ
    x : list α, «expr ++ »(l, «expr :: »(y, x)), append «expr ++ »(l, «expr[ , ]»([y]))), by funext []; simp [] [] [] [] [] [], ",", expr mem_cons_iff, ",", expr ih, "]"] [],
  split,
  { rintro ["(", ident e, "|", "⟨", ident l₁, ",", ident l₂, ",", ident l0, ",", ident ye, ",", "_", "⟩", ")"],
    { subst [expr l'],
      exact [expr ⟨«expr[ , ]»([]), «expr :: »(y, ys), by simp [] [] [] [] [] []⟩] },
    { substs [ident l', ident ys],
      exact [expr ⟨«expr :: »(y, l₁), l₂, l0, by simp [] [] [] [] [] []⟩] } },
  { rintro ["⟨", "_", "|", "⟨", ident y', ",", ident l₁, "⟩", ",", ident l₂, ",", ident l0, ",", ident ye, ",", ident rfl, "⟩"],
    { simp [] [] [] ["[", expr ye, "]"] [] [] },
    { simp [] [] ["only"] ["[", expr cons_append, "]"] [] ["at", ident ye],
      rcases [expr ye, "with", "⟨", ident rfl, ",", ident rfl, "⟩"],
      exact [expr or.inr ⟨l₁, l₂, l0, by simp [] [] [] [] [] []⟩] } }
end

theorem mem_permutations_aux2' {t : α} {ts : List α} {ys : List α} {l : List α} :
  l ∈ (permutations_aux2 t ts [] ys id).2 ↔ ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l = l₁ ++ t :: l₂ ++ ts :=
  by 
    rw
        [show @id (List α) = append nil by 
          funext  <;> rfl] <;>
      apply mem_permutations_aux2

theorem length_permutations_aux2 (t : α) (ts : List α) (ys : List α) (f : List α → β) :
  length (permutations_aux2 t ts [] ys f).2 = length ys :=
  by 
    induction ys generalizing f <;> simp 

theorem foldr_permutations_aux2 (t : α) (ts : List α) (r L : List (List α)) :
  foldr (fun y r => (permutations_aux2 t ts r y id).2) r L =
    (L.bind fun y => (permutations_aux2 t ts [] y id).2) ++ r :=
  by 
    induction' L with l L ih <;> [rfl,
      ·
        simp [ih]
        rw [←permutations_aux2_append]]

theorem mem_foldr_permutations_aux2 {t : α} {ts : List α} {r L : List (List α)} {l' : List α} :
  l' ∈ foldr (fun y r => (permutations_aux2 t ts r y id).2) r L ↔
    l' ∈ r ∨ ∃ l₁ l₂, l₁ ++ l₂ ∈ L ∧ l₂ ≠ [] ∧ l' = l₁ ++ t :: l₂ ++ ts :=
  have  :
    (∃ a : List α, a ∈ L ∧ ∃ l₁ l₂ : List α, ¬l₂ = nil ∧ a = l₁ ++ l₂ ∧ l' = l₁ ++ t :: (l₂ ++ ts)) ↔
      ∃ l₁ l₂ : List α, ¬l₂ = nil ∧ l₁ ++ l₂ ∈ L ∧ l' = l₁ ++ t :: (l₂ ++ ts) :=
    ⟨fun ⟨a, aL, l₁, l₂, l0, e, h⟩ => ⟨l₁, l₂, l0, e ▸ aL, h⟩, fun ⟨l₁, l₂, l0, aL, h⟩ => ⟨_, aL, l₁, l₂, l0, rfl, h⟩⟩
  by 
    rw [foldr_permutations_aux2] <;>
      simp [mem_permutations_aux2', this, Or.comm, Or.left_comm, Or.assoc, And.comm, And.left_comm, And.assoc]

theorem length_foldr_permutations_aux2 (t : α) (ts : List α) (r L : List (List α)) :
  length (foldr (fun y r => (permutations_aux2 t ts r y id).2) r L) = Sum (map length L)+length r :=
  by 
    simp [foldr_permutations_aux2, · ∘ ·, length_permutations_aux2]

-- error in Data.List.Permutation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem length_foldr_permutations_aux2'
(t : α)
(ts : list α)
(r L : list (list α))
(n)
(H : ∀
 l «expr ∈ » L, «expr = »(length l, n)) : «expr = »(length (foldr (λ
   y r, (permutations_aux2 t ts r y id).2) r L), «expr + »(«expr * »(n, length L), length r)) :=
begin
  rw ["[", expr length_foldr_permutations_aux2, ",", expr (_ : «expr = »(sum (map length L), «expr * »(n, length L))), "]"] [],
  induction [expr L] [] ["with", ident l, ident L, ident ih] [],
  { simp [] [] [] [] [] [] },
  have [ident sum_map] [":", expr «expr = »(sum (map length L), «expr * »(n, length L))] [":=", expr ih (λ
    l m, H l (mem_cons_of_mem _ m))],
  have [ident length_l] [":", expr «expr = »(length l, n)] [":=", expr H _ (mem_cons_self _ _)],
  simp [] [] [] ["[", expr sum_map, ",", expr length_l, ",", expr mul_add, ",", expr add_comm, "]"] [] []
end

@[simp]
theorem permutations_aux_nil (is : List α) : permutations_aux [] is = [] :=
  by 
    rw [permutations_aux, permutations_aux.rec]

@[simp]
theorem permutations_aux_cons (t : α) (ts is : List α) :
  permutations_aux (t :: ts) is =
    foldr (fun y r => (permutations_aux2 t ts r y id).2) (permutations_aux ts (t :: is)) (permutations is) :=
  by 
    rw [permutations_aux, permutations_aux.rec] <;> rfl

@[simp]
theorem permutations_nil : permutations ([] : List α) = [[]] :=
  by 
    rw [permutations, permutations_aux_nil]

-- error in Data.List.Permutation: ././Mathport/Syntax/Translate/Basic.lean:179:15: failed to format: format: uncaught backtrack exception
theorem map_permutations_aux
(f : α → β) : ∀
ts is : list α, «expr = »(map (map f) (permutations_aux ts is), permutations_aux (map f ts) (map f is)) :=
begin
  refine [expr permutations_aux.rec (by simp [] [] [] [] [] []) _],
  introv [ident IH1, ident IH2],
  rw [expr map] ["at", ident IH2],
  simp [] [] ["only"] ["[", expr foldr_permutations_aux2, ",", expr map_append, ",", expr map, ",", expr map_map_permutations_aux2, ",", expr permutations, ",", expr bind_map, ",", expr IH1, ",", expr append_assoc, ",", expr permutations_aux_cons, ",", expr cons_bind, ",", "<-", expr IH2, ",", expr map_bind, "]"] [] []
end

theorem map_permutations (f : α → β) (ts : List α) : map (map f) (permutations ts) = permutations (map f ts) :=
  by 
    rw [permutations, permutations, map, map_permutations_aux, map]

theorem map_permutations' (f : α → β) (ts : List α) : map (map f) (permutations' ts) = permutations' (map f ts) :=
  by 
    induction' ts with t ts ih <;> [rfl, simp [←ih, map_bind, ←map_map_permutations'_aux, bind_map]]

-- error in Data.List.Permutation: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem permutations_aux_append
(is
 is'
 ts : list α) : «expr = »(permutations_aux «expr ++ »(is, ts) is', «expr ++ »((permutations_aux is is').map ((«expr ++ » ts)), permutations_aux ts «expr ++ »(is.reverse, is'))) :=
begin
  induction [expr is] [] ["with", ident t, ident is, ident ih] ["generalizing", ident is'],
  { simp [] [] [] [] [] [] },
  simp [] [] [] ["[", expr foldr_permutations_aux2, ",", expr ih, ",", expr bind_map, "]"] [] [],
  congr' [2] [],
  funext [ident ys],
  rw ["[", expr map_permutations_aux2, "]"] [],
  simp [] [] ["only"] ["[", "<-", expr permutations_aux2_comp_append, "]"] [] [] { single_pass := tt },
  simp [] [] ["only"] ["[", expr id, ",", expr append_assoc, "]"] [] []
end

theorem permutations_append (is ts : List α) :
  permutations (is ++ ts) = (permutations is).map (· ++ ts) ++ permutations_aux ts is.reverse :=
  by 
    simp [permutations, permutations_aux_append]

end List

