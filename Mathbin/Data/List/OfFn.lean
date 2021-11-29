import Mathbin.Data.Fin.Basic 
import Mathbin.Data.List.Basic

/-!
# Lists from functions

Theorems and lemmas for dealing with `list.of_fn`, which converts a function on `fin n` to a list
of length `n`.

## Main Definitions

The main definitions pertain to lists generated using `of_fn`

- `list.length_of_fn`, which tells us the length of such a list
- `list.nth_of_fn`, which tells us the nth element of such a list
- `list.array_eq_of_fn`, which interprets the list form of an array as such a list.
-/


universe u

variable{α : Type u}

open Nat

namespace List

theorem length_of_fn_aux {n} (f : Finₓ n → α) : ∀ m h l, length (of_fn_aux f m h l) = length l+m
| 0, h, l => rfl
| succ m, h, l => (length_of_fn_aux m _ _).trans (succ_add _ _)

/-- The length of a list converted from a function is the size of the domain. -/
@[simp]
theorem length_of_fn {n} (f : Finₓ n → α) : length (of_fn f) = n :=
  (length_of_fn_aux f _ _ _).trans (zero_addₓ _)

theorem nth_of_fn_aux {n} (f : Finₓ n → α) i :
  ∀ m h l, (∀ i, nth l i = of_fn_nth_val f (i+m)) → nth (of_fn_aux f m h l) i = of_fn_nth_val f i
| 0, h, l, H => H i
| succ m, h, l, H =>
  nth_of_fn_aux m _ _
    (by 
      intro j 
      cases' j with j
      ·
        simp only [nth, of_fn_nth_val, zero_addₓ, dif_pos (show m < n from h)]
      ·
        simp only [nth, H, add_succ, succ_add])

/-- The `n`th element of a list -/
@[simp]
theorem nth_of_fn {n} (f : Finₓ n → α) i : nth (of_fn f) i = of_fn_nth_val f i :=
  nth_of_fn_aux f _ _ _ _$
    fun i =>
      by 
        simp only [of_fn_nth_val, dif_neg (not_ltₓ.2 (Nat.le_add_leftₓ n i))] <;> rfl

theorem nth_le_of_fn {n} (f : Finₓ n → α) (i : Finₓ n) : nth_le (of_fn f) i ((length_of_fn f).symm ▸ i.2) = f i :=
  Option.some.injₓ$
    by 
      rw [←nth_le_nth] <;> simp only [List.nth_of_fn, of_fn_nth_val, Finₓ.eta, dif_pos i.is_lt]

@[simp]
theorem nth_le_of_fn' {n} (f : Finₓ n → α) {i : ℕ} (h : i < (of_fn f).length) :
  nth_le (of_fn f) i h = f ⟨i, length_of_fn f ▸ h⟩ :=
  nth_le_of_fn f ⟨i, length_of_fn f ▸ h⟩

@[simp]
theorem map_of_fn {β : Type _} {n : ℕ} (f : Finₓ n → α) (g : α → β) : map g (of_fn f) = of_fn (g ∘ f) :=
  ext_le
    (by 
      simp )
    fun i h h' =>
      by 
        simp 

/-- Arrays converted to lists are the same as `of_fn` on the indexing function of the array. -/
theorem array_eq_of_fn {n} (a : Arrayₓ n α) : a.to_list = of_fn a.read :=
  suffices ∀ {m h l}, DArray.revIterateAux a (fun i => cons) m h l = of_fn_aux (DArray.read a) m h l from this 
  by 
    intros 
    induction' m with m IH generalizing l
    ·
      rfl 
    simp only [DArray.revIterateAux, of_fn_aux, IH]

/-- `of_fn` on an empty domain is the empty list. -/
@[simp]
theorem of_fn_zero (f : Finₓ 0 → α) : of_fn f = [] :=
  rfl

@[simp]
theorem of_fn_succ {n} (f : Finₓ (succ n) → α) : of_fn f = f 0 :: of_fn fun i => f i.succ :=
  suffices ∀ {m h l}, of_fn_aux f (succ m) (succ_le_succ h) l = f 0 :: of_fn_aux (fun i => f i.succ) m h l from this 
  by 
    intros 
    induction' m with m IH generalizing l
    ·
      rfl 
    rw [of_fn_aux, IH]
    rfl

theorem of_fn_nth_le : ∀ (l : List α), (of_fn fun i => nth_le l i i.2) = l
| [] => rfl
| a :: l =>
  by 
    rw [of_fn_succ]
    congr 
    simp only [Finₓ.coe_succ]
    exact of_fn_nth_le l

theorem mem_of_fn {n} (f : Finₓ n → α) (a : α) : a ∈ of_fn f ↔ a ∈ Set.Range f :=
  by 
    simp only [mem_iff_nth_le, Set.mem_range, nth_le_of_fn']
    exact
      ⟨fun ⟨i, hi, h⟩ => ⟨_, h⟩,
        fun ⟨i, hi⟩ =>
          ⟨i.1, (length_of_fn f).symm ▸ i.2,
            by 
              simpa using hi⟩⟩

@[simp]
theorem forall_mem_of_fn_iff {n : ℕ} {f : Finₓ n → α} {P : α → Prop} :
  (∀ i (_ : i ∈ of_fn f), P i) ↔ ∀ (j : Finₓ n), P (f j) :=
  by 
    simp only [mem_of_fn, Set.forall_range_iff]

-- error in Data.List.OfFn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[simp] theorem of_fn_const (n : exprℕ()) (c : α) : «expr = »(of_fn (λ i : fin n, c), repeat c n) :=
«expr $ »(nat.rec_on n (by simp [] [] [] [] [] []), λ n ihn, by simp [] [] [] ["[", expr ihn, "]"] [] [])

end List

