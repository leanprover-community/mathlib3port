/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Fin.Tuple.Basic
import Mathbin.Data.List.Basic
import Mathbin.Data.List.Join

/-!
# Lists from functions

Theorems and lemmas for dealing with `list.of_fn`, which converts a function on `fin n` to a list
of length `n`.

## Main Statements

The main statements pertain to lists generated using `of_fn`

- `list.length_of_fn`, which tells us the length of such a list
- `list.nth_of_fn`, which tells us the nth element of such a list
- `list.array_eq_of_fn`, which interprets the list form of an array as such a list.
- `list.equiv_sigma_tuple`, which is an `equiv` between lists and the functions that generate them
  via `list.of_fn`.
-/


universe u

variable {α : Type u}

open Nat

namespace List

theorem length_of_fn_aux {n} (f : Finₓ n → α) : ∀ m h l, length (ofFnAuxₓ f m h l) = length l + m
  | 0, h, l => rfl
  | succ m, h, l => (length_of_fn_aux m _ _).trans (succ_add _ _)

/-- The length of a list converted from a function is the size of the domain. -/
@[simp]
theorem length_of_fn {n} (f : Finₓ n → α) : length (ofFnₓ f) = n :=
  (length_of_fn_aux f _ _ _).trans (zero_addₓ _)

theorem nth_of_fn_aux {n} (f : Finₓ n → α) (i) :
    ∀ m h l, (∀ i, nth l i = ofFnNthValₓ f (i + m)) → nth (ofFnAuxₓ f m h l) i = ofFnNthValₓ f i
  | 0, h, l, H => H i
  | succ m, h, l, H =>
    nth_of_fn_aux m _ _
      (by
        intro j
        cases' j with j
        · simp only [nth, of_fn_nth_val, zero_addₓ, dif_pos (show m < n from h)]
          
        · simp only [nth, H, add_succ, succ_add]
          )

/-- The `n`th element of a list -/
@[simp]
theorem nth_of_fn {n} (f : Finₓ n → α) (i) : nth (ofFnₓ f) i = ofFnNthValₓ f i :=
  (nth_of_fn_aux f _ _ _ _) fun i => by
    simp only [of_fn_nth_val, dif_neg (not_ltₓ.2 (Nat.le_add_leftₓ n i))] <;> rfl

theorem nth_le_of_fn {n} (f : Finₓ n → α) (i : Finₓ n) : nthLe (ofFnₓ f) i ((length_of_fn f).symm ▸ i.2) = f i :=
  Option.some.injₓ <| by
    rw [← nth_le_nth] <;> simp only [List.nth_of_fn, of_fn_nth_val, Finₓ.eta, dif_pos i.is_lt]

@[simp]
theorem nth_le_of_fn' {n} (f : Finₓ n → α) {i : ℕ} (h : i < (ofFnₓ f).length) :
    nthLe (ofFnₓ f) i h = f ⟨i, length_of_fn f ▸ h⟩ :=
  nth_le_of_fn f ⟨i, length_of_fn f ▸ h⟩

@[simp]
theorem map_of_fn {β : Type _} {n : ℕ} (f : Finₓ n → α) (g : α → β) : map g (ofFnₓ f) = ofFnₓ (g ∘ f) :=
  ext_le
    (by
      simp )
    fun i h h' => by
    simp

/-- Arrays converted to lists are the same as `of_fn` on the indexing function of the array. -/
theorem array_eq_of_fn {n} (a : Arrayₓ n α) : a.toList = ofFnₓ a.read := by
  suffices ∀ {m h l}, DArray.revIterateAux a (fun i => cons) m h l = ofFnAuxₓ (DArray.read a) m h l from this
  intros
  induction' m with m IH generalizing l
  · rfl
    
  simp only [DArray.revIterateAux, of_fn_aux, IH]

@[congr]
theorem of_fn_congr {m n : ℕ} (h : m = n) (f : Finₓ m → α) : ofFnₓ f = ofFnₓ fun i : Finₓ n => f (Finₓ.cast h.symm i) :=
  by
  subst h
  simp_rw [Finₓ.cast_refl, OrderIso.refl_apply]

/-- `of_fn` on an empty domain is the empty list. -/
@[simp]
theorem of_fn_zero (f : Finₓ 0 → α) : ofFnₓ f = [] :=
  rfl

@[simp]
theorem of_fn_succ {n} (f : Finₓ (succ n) → α) : ofFnₓ f = f 0 :: ofFnₓ fun i => f i.succ := by
  suffices ∀ {m h l}, ofFnAuxₓ f (succ m) (succ_le_succₓ h) l = f 0 :: ofFnAuxₓ (fun i => f i.succ) m h l from this
  intros
  induction' m with m IH generalizing l
  · rfl
    
  rw [of_fn_aux, IH]
  rfl

theorem of_fn_succ' {n} (f : Finₓ (succ n) → α) : ofFnₓ f = (ofFnₓ fun i => f i.cast_succ).concat (f (Finₓ.last _)) :=
  by
  induction' n with n IH
  · rw [of_fn_zero, concat_nil, of_fn_succ, of_fn_zero]
    rfl
    
  · rw [of_fn_succ, IH, of_fn_succ, concat_cons, Finₓ.cast_succ_zero]
    congr 3
    simp_rw [Finₓ.cast_succ_fin_succ]
    

@[simp]
theorem of_fn_eq_nil_iff {n : ℕ} {f : Finₓ n → α} : ofFnₓ f = [] ↔ n = 0 := by
  cases n <;> simp only [of_fn_zero, of_fn_succ, eq_self_iff_true, Nat.succ_ne_zero]

theorem last_of_fn {n : ℕ} (f : Finₓ n → α) (h : ofFnₓ f ≠ [])
    (hn : n - 1 < n := Nat.pred_ltₓ <| of_fn_eq_nil_iff.Not.mp h) : last (ofFnₓ f) h = f ⟨n - 1, hn⟩ := by
  simp [last_eq_nth_le]

theorem last_of_fn_succ {n : ℕ} (f : Finₓ n.succ → α)
    (h : ofFnₓ f ≠ [] := mt of_fn_eq_nil_iff.mp (Nat.succ_ne_zero _)) : last (ofFnₓ f) h = f (Finₓ.last _) :=
  last_of_fn f h

/-- Note this matches the convention of `list.of_fn_succ'`, putting the `fin m` elements first. -/
theorem of_fn_add {m n} (f : Finₓ (m + n) → α) :
    List.ofFnₓ f = (List.ofFnₓ fun i => f (Finₓ.castAdd n i)) ++ List.ofFnₓ fun j => f (Finₓ.natAdd m j) := by
  induction' n with n IH
  · rw [of_fn_zero, append_nil, Finₓ.cast_add_zero, Finₓ.cast_refl]
    rfl
    
  · rw [of_fn_succ', of_fn_succ', IH, append_concat]
    rfl
    

/-- This breaks a list of `m*n` items into `m` groups each containing `n` elements. -/
theorem of_fn_mul {m n} (f : Finₓ (m * n) → α) :
    List.ofFnₓ f =
      List.join
        (List.ofFnₓ fun i : Finₓ m =>
          List.ofFnₓ fun j : Finₓ n =>
            f
              ⟨i * n + j,
                calc
                  ↑i * n + j < (i + 1) * n := (add_lt_add_left j.Prop _).trans_eq (add_one_mul _ _).symm
                  _ ≤ _ := Nat.mul_le_mul_rightₓ _ i.Prop
                  ⟩) :=
  by
  induction' m with m IH
  · simp_rw [of_fn_zero, zero_mul, of_fn_zero, join]
    
  · simp_rw [of_fn_succ', succ_mul, join_concat, of_fn_add, IH]
    rfl
    

/-- This breaks a list of `m*n` items into `n` groups each containing `m` elements. -/
theorem of_fn_mul' {m n} (f : Finₓ (m * n) → α) :
    List.ofFnₓ f =
      List.join
        (List.ofFnₓ fun i : Finₓ n =>
          List.ofFnₓ fun j : Finₓ m =>
            f
              ⟨m * i + j,
                calc
                  m * i + j < m * (i + 1) := (add_lt_add_left j.Prop _).trans_eq (mul_add_one _ _).symm
                  _ ≤ _ := Nat.mul_le_mul_leftₓ _ i.Prop
                  ⟩) :=
  by
  simp_rw [mul_comm m n, mul_comm m, of_fn_mul, Finₓ.cast_mk]

theorem of_fn_nth_le : ∀ l : List α, (ofFnₓ fun i => nthLe l i i.2) = l
  | [] => rfl
  | a :: l => by
    rw [of_fn_succ]
    congr
    simp only [Finₓ.coe_succ]
    exact of_fn_nth_le l

-- not registered as a simp lemma, as otherwise it fires before `forall_mem_of_fn_iff` which
-- is much more useful
theorem mem_of_fn {n} (f : Finₓ n → α) (a : α) : a ∈ ofFnₓ f ↔ a ∈ Set.Range f := by
  simp only [mem_iff_nth_le, Set.mem_range, nth_le_of_fn']
  exact
    ⟨fun ⟨i, hi, h⟩ => ⟨_, h⟩, fun ⟨i, hi⟩ =>
      ⟨i.1, (length_of_fn f).symm ▸ i.2, by
        simpa using hi⟩⟩

@[simp]
theorem forall_mem_of_fn_iff {n : ℕ} {f : Finₓ n → α} {P : α → Prop} : (∀ i ∈ ofFnₓ f, P i) ↔ ∀ j : Finₓ n, P (f j) :=
  by
  simp only [mem_of_fn, Set.forall_range_iff]

@[simp]
theorem of_fn_const (n : ℕ) (c : α) : (ofFnₓ fun i : Finₓ n => c) = repeat c n :=
  (Nat.recOn n
      (by
        simp ))
    fun n ihn => by
    simp [ihn]

/-- Lists are equivalent to the sigma type of tuples of a given length. -/
@[simps]
def equivSigmaTuple : List α ≃ Σn, Finₓ n → α where
  toFun := fun l => ⟨l.length, fun i => l.nthLe (↑i) i.2⟩
  invFun := fun f => List.ofFnₓ f.2
  left_inv := List.of_fn_nth_le
  right_inv := fun ⟨n, f⟩ => Finₓ.sigma_eq_of_eq_comp_cast (length_of_fn _) <| funext fun i => nth_le_of_fn' f i.Prop

/-- A recursor for lists that expands a list into a function mapping to its elements.

This can be used with `induction l using list.of_fn_rec`. -/
@[elabAsElim]
def ofFnRec {C : List α → Sort _} (h : ∀ (n) (f : Finₓ n → α), C (List.ofFnₓ f)) (l : List α) : C l :=
  cast (congr_arg _ l.of_fn_nth_le) <| h l.length fun i => l.nthLe (↑i) i.2

@[simp]
theorem of_fn_rec_of_fn {C : List α → Sort _} (h : ∀ (n) (f : Finₓ n → α), C (List.ofFnₓ f)) {n : ℕ} (f : Finₓ n → α) :
    @ofFnRec _ C h (List.ofFnₓ f) = h _ f :=
  equivSigmaTuple.right_inverse_symm.cast_eq (fun s => h s.1 s.2) ⟨n, f⟩

theorem exists_iff_exists_tuple {P : List α → Prop} :
    (∃ l : List α, P l) ↔ ∃ (n : _)(f : Finₓ n → α), P (List.ofFnₓ f) :=
  equivSigmaTuple.symm.Surjective.exists.trans Sigma.exists

theorem forall_iff_forall_tuple {P : List α → Prop} : (∀ l : List α, P l) ↔ ∀ (n) (f : Finₓ n → α), P (List.ofFnₓ f) :=
  equivSigmaTuple.symm.Surjective.forall.trans Sigma.forall

/-- `fin.sigma_eq_iff_eq_comp_cast` may be useful to work with the RHS of this expression. -/
theorem of_fn_inj' {m n : ℕ} {f : Finₓ m → α} {g : Finₓ n → α} :
    ofFnₓ f = ofFnₓ g ↔ (⟨m, f⟩ : Σn, Finₓ n → α) = ⟨n, g⟩ :=
  Iff.symm <| equivSigmaTuple.symm.Injective.eq_iff.symm

/-- Note we can only state this when the two functions are indexed by defeq `n`. -/
theorem of_fn_injective {n : ℕ} : Function.Injective (ofFnₓ : (Finₓ n → α) → List α) := fun f g h =>
  eq_of_heq <| by
    injection of_fn_inj'.mp h

/-- A special case of `list.of_fn_inj'` for when the two functions are indexed by defeq `n`. -/
@[simp]
theorem of_fn_inj {n : ℕ} {f g : Finₓ n → α} : ofFnₓ f = ofFnₓ g ↔ f = g :=
  of_fn_injective.eq_iff

end List

