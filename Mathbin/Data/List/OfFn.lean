/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.Fin.Tuple.Basic
import Data.List.Join
import Data.List.Pairwise

#align_import data.list.of_fn from "leanprover-community/mathlib"@"bf27744463e9620ca4e4ebe951fe83530ae6949b"

/-!
# Lists from functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

theorem length_ofFnAux {n} (f : Fin n → α) : ∀ m h l, length (ofFnAux f m h l) = length l + m
  | 0, h, l => rfl
  | succ m, h, l => (length_of_fn_aux m _ _).trans (succ_add _ _)
#align list.length_of_fn_aux List.length_ofFnAux

#print List.length_ofFn /-
/-- The length of a list converted from a function is the size of the domain. -/
@[simp]
theorem length_ofFn {n} (f : Fin n → α) : length (ofFn f) = n :=
  (length_ofFnAux f _ _ _).trans (zero_add _)
#align list.length_of_fn List.length_ofFn
-/

theorem get?_ofFnAux {n} (f : Fin n → α) (i) :
    ∀ m h l, (∀ i, get? l i = ofFnNthVal f (i + m)) → get? (ofFnAux f m h l) i = ofFnNthVal f i
  | 0, h, l, H => H i
  | succ m, h, l, H =>
    nth_of_fn_aux m _ _
      (by
        intro j; cases' j with j
        · simp only [nth, of_fn_nth_val, zero_add, dif_pos (show m < n from h)]
        · simp only [nth, H, add_succ, succ_add])
#align list.nth_of_fn_aux List.get?_ofFnAux

#print List.get?_ofFn /-
/-- The `n`th element of a list -/
@[simp]
theorem get?_ofFn {n} (f : Fin n → α) (i) : get? (ofFn f) i = ofFnNthVal f i :=
  get?_ofFnAux f _ _ _ _ fun i => by
    simp only [of_fn_nth_val, dif_neg (not_lt.2 (Nat.le_add_left n i))] <;> rfl
#align list.nth_of_fn List.get?_ofFn
-/

#print List.nthLe_ofFn /-
theorem nthLe_ofFn {n} (f : Fin n → α) (i : Fin n) :
    nthLe (ofFn f) i ((length_ofFn f).symm ▸ i.2) = f i :=
  Option.some.inj <| by
    rw [← nth_le_nth] <;> simp only [List.get?_ofFn, of_fn_nth_val, Fin.eta, dif_pos i.is_lt]
#align list.nth_le_of_fn List.nthLe_ofFn
-/

#print List.nthLe_ofFn' /-
@[simp]
theorem nthLe_ofFn' {n} (f : Fin n → α) {i : ℕ} (h : i < (ofFn f).length) :
    nthLe (ofFn f) i h = f ⟨i, length_ofFn f ▸ h⟩ :=
  nthLe_ofFn f ⟨i, length_ofFn f ▸ h⟩
#align list.nth_le_of_fn' List.nthLe_ofFn'
-/

#print List.map_ofFn /-
@[simp]
theorem map_ofFn {β : Type _} {n : ℕ} (f : Fin n → α) (g : α → β) : map g (ofFn f) = ofFn (g ∘ f) :=
  ext_nthLe (by simp) fun i h h' => by simp
#align list.map_of_fn List.map_ofFn
-/

/-- Arrays converted to lists are the same as `of_fn` on the indexing function of the array. -/
theorem array'_eq_ofFn {n} (a : Array' n α) : a.toList = ofFn a.read :=
  by
  suffices ∀ {m h l}, DArray.revIterateAux a (fun i => cons) m h l = ofFnAux (DArray.read a) m h l
    from this
  intros; induction' m with m IH generalizing l; · rfl
  simp only [DArray.revIterateAux, of_fn_aux, IH]
#align list.array_eq_of_fn List.array'_eq_ofFn

#print List.ofFn_congr /-
@[congr]
theorem ofFn_congr {m n : ℕ} (h : m = n) (f : Fin m → α) :
    ofFn f = ofFn fun i : Fin n => f (Fin.castOrderIso h.symm i) :=
  by
  subst h
  simp_rw [Fin.castOrderIso_refl, OrderIso.refl_apply]
#align list.of_fn_congr List.ofFn_congr
-/

#print List.ofFn_zero /-
/-- `of_fn` on an empty domain is the empty list. -/
@[simp]
theorem ofFn_zero (f : Fin 0 → α) : ofFn f = [] :=
  rfl
#align list.of_fn_zero List.ofFn_zero
-/

#print List.ofFn_succ /-
@[simp]
theorem ofFn_succ {n} (f : Fin (succ n) → α) : ofFn f = f 0 :: ofFn fun i => f i.succ :=
  by
  suffices
    ∀ {m h l}, ofFnAux f (succ m) (succ_le_succ h) l = f 0 :: ofFnAux (fun i => f i.succ) m h l from
    this
  intros; induction' m with m IH generalizing l; · rfl
  rw [of_fn_aux, IH]; rfl
#align list.of_fn_succ List.ofFn_succ
-/

#print List.ofFn_succ' /-
theorem ofFn_succ' {n} (f : Fin (succ n) → α) :
    ofFn f = (ofFn fun i => f i.cast_succ).push (f (Fin.last _)) :=
  by
  induction' n with n IH
  · rw [of_fn_zero, concat_nil, of_fn_succ, of_fn_zero]; rfl
  · rw [of_fn_succ, IH, of_fn_succ, concat_cons, Fin.castSucc_zero']
    congr 3
    simp_rw [Fin.castSucc_fin_succ]
#align list.of_fn_succ' List.ofFn_succ'
-/

#print List.ofFn_eq_nil_iff /-
@[simp]
theorem ofFn_eq_nil_iff {n : ℕ} {f : Fin n → α} : ofFn f = [] ↔ n = 0 := by
  cases n <;> simp only [of_fn_zero, of_fn_succ, eq_self_iff_true, Nat.succ_ne_zero]
#align list.of_fn_eq_nil_iff List.ofFn_eq_nil_iff
-/

#print List.last_ofFn /-
theorem last_ofFn {n : ℕ} (f : Fin n → α) (h : ofFn f ≠ [])
    (hn : n - 1 < n := Nat.pred_lt <| ofFn_eq_nil_iff.Not.mp h) :
    getLast (ofFn f) h = f ⟨n - 1, hn⟩ := by simp [last_eq_nth_le]
#align list.last_of_fn List.last_ofFn
-/

#print List.last_ofFn_succ /-
theorem last_ofFn_succ {n : ℕ} (f : Fin n.succ → α)
    (h : ofFn f ≠ [] := mt ofFn_eq_nil_iff.mp (Nat.succ_ne_zero _)) :
    getLast (ofFn f) h = f (Fin.last _) :=
  last_ofFn f h
#align list.last_of_fn_succ List.last_ofFn_succ
-/

#print List.ofFn_add /-
/-- Note this matches the convention of `list.of_fn_succ'`, putting the `fin m` elements first. -/
theorem ofFn_add {m n} (f : Fin (m + n) → α) :
    List.ofFn f =
      (List.ofFn fun i => f (Fin.castAddOrderEmb n i)) ++
        List.ofFn fun j => f (Fin.natAddOrderEmb m j) :=
  by
  induction' n with n IH
  · rw [of_fn_zero, append_nil, Fin.castAdd_zero, Fin.castOrderIso_refl]; rfl
  · rw [of_fn_succ', of_fn_succ', IH, append_concat]; rfl
#align list.of_fn_add List.ofFn_add
-/

#print List.ofFn_fin_append /-
@[simp]
theorem ofFn_fin_append {m n} (a : Fin m → α) (b : Fin n → α) :
    List.ofFn (Fin.append a b) = List.ofFn a ++ List.ofFn b := by
  simp_rw [of_fn_add, Fin.append_left, Fin.append_right]
#align list.of_fn_fin_append List.ofFn_fin_append
-/

#print List.ofFn_mul /-
/-- This breaks a list of `m*n` items into `m` groups each containing `n` elements. -/
theorem ofFn_mul {m n} (f : Fin (m * n) → α) :
    List.ofFn f =
      List.join
        (List.ofFn fun i : Fin m =>
          List.ofFn fun j : Fin n =>
            f
              ⟨i * n + j,
                calc
                  ↑i * n + j < (i + 1) * n :=
                    (add_lt_add_left j.Prop _).trans_eq (add_one_mul _ _).symm
                  _ ≤ _ := Nat.mul_le_mul_right _ i.Prop⟩) :=
  by
  induction' m with m IH
  · simp_rw [of_fn_zero, MulZeroClass.zero_mul, of_fn_zero, join]
  · simp_rw [of_fn_succ', succ_mul, join_concat, of_fn_add, IH]; rfl
#align list.of_fn_mul List.ofFn_mul
-/

#print List.ofFn_mul' /-
/-- This breaks a list of `m*n` items into `n` groups each containing `m` elements. -/
theorem ofFn_mul' {m n} (f : Fin (m * n) → α) :
    List.ofFn f =
      List.join
        (List.ofFn fun i : Fin n =>
          List.ofFn fun j : Fin m =>
            f
              ⟨m * i + j,
                calc
                  m * i + j < m * (i + 1) :=
                    (add_lt_add_left j.Prop _).trans_eq (mul_add_one _ _).symm
                  _ ≤ _ := Nat.mul_le_mul_left _ i.Prop⟩) :=
  by simp_rw [mul_comm m n, mul_comm m, of_fn_mul, Fin.cast_mk]
#align list.of_fn_mul' List.ofFn_mul'
-/

#print List.ofFn_nthLe /-
theorem ofFn_nthLe : ∀ l : List α, (ofFn fun i => nthLe l i i.2) = l
  | [] => rfl
  | a :: l => by rw [of_fn_succ]; congr; simp only [Fin.val_succ]; exact of_fn_nth_le l
#align list.of_fn_nth_le List.ofFn_nthLe
-/

#print List.mem_ofFn /-
-- not registered as a simp lemma, as otherwise it fires before `forall_mem_of_fn_iff` which
-- is much more useful
theorem mem_ofFn {n} (f : Fin n → α) (a : α) : a ∈ ofFn f ↔ a ∈ Set.range f :=
  by
  simp only [mem_iff_nth_le, Set.mem_range, nth_le_of_fn']
  exact
    ⟨fun ⟨i, hi, h⟩ => ⟨_, h⟩, fun ⟨i, hi⟩ => ⟨i.1, (length_of_fn f).symm ▸ i.2, by simpa using hi⟩⟩
#align list.mem_of_fn List.mem_ofFn
-/

#print List.forall_mem_ofFn_iff /-
@[simp]
theorem forall_mem_ofFn_iff {n : ℕ} {f : Fin n → α} {P : α → Prop} :
    (∀ i ∈ ofFn f, P i) ↔ ∀ j : Fin n, P (f j) := by simp only [mem_of_fn, Set.forall_mem_range]
#align list.forall_mem_of_fn_iff List.forall_mem_ofFn_iff
-/

#print List.ofFn_const /-
@[simp]
theorem ofFn_const (n : ℕ) (c : α) : (ofFn fun i : Fin n => c) = replicate n c :=
  Nat.recOn n (by simp) fun n ihn => by simp [ihn]
#align list.of_fn_const List.ofFn_const
-/

#print List.ofFn_fin_repeat /-
@[simp]
theorem ofFn_fin_repeat {m} (a : Fin m → α) (n : ℕ) :
    List.ofFn (Fin.repeat n a) = (List.replicate n (List.ofFn a)).join := by
  simp_rw [of_fn_mul, ← of_fn_const, Fin.repeat, Fin.modNat, Fin.val_mk, add_comm,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Fin.is_lt _), Fin.eta]
#align list.of_fn_fin_repeat List.ofFn_fin_repeat
-/

#print List.pairwise_ofFn /-
@[simp]
theorem pairwise_ofFn {R : α → α → Prop} {n} {f : Fin n → α} :
    (ofFn f).Pairwise R ↔ ∀ ⦃i j⦄, i < j → R (f i) (f j) :=
  by
  simp only [pairwise_iff_nth_le, Fin.forall_iff, length_of_fn, nth_le_of_fn', Fin.mk_lt_mk]
  exact ⟨fun h i hi j hj hij => h _ _ hj hij, fun h i j hj hij => h _ (hij.trans hj) _ hj hij⟩
#align list.pairwise_of_fn List.pairwise_ofFn
-/

#print List.equivSigmaTuple /-
/-- Lists are equivalent to the sigma type of tuples of a given length. -/
@[simps]
def equivSigmaTuple : List α ≃ Σ n, Fin n → α
    where
  toFun l := ⟨l.length, fun i => l.nthLe (↑i) i.2⟩
  invFun f := List.ofFn f.2
  left_inv := List.ofFn_nthLe
  right_inv := fun ⟨n, f⟩ =>
    Fin.sigma_eq_of_eq_comp_cast (length_ofFn _) <| funext fun i => nthLe_ofFn' f i.Prop
#align list.equiv_sigma_tuple List.equivSigmaTuple
-/

#print List.ofFnRec /-
/-- A recursor for lists that expands a list into a function mapping to its elements.

This can be used with `induction l using list.of_fn_rec`. -/
@[elab_as_elim]
def ofFnRec {C : List α → Sort _} (h : ∀ (n) (f : Fin n → α), C (List.ofFn f)) (l : List α) : C l :=
  cast (congr_arg _ l.ofFn_nthLe) <| h l.length fun i => l.nthLe (↑i) i.2
#align list.of_fn_rec List.ofFnRec
-/

#print List.ofFnRec_ofFn /-
@[simp]
theorem ofFnRec_ofFn {C : List α → Sort _} (h : ∀ (n) (f : Fin n → α), C (List.ofFn f)) {n : ℕ}
    (f : Fin n → α) : @ofFnRec _ C h (List.ofFn f) = h _ f :=
  equivSigmaTuple.rightInverse_symm.cast_eq (fun s => h s.1 s.2) ⟨n, f⟩
#align list.of_fn_rec_of_fn List.ofFnRec_ofFn
-/

#print List.exists_iff_exists_tuple /-
theorem exists_iff_exists_tuple {P : List α → Prop} :
    (∃ l : List α, P l) ↔ ∃ (n : _) (f : Fin n → α), P (List.ofFn f) :=
  equivSigmaTuple.symm.Surjective.exists.trans Sigma.exists
#align list.exists_iff_exists_tuple List.exists_iff_exists_tuple
-/

#print List.forall_iff_forall_tuple /-
theorem forall_iff_forall_tuple {P : List α → Prop} :
    (∀ l : List α, P l) ↔ ∀ (n) (f : Fin n → α), P (List.ofFn f) :=
  equivSigmaTuple.symm.Surjective.forall.trans Sigma.forall
#align list.forall_iff_forall_tuple List.forall_iff_forall_tuple
-/

#print List.ofFn_inj' /-
/-- `fin.sigma_eq_iff_eq_comp_cast` may be useful to work with the RHS of this expression. -/
theorem ofFn_inj' {m n : ℕ} {f : Fin m → α} {g : Fin n → α} :
    ofFn f = ofFn g ↔ (⟨m, f⟩ : Σ n, Fin n → α) = ⟨n, g⟩ :=
  Iff.symm <| equivSigmaTuple.symm.Injective.eq_iff.symm
#align list.of_fn_inj' List.ofFn_inj'
-/

#print List.ofFn_injective /-
/-- Note we can only state this when the two functions are indexed by defeq `n`. -/
theorem ofFn_injective {n : ℕ} : Function.Injective (ofFn : (Fin n → α) → List α) := fun f g h =>
  eq_of_hEq <| by injection of_fn_inj'.mp h
#align list.of_fn_injective List.ofFn_injective
-/

#print List.ofFn_inj /-
/-- A special case of `list.of_fn_inj'` for when the two functions are indexed by defeq `n`. -/
@[simp]
theorem ofFn_inj {n : ℕ} {f g : Fin n → α} : ofFn f = ofFn g ↔ f = g :=
  ofFn_injective.eq_iff
#align list.of_fn_inj List.ofFn_inj
-/

end List

