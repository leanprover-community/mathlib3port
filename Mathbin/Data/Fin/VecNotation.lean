/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module data.fin.vec_notation
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Tuple.Basic
import Mathbin.Data.List.Range
import Mathbin.GroupTheory.GroupAction.Pi
import Mathbin.Meta.Univs

/-!
# Matrix and vector notation

This file defines notation for vectors and matrices. Given `a b c d : α`,
the notation allows us to write `![a, b, c, d] : fin 4 → α`.
Nesting vectors gives coefficients of a matrix, so `![![a, b], ![c, d]] : fin 2 → fin 2 → α`.
In later files we introduce `!![a, b; c, d]` as notation for `matrix.of ![![a, b], ![c, d]]`.

## Main definitions

* `vec_empty` is the empty vector (or `0` by `n` matrix) `![]`
* `vec_cons` prepends an entry to a vector, so `![a, b]` is `vec_cons a (vec_cons b vec_empty)`

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vec_cons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notations

The main new notation is `![a, b]`, which gets expanded to `vec_cons a (vec_cons b vec_empty)`.

## Examples

Examples of usage can be found in the `test/matrix.lean` file.
-/


namespace Matrix

universe u

variable {α : Type u}

section MatrixNotation

/-- `![]` is the vector with no entries. -/
def vecEmpty : Fin 0 → α :=
  finZeroElim
#align matrix.vec_empty Matrix.vecEmpty

/-- `vec_cons h t` prepends an entry `h` to a vector `t`.

The inverse functions are `vec_head` and `vec_tail`.
The notation `![a, b, ...]` expands to `vec_cons a (vec_cons b ...)`.
-/
def vecCons {n : ℕ} (h : α) (t : Fin n → α) : Fin n.succ → α :=
  Fin.cons h t
#align matrix.vec_cons Matrix.vecCons

-- mathport name: «expr![ ,]»
notation3"!["(l", "* => foldr (h t => vecCons h t) vecEmpty)"]" => l

/-- `vec_head v` gives the first entry of the vector `v` -/
def vecHead {n : ℕ} (v : Fin n.succ → α) : α :=
  v 0
#align matrix.vec_head Matrix.vecHead

/-- `vec_tail v` gives a vector consisting of all entries of `v` except the first -/
def vecTail {n : ℕ} (v : Fin n.succ → α) : Fin n → α :=
  v ∘ Fin.succ
#align matrix.vec_tail Matrix.vecTail

variable {m n : ℕ}

/-- Use `![...]` notation for displaying a vector `fin n → α`, for example:

```
#eval ![1, 2] + ![3, 4] -- ![4, 6]
```
-/
instance PiFin.hasRepr [Repr α] :
    Repr
      (Fin n →
        α) where repr f :=
    "![" ++ String.intercalate ", " ((List.finRange n).map fun n => repr (f n)) ++ "]"
#align pi_fin.has_repr PiFin.hasRepr

end MatrixNotation

variable {m n o : ℕ} {m' n' o' : Type _}

theorem empty_eq (v : Fin 0 → α) : v = ![] :=
  Subsingleton.elim _ _
#align matrix.empty_eq Matrix.empty_eq

section Val

@[simp]
theorem head_fin_const (a : α) : (vecHead fun i : Fin (n + 1) => a) = a :=
  rfl
#align matrix.head_fin_const Matrix.head_fin_const

@[simp]
theorem cons_val_zero (x : α) (u : Fin m → α) : vecCons x u 0 = x :=
  rfl
#align matrix.cons_val_zero Matrix.cons_val_zero

theorem cons_val_zero' (h : 0 < m.succ) (x : α) (u : Fin m → α) : vecCons x u ⟨0, h⟩ = x :=
  rfl
#align matrix.cons_val_zero' Matrix.cons_val_zero'

@[simp]
theorem cons_val_succ (x : α) (u : Fin m → α) (i : Fin m) : vecCons x u i.succ = u i := by
  simp [vec_cons]
#align matrix.cons_val_succ Matrix.cons_val_succ

@[simp]
theorem cons_val_succ' {i : ℕ} (h : i.succ < m.succ) (x : α) (u : Fin m → α) :
    vecCons x u ⟨i.succ, h⟩ = u ⟨i, Nat.lt_of_succ_lt_succ h⟩ := by
  simp only [vec_cons, Fin.cons, Fin.cases_succ']
#align matrix.cons_val_succ' Matrix.cons_val_succ'

@[simp]
theorem head_cons (x : α) (u : Fin m → α) : vecHead (vecCons x u) = x :=
  rfl
#align matrix.head_cons Matrix.head_cons

@[simp]
theorem tail_cons (x : α) (u : Fin m → α) : vecTail (vecCons x u) = u := by
  ext
  simp [vec_tail]
#align matrix.tail_cons Matrix.tail_cons

@[simp]
theorem empty_val' {n' : Type _} (j : n') : (fun i => (![] : Fin 0 → n' → α) i j) = ![] :=
  empty_eq _
#align matrix.empty_val' Matrix.empty_val'

@[simp]
theorem cons_head_tail (u : Fin m.succ → α) : vecCons (vecHead u) (vecTail u) = u :=
  Fin.cons_self_tail _
#align matrix.cons_head_tail Matrix.cons_head_tail

@[simp]
theorem range_cons (x : α) (u : Fin n → α) : Set.range (vecCons x u) = {x} ∪ Set.range u :=
  Set.ext fun y => by simp [Fin.exists_fin_succ, eq_comm]
#align matrix.range_cons Matrix.range_cons

@[simp]
theorem range_empty (u : Fin 0 → α) : Set.range u = ∅ :=
  Set.range_eq_empty _
#align matrix.range_empty Matrix.range_empty

@[simp]
theorem vec_cons_const (a : α) : (vecCons a fun k : Fin n => a) = fun _ => a :=
  funext <| Fin.forall_fin_succ.2 ⟨rfl, cons_val_succ _ _⟩
#align matrix.vec_cons_const Matrix.vec_cons_const

theorem vec_single_eq_const (a : α) : ![a] = fun _ => a :=
  funext <| Unique.forall_iff.2 rfl
#align matrix.vec_single_eq_const Matrix.vec_single_eq_const

/-- `![a, b, ...] 1` is equal to `b`.

  The simplifier needs a special lemma for length `≥ 2`, in addition to
  `cons_val_succ`, because `1 : fin 1 = 0 : fin 1`.
-/
@[simp]
theorem cons_val_one (x : α) (u : Fin m.succ → α) : vecCons x u 1 = vecHead u := by
  rw [← Fin.succ_zero_eq_one, cons_val_succ]
  rfl
#align matrix.cons_val_one Matrix.cons_val_one

@[simp]
theorem cons_val_fin_one (x : α) (u : Fin 0 → α) (i : Fin 1) : vecCons x u i = x := by
  refine' Fin.forall_fin_one.2 _ i
  rfl
#align matrix.cons_val_fin_one Matrix.cons_val_fin_one

theorem cons_fin_one (x : α) (u : Fin 0 → α) : vecCons x u = fun _ => x :=
  funext (cons_val_fin_one x u)
#align matrix.cons_fin_one Matrix.cons_fin_one

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[] -/
unsafe instance _root_.pi_fin.reflect [reflected_univ.{u}] [reflected _ α] [has_reflect α] :
    ∀ {n}, has_reflect (Fin n → α)
  | 0, v =>
    (Subsingleton.elim vecEmpty v).rec
      ((by
            trace
              "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[]" :
            reflected _ @vecEmpty.{u}).subst
        q(α))
  | n + 1, v =>
    (cons_head_tail v).rec <|
      (by
            trace
              "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[]" :
            reflected _ @vecCons.{u}).subst₄
        q(α) q(n) q(_) (_root_.pi_fin.reflect _)
#align pi_fin.reflect pi_fin.reflect

/-- Convert a vector of pexprs to the pexpr constructing that vector.-/
unsafe def _root_.pi_fin.to_pexpr : ∀ {n}, (Fin n → pexpr) → pexpr
  | 0, v => ``(![])
  | n + 1, v => ``(vecCons $(v 0) $(_root_.pi_fin.to_pexpr <| vecTail v))
#align pi_fin.to_pexpr pi_fin.to_pexpr

/-! ### Numeral (`bit0` and `bit1`) indices
The following definitions and `simp` lemmas are to allow any
numeral-indexed element of a vector given with matrix notation to
be extracted by `simp` (even when the numeral is larger than the
number of elements in the vector, which is taken modulo that number
of elements by virtue of the semantics of `bit0` and `bit1` and of
addition on `fin n`).
-/


@[simp]
theorem empty_append (v : Fin n → α) : Fin.append (zero_add _).symm ![] v = v := by
  ext
  simp [Fin.append]
#align matrix.empty_append Matrix.empty_append

@[simp]
theorem cons_append (ho : o + 1 = m + 1 + n) (x : α) (u : Fin m → α) (v : Fin n → α) :
    Fin.append ho (vecCons x u) v =
      vecCons x
        (Fin.append (by rwa [add_assoc, add_comm 1, ← add_assoc, add_right_cancel_iff] at ho) u
          v) :=
  by 
  ext i
  simp_rw [Fin.append]
  split_ifs with h
  · rcases i with ⟨⟨⟩ | i, hi⟩
    · simp
    · simp only [Nat.succ_eq_add_one, add_lt_add_iff_right, Fin.coe_mk] at h
      simp [h]
  · rcases i with ⟨⟨⟩ | i, hi⟩
    · simpa using h
    · rw [not_lt, Fin.coe_mk, Nat.succ_eq_add_one, add_le_add_iff_right] at h
      simp [h]
#align matrix.cons_append Matrix.cons_append

/-- `vec_alt0 v` gives a vector with half the length of `v`, with
only alternate elements (even-numbered). -/
def vecAlt0 (hm : m = n + n) (v : Fin m → α) (k : Fin n) : α :=
  v ⟨(k : ℕ) + k, hm.symm ▸ add_lt_add k.property k.property⟩
#align matrix.vec_alt0 Matrix.vecAlt0

/-- `vec_alt1 v` gives a vector with half the length of `v`, with
only alternate elements (odd-numbered). -/
def vecAlt1 (hm : m = n + n) (v : Fin m → α) (k : Fin n) : α :=
  v ⟨(k : ℕ) + k + 1, hm.symm ▸ Nat.add_succ_lt_add k.property k.property⟩
#align matrix.vec_alt1 Matrix.vecAlt1

theorem vec_alt0_append (v : Fin n → α) : vecAlt0 rfl (Fin.append rfl v v) = v ∘ bit0 := by
  ext i
  simp_rw [Function.comp, bit0, vec_alt0, Fin.append]
  split_ifs with h <;> congr
  · rw [Fin.coe_mk] at h
    simp only [Fin.ext_iff, Fin.coe_add, Fin.coe_mk]
    exact (Nat.mod_eq_of_lt h).symm
  · rw [Fin.coe_mk, not_lt] at h
    simp only [Fin.ext_iff, Fin.coe_add, Fin.coe_mk, Nat.mod_eq_sub_mod h]
    refine' (Nat.mod_eq_of_lt _).symm
    rw [tsub_lt_iff_left h]
    exact add_lt_add i.property i.property
#align matrix.vec_alt0_append Matrix.vec_alt0_append

theorem vec_alt1_append (v : Fin (n + 1) → α) : vecAlt1 rfl (Fin.append rfl v v) = v ∘ bit1 := by
  ext i
  simp_rw [Function.comp, vec_alt1, Fin.append]
  cases n
  · simp
    congr
  · split_ifs with h <;> simp_rw [bit1, bit0] <;> congr
    · simp only [Fin.ext_iff, Fin.coe_add, Fin.coe_mk]
      rw [Fin.coe_mk] at h
      rw [Fin.coe_one]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_succ_lt h)]
      rw [Nat.mod_eq_of_lt h]
    · rw [Fin.coe_mk, not_lt] at h
      simp only [Fin.ext_iff, Fin.coe_add, Fin.coe_mk, Nat.mod_add_mod, Fin.coe_one,
        Nat.mod_eq_sub_mod h]
      refine' (Nat.mod_eq_of_lt _).symm
      rw [tsub_lt_iff_left h]
      exact Nat.add_succ_lt_add i.property i.property
#align matrix.vec_alt1_append Matrix.vec_alt1_append

@[simp]
theorem vec_head_vec_alt0 (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) → α) :
    vecHead (vecAlt0 hm v) = v 0 :=
  rfl
#align matrix.vec_head_vec_alt0 Matrix.vec_head_vec_alt0

@[simp]
theorem vec_head_vec_alt1 (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) → α) :
    vecHead (vecAlt1 hm v) = v 1 := by simp [vec_head, vec_alt1]
#align matrix.vec_head_vec_alt1 Matrix.vec_head_vec_alt1

@[simp]
theorem cons_vec_bit0_eq_alt0 (x : α) (u : Fin n → α) (i : Fin (n + 1)) :
    vecCons x u (bit0 i) = vecAlt0 rfl (Fin.append rfl (vecCons x u) (vecCons x u)) i := by
  rw [vec_alt0_append]
#align matrix.cons_vec_bit0_eq_alt0 Matrix.cons_vec_bit0_eq_alt0

@[simp]
theorem cons_vec_bit1_eq_alt1 (x : α) (u : Fin n → α) (i : Fin (n + 1)) :
    vecCons x u (bit1 i) = vecAlt1 rfl (Fin.append rfl (vecCons x u) (vecCons x u)) i := by
  rw [vec_alt1_append]
#align matrix.cons_vec_bit1_eq_alt1 Matrix.cons_vec_bit1_eq_alt1

@[simp]
theorem cons_vec_alt0 (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m → α) :
    vecAlt0 h (vecCons x (vecCons y u)) =
      vecCons x
        (vecAlt0
          (by
            rwa [add_assoc n, add_comm 1, ← add_assoc, ← add_assoc, add_right_cancel_iff,
              add_right_cancel_iff] at h)
          u) :=
  by 
  ext i
  simp_rw [vec_alt0]
  rcases i with ⟨⟨⟩ | i, hi⟩
  · rfl
  · simp [vec_alt0, Nat.add_succ, Nat.succ_add]
#align matrix.cons_vec_alt0 Matrix.cons_vec_alt0

-- Although proved by simp, extracting element 8 of a five-element
-- vector does not work by simp unless this lemma is present.
@[simp]
theorem empty_vec_alt0 (α) {h} : vecAlt0 h (![] : Fin 0 → α) = ![] := by simp
#align matrix.empty_vec_alt0 Matrix.empty_vec_alt0

@[simp]
theorem cons_vec_alt1 (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m → α) :
    vecAlt1 h (vecCons x (vecCons y u)) =
      vecCons y
        (vecAlt1
          (by
            rwa [add_assoc n, add_comm 1, ← add_assoc, ← add_assoc, add_right_cancel_iff,
              add_right_cancel_iff] at h)
          u) :=
  by 
  ext i
  simp_rw [vec_alt1]
  rcases i with ⟨⟨⟩ | i, hi⟩
  · rfl
  · simp [vec_alt1, Nat.add_succ, Nat.succ_add]
#align matrix.cons_vec_alt1 Matrix.cons_vec_alt1

-- Although proved by simp, extracting element 9 of a five-element
-- vector does not work by simp unless this lemma is present.
@[simp]
theorem empty_vec_alt1 (α) {h} : vecAlt1 h (![] : Fin 0 → α) = ![] := by simp
#align matrix.empty_vec_alt1 Matrix.empty_vec_alt1

end Val

section Smul

variable {M : Type _} [HasSmul M α]

@[simp]
theorem smul_empty (x : M) (v : Fin 0 → α) : x • v = ![] :=
  empty_eq _
#align matrix.smul_empty Matrix.smul_empty

@[simp]
theorem smul_cons (x : M) (y : α) (v : Fin n → α) : x • vecCons y v = vecCons (x • y) (x • v) := by
  ext i
  refine' Fin.cases _ _ i <;> simp
#align matrix.smul_cons Matrix.smul_cons

end Smul

section Add

variable [Add α]

@[simp]
theorem empty_add_empty (v w : Fin 0 → α) : v + w = ![] :=
  empty_eq _
#align matrix.empty_add_empty Matrix.empty_add_empty

@[simp]
theorem cons_add (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    vecCons x v + w = vecCons (x + vecHead w) (v + vecTail w) := by
  ext i
  refine' Fin.cases _ _ i <;> simp [vec_head, vec_tail]
#align matrix.cons_add Matrix.cons_add

@[simp]
theorem add_cons (v : Fin n.succ → α) (y : α) (w : Fin n → α) :
    v + vecCons y w = vecCons (vecHead v + y) (vecTail v + w) := by
  ext i
  refine' Fin.cases _ _ i <;> simp [vec_head, vec_tail]
#align matrix.add_cons Matrix.add_cons

@[simp]
theorem cons_add_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    vecCons x v + vecCons y w = vecCons (x + y) (v + w) := by simp
#align matrix.cons_add_cons Matrix.cons_add_cons

@[simp]
theorem head_add (a b : Fin n.succ → α) : vecHead (a + b) = vecHead a + vecHead b :=
  rfl
#align matrix.head_add Matrix.head_add

@[simp]
theorem tail_add (a b : Fin n.succ → α) : vecTail (a + b) = vecTail a + vecTail b :=
  rfl
#align matrix.tail_add Matrix.tail_add

end Add

section Sub

variable [Sub α]

@[simp]
theorem empty_sub_empty (v w : Fin 0 → α) : v - w = ![] :=
  empty_eq _
#align matrix.empty_sub_empty Matrix.empty_sub_empty

@[simp]
theorem cons_sub (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    vecCons x v - w = vecCons (x - vecHead w) (v - vecTail w) := by
  ext i
  refine' Fin.cases _ _ i <;> simp [vec_head, vec_tail]
#align matrix.cons_sub Matrix.cons_sub

@[simp]
theorem sub_cons (v : Fin n.succ → α) (y : α) (w : Fin n → α) :
    v - vecCons y w = vecCons (vecHead v - y) (vecTail v - w) := by
  ext i
  refine' Fin.cases _ _ i <;> simp [vec_head, vec_tail]
#align matrix.sub_cons Matrix.sub_cons

@[simp]
theorem cons_sub_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    vecCons x v - vecCons y w = vecCons (x - y) (v - w) := by simp
#align matrix.cons_sub_cons Matrix.cons_sub_cons

@[simp]
theorem head_sub (a b : Fin n.succ → α) : vecHead (a - b) = vecHead a - vecHead b :=
  rfl
#align matrix.head_sub Matrix.head_sub

@[simp]
theorem tail_sub (a b : Fin n.succ → α) : vecTail (a - b) = vecTail a - vecTail b :=
  rfl
#align matrix.tail_sub Matrix.tail_sub

end Sub

section Zero

variable [Zero α]

@[simp]
theorem zero_empty : (0 : Fin 0 → α) = ![] :=
  empty_eq _
#align matrix.zero_empty Matrix.zero_empty

@[simp]
theorem cons_zero_zero : vecCons (0 : α) (0 : Fin n → α) = 0 := by
  ext (i j)
  refine' Fin.cases _ _ i
  · rfl
  simp
#align matrix.cons_zero_zero Matrix.cons_zero_zero

@[simp]
theorem head_zero : vecHead (0 : Fin n.succ → α) = 0 :=
  rfl
#align matrix.head_zero Matrix.head_zero

@[simp]
theorem tail_zero : vecTail (0 : Fin n.succ → α) = 0 :=
  rfl
#align matrix.tail_zero Matrix.tail_zero

@[simp]
theorem cons_eq_zero_iff {v : Fin n → α} {x : α} : vecCons x v = 0 ↔ x = 0 ∧ v = 0 :=
  ⟨fun h =>
    ⟨congr_fun h 0, by 
      convert congr_arg vec_tail h
      simp⟩,
    fun ⟨hx, hv⟩ => by simp [hx, hv]⟩
#align matrix.cons_eq_zero_iff Matrix.cons_eq_zero_iff

open Classical

theorem cons_nonzero_iff {v : Fin n → α} {x : α} : vecCons x v ≠ 0 ↔ x ≠ 0 ∨ v ≠ 0 :=
  ⟨fun h => not_and_or.mp (h ∘ cons_eq_zero_iff.mpr), fun h =>
    mt cons_eq_zero_iff.mp (not_and_or.mpr h)⟩
#align matrix.cons_nonzero_iff Matrix.cons_nonzero_iff

end Zero

section Neg

variable [Neg α]

@[simp]
theorem neg_empty (v : Fin 0 → α) : -v = ![] :=
  empty_eq _
#align matrix.neg_empty Matrix.neg_empty

@[simp]
theorem neg_cons (x : α) (v : Fin n → α) : -vecCons x v = vecCons (-x) (-v) := by
  ext i
  refine' Fin.cases _ _ i <;> simp
#align matrix.neg_cons Matrix.neg_cons

@[simp]
theorem head_neg (a : Fin n.succ → α) : vecHead (-a) = -vecHead a :=
  rfl
#align matrix.head_neg Matrix.head_neg

@[simp]
theorem tail_neg (a : Fin n.succ → α) : vecTail (-a) = -vecTail a :=
  rfl
#align matrix.tail_neg Matrix.tail_neg

end Neg

end Matrix

