/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

General utility functions for buffers.

! This file was ported from Lean 3 source module data.buffer.basic
! leanprover-community/mathlib commit 986c4d5761f938b2e1c43c01f001b6d9d88c2055
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Array.Lemmas
import Mathbin.Control.Traversable.Instances

namespace Buffer

open Function

variable {α : Type _} {xs : List α}

instance : Inhabited (Buffer α) :=
  ⟨nil⟩

@[ext]
theorem ext : ∀ {b₁ b₂ : Buffer α}, toList b₁ = toList b₂ → b₁ = b₂
  | ⟨n₁, a₁⟩, ⟨n₂, a₂⟩, h => by
    simp [to_list, to_array] at h
    have e : n₁ = n₂ := by rw [← Array'.to_list_length a₁, ← Array'.to_list_length a₂, h]
    subst e
    have h : HEq a₁ a₂.to_list.to_array := h ▸ a₁.to_list_to_array.symm
    rw [eq_of_heq (h.trans a₂.to_list_to_array)]
#align buffer.ext Buffer.ext

theorem ext_iff {b₁ b₂ : Buffer α} : b₁ = b₂ ↔ toList b₁ = toList b₂ :=
  ⟨fun h => h ▸ rfl, ext⟩
#align buffer.ext_iff Buffer.ext_iff

theorem size_eq_zero_iff {b : Buffer α} : b.size = 0 ↔ b = nil :=
  by
  rcases b with ⟨_ | n, ⟨a⟩⟩
  · simp only [size, nil, mkBuffer, true_and_iff, true_iff_iff, eq_self_iff_true, heq_iff_eq,
      Sigma.mk.inj_iff]
    ext i
    exact Fin.elim0 i
  · simp [size, nil, mkBuffer, Nat.succ_ne_zero]
#align buffer.size_eq_zero_iff Buffer.size_eq_zero_iff

@[simp]
theorem size_nil : (@nil α).size = 0 := by rw [size_eq_zero_iff]
#align buffer.size_nil Buffer.size_nil

@[simp]
theorem to_list_nil : toList (@nil α) = [] :=
  rfl
#align buffer.to_list_nil Buffer.to_list_nil

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_dec_eq_instance -/
instance (α) [DecidableEq α] : DecidableEq (Buffer α) := by
  run_tac
    tactic.mk_dec_eq_instance

@[simp]
theorem to_list_append_list {b : Buffer α} : toList (appendList b xs) = toList b ++ xs := by
  induction xs generalizing b <;> simp! [*] <;> cases b <;> simp! [to_list, to_array]
#align buffer.to_list_append_list Buffer.to_list_append_list

@[simp]
theorem append_list_mk_buffer : appendList mkBuffer xs = Array'.toBuffer (List.toArray xs) := by
  ext x : 1 <;> simp [Array'.toBuffer, to_list, to_list_append_list] <;> induction xs <;> [rfl,
        skip] <;>
      simp [to_array] <;>
    rfl
#align buffer.append_list_mk_buffer Buffer.append_list_mk_buffer

@[simp]
theorem to_buffer_to_list (b : Buffer α) : b.toList.toBuffer = b :=
  by
  cases b
  rw [to_list, to_array, List.toBuffer, append_list_mk_buffer]
  congr
  · simpa
  · apply Array'.to_list_to_array
#align buffer.to_buffer_to_list Buffer.to_buffer_to_list

@[simp]
theorem to_list_to_buffer (l : List α) : l.toBuffer.toList = l :=
  by
  cases l
  · rfl
  · rw [List.toBuffer, to_list_append_list]
    rfl
#align buffer.to_list_to_buffer Buffer.to_list_to_buffer

@[simp]
theorem to_list_to_array (b : Buffer α) : b.toArray.toList = b.toList :=
  by
  cases b
  simp [to_list]
#align buffer.to_list_to_array Buffer.to_list_to_array

@[simp]
theorem append_list_nil (b : Buffer α) : b.appendList [] = b :=
  rfl
#align buffer.append_list_nil Buffer.append_list_nil

theorem to_buffer_cons (c : α) (l : List α) : (c :: l).toBuffer = [c].toBuffer.appendList l :=
  by
  induction' l with hd tl hl
  · simp
  · apply ext
    simp [hl]
#align buffer.to_buffer_cons Buffer.to_buffer_cons

@[simp]
theorem size_push_back (b : Buffer α) (a : α) : (b.pushBack a).size = b.size + 1 :=
  by
  cases b
  simp [size, push_back]
#align buffer.size_push_back Buffer.size_push_back

@[simp]
theorem size_append_list (b : Buffer α) (l : List α) : (b.appendList l).size = b.size + l.length :=
  by
  induction' l with hd tl hl generalizing b
  · simp
  · simp [append_list, hl, add_comm, add_assoc]
#align buffer.size_append_list Buffer.size_append_list

@[simp]
theorem size_to_buffer (l : List α) : l.toBuffer.size = l.length :=
  by
  induction' l with hd tl hl
  · simpa
  · rw [to_buffer_cons]
    have : [hd].toBuffer.size = 1 := rfl
    simp [add_comm, this]
#align buffer.size_to_buffer Buffer.size_to_buffer

@[simp]
theorem length_to_list (b : Buffer α) : b.toList.length = b.size := by
  rw [← to_buffer_to_list b, to_list_to_buffer, size_to_buffer]
#align buffer.length_to_list Buffer.length_to_list

theorem size_singleton (a : α) : [a].toBuffer.size = 1 :=
  rfl
#align buffer.size_singleton Buffer.size_singleton

theorem read_push_back_left (b : Buffer α) (a : α) {i : ℕ} (h : i < b.size) :
    (b.pushBack a).read
        ⟨i, by
          convert Nat.lt_succ_of_lt h
          simp⟩ =
      b.read ⟨i, h⟩ :=
  by
  cases b
  convert Array'.read_push_back_left _
  simp
#align buffer.read_push_back_left Buffer.read_push_back_left

@[simp]
theorem read_push_back_right (b : Buffer α) (a : α) : (b.pushBack a).read ⟨b.size, by simp⟩ = a :=
  by
  cases b
  convert Array'.read_push_back_right
#align buffer.read_push_back_right Buffer.read_push_back_right

theorem read_append_list_left' (b : Buffer α) (l : List α) {i : ℕ} (h : i < (b.appendList l).size)
    (h' : i < b.size) : (b.appendList l).read ⟨i, h⟩ = b.read ⟨i, h'⟩ :=
  by
  induction' l with hd tl hl generalizing b
  · rfl
  · have hb : i < ((b.push_back hd).appendList tl).size := by convert h using 1
    have hb' : i < (b.push_back hd).size :=
      by
      convert Nat.lt_succ_of_lt h'
      simp
    have : (append_list b (hd :: tl)).read ⟨i, h⟩ = read ((push_back b hd).appendList tl) ⟨i, hb⟩ :=
      rfl
    simp [this, hl _ hb hb', read_push_back_left _ _ h']
#align buffer.read_append_list_left' Buffer.read_append_list_left'

theorem read_append_list_left (b : Buffer α) (l : List α) {i : ℕ} (h : i < b.size) :
    (b.appendList l).read ⟨i, by simpa using Nat.lt_add_right _ _ _ h⟩ = b.read ⟨i, h⟩ :=
  read_append_list_left' b l _ h
#align buffer.read_append_list_left Buffer.read_append_list_left

@[simp]
theorem read_append_list_right (b : Buffer α) (l : List α) {i : ℕ} (h : i < l.length) :
    (b.appendList l).read ⟨b.size + i, by simp [h]⟩ = l.nthLe i h :=
  by
  induction' l with hd tl hl generalizing b i
  · exact absurd i.zero_le (not_le_of_lt h)
  · convert_to ((b.push_back hd).appendList tl).read _ = _
    cases i
    · convert read_append_list_left _ _ _ <;> simp
    · rw [List.length, Nat.succ_lt_succ_iff] at h
      have : b.size + i.succ = (b.push_back hd).size + i := by
        simp [add_comm, add_left_comm, Nat.succ_eq_add_one]
      convert hl (b.push_back hd) h using 1
      simpa [Nat.add_succ, Nat.succ_add]
#align buffer.read_append_list_right Buffer.read_append_list_right

theorem read_to_buffer' (l : List α) {i : ℕ} (h : i < l.toBuffer.size) (h' : i < l.length) :
    l.toBuffer.read ⟨i, h⟩ = l.nthLe i h' :=
  by
  cases' l with hd tl
  · simpa using h'
  · have hi : i < ([hd].toBuffer.appendList tl).size := by simpa [add_comm] using h
    convert_to ([hd].toBuffer.appendList tl).read ⟨i, hi⟩ = _
    cases i
    · convert read_append_list_left _ _ _
      simp
    · rw [List.nthLe]
      convert read_append_list_right _ _ _
      simp [Nat.succ_eq_add_one, add_comm]
#align buffer.read_to_buffer' Buffer.read_to_buffer'

@[simp]
theorem read_to_buffer (l : List α) (i) :
    l.toBuffer.read i =
      l.nthLe i
        (by
          convert i.property
          simp) :=
  by
  convert read_to_buffer' _ _ _
  · simp
  · simpa using i.property
#align buffer.read_to_buffer Buffer.read_to_buffer

theorem nth_le_to_list' (b : Buffer α) {i : ℕ} (h h') : b.toList.nthLe i h = b.read ⟨i, h'⟩ :=
  by
  have : b.to_list.to_buffer.read ⟨i, by simpa using h'⟩ = b.read ⟨i, h'⟩ := by
    congr 1 <;> simp [Fin.heq_ext_iff]
  simp [← this]
#align buffer.nth_le_to_list' Buffer.nth_le_to_list'

theorem nth_le_to_list (b : Buffer α) {i : ℕ} (h) :
    b.toList.nthLe i h = b.read ⟨i, by simpa using h⟩ :=
  nth_le_to_list' _ _ _
#align buffer.nth_le_to_list Buffer.nth_le_to_list

theorem read_eq_nth_le_to_list (b : Buffer α) (i) : b.read i = b.toList.nthLe i (by simp) := by
  simp [nth_le_to_list]
#align buffer.read_eq_nth_le_to_list Buffer.read_eq_nth_le_to_list

theorem read_singleton (c : α) : [c].toBuffer.read ⟨0, by simp⟩ = c := by simp
#align buffer.read_singleton Buffer.read_singleton

/-- The natural equivalence between lists and buffers, using
`list.to_buffer` and `buffer.to_list`. -/
def listEquivBuffer (α : Type _) : List α ≃ Buffer α := by
  refine'
      { toFun := List.toBuffer
        invFun := Buffer.toList.. } <;>
    simp [left_inverse, Function.RightInverse]
#align buffer.list_equiv_buffer Buffer.listEquivBuffer

instance : Traversable Buffer :=
  Equiv.traversable listEquivBuffer

instance : IsLawfulTraversable Buffer :=
  Equiv.isLawfulTraversable listEquivBuffer

/-- A convenience wrapper around `read` that just fails if the index is out of bounds.
-/
unsafe def read_t (b : Buffer α) (i : ℕ) : tactic α :=
  if h : i < b.size then return <| b.read (Fin.mk i h) else tactic.fail "invalid buffer access"
#align buffer.read_t buffer.read_t

end Buffer

