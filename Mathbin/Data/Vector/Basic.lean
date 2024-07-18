/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.Vector.Defs
import Data.List.Nodup
import Data.List.OfFn
import Control.Applicative
import Meta.Univs

#align_import data.vector.basic from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# Additional theorems and definitions about the `vector` type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file introduces the infix notation `::ᵥ` for `vector.cons`.
-/


universe u

variable {n : ℕ}

namespace Mathlib.Vector

variable {α : Type _}

infixr:67 " ::ᵥ " => Mathlib.Vector.cons

attribute [simp] head_cons tail_cons

instance [Inhabited α] : Inhabited (Mathlib.Vector α n) :=
  ⟨Mathlib.Vector.ofFn default⟩

#print Mathlib.Vector.toList_injective /-
theorem Mathlib.Vector.toList_injective : Function.Injective (@Mathlib.Vector.toList α n) :=
  Subtype.val_injective
#align vector.to_list_injective Mathlib.Vector.toList_injective
-/

#print Mathlib.Vector.ext /-
/-- Two `v w : vector α n` are equal iff they are equal at every single index. -/
@[ext]
theorem Mathlib.Vector.ext :
    ∀ {v w : Mathlib.Vector α n} (h : ∀ m : Fin n, Mathlib.Vector.get v m = Mathlib.Vector.get w m),
      v = w
  | ⟨v, hv⟩, ⟨w, hw⟩, h =>
    Subtype.eq (List.ext_nthLe (by rw [hv, hw]) fun m hm hn => h ⟨m, hv ▸ hm⟩)
#align vector.ext Mathlib.Vector.ext
-/

#print Mathlib.Vector.replicate /-
/-- A vector with `n` elements `a`. -/
def Mathlib.Vector.replicate (n : ℕ) (a : α) : Mathlib.Vector α n :=
  ⟨List.replicate n a, List.length_replicate n a⟩
#align vector.replicate Mathlib.Vector.replicate
-/

#print Mathlib.Vector.zero_subsingleton /-
/-- The empty `vector` is a `subsingleton`. -/
instance Mathlib.Vector.zero_subsingleton : Subsingleton (Mathlib.Vector α 0) :=
  ⟨fun _ _ => Mathlib.Vector.ext fun m => Fin.elim0 m⟩
#align vector.zero_subsingleton Mathlib.Vector.zero_subsingleton
-/

#print Mathlib.Vector.cons_val /-
@[simp]
theorem Mathlib.Vector.cons_val (a : α) : ∀ v : Mathlib.Vector α n, (a ::ᵥ v).val = a :: v.val
  | ⟨_, _⟩ => rfl
#align vector.cons_val Mathlib.Vector.cons_val
-/

/- warning: vector.cons_head clashes with vector.head_cons -> Mathlib.Vector.head_cons
Case conversion may be inaccurate. Consider using '#align vector.cons_head Mathlib.Vector.head_consₓ'. -/
#print Mathlib.Vector.head_cons /-
@[simp]
theorem Mathlib.Vector.head_cons (a : α) : ∀ v : Mathlib.Vector α n, (a ::ᵥ v).headI = a
  | ⟨_, _⟩ => rfl
#align vector.cons_head Mathlib.Vector.head_cons
-/

/- warning: vector.cons_tail clashes with vector.tail_cons -> Mathlib.Vector.tail_cons
Case conversion may be inaccurate. Consider using '#align vector.cons_tail Mathlib.Vector.tail_consₓ'. -/
#print Mathlib.Vector.tail_cons /-
@[simp]
theorem Mathlib.Vector.tail_cons (a : α) : ∀ v : Mathlib.Vector α n, (a ::ᵥ v).tail = v
  | ⟨_, _⟩ => rfl
#align vector.cons_tail Mathlib.Vector.tail_cons
-/

#print Mathlib.Vector.eq_cons_iff /-
theorem Mathlib.Vector.eq_cons_iff (a : α) (v : Mathlib.Vector α n.succ) (v' : Mathlib.Vector α n) :
    v = a ::ᵥ v' ↔ v.headI = a ∧ v.tail = v' :=
  ⟨fun h => h.symm ▸ ⟨Mathlib.Vector.head_cons a v', Mathlib.Vector.tail_cons a v'⟩, fun h =>
    trans (Mathlib.Vector.cons_head_tail v).symm (by rw [h.1, h.2])⟩
#align vector.eq_cons_iff Mathlib.Vector.eq_cons_iff
-/

#print Mathlib.Vector.ne_cons_iff /-
theorem Mathlib.Vector.ne_cons_iff (a : α) (v : Mathlib.Vector α n.succ) (v' : Mathlib.Vector α n) :
    v ≠ a ::ᵥ v' ↔ v.headI ≠ a ∨ v.tail ≠ v' := by rw [Ne.def, eq_cons_iff a v v', not_and_or]
#align vector.ne_cons_iff Mathlib.Vector.ne_cons_iff
-/

#print Mathlib.Vector.exists_eq_cons /-
theorem Mathlib.Vector.exists_eq_cons (v : Mathlib.Vector α n.succ) :
    ∃ (a : α) (as : Mathlib.Vector α n), v = a ::ᵥ as :=
  ⟨v.headI, v.tail, (Mathlib.Vector.eq_cons_iff v.headI v v.tail).2 ⟨rfl, rfl⟩⟩
#align vector.exists_eq_cons Mathlib.Vector.exists_eq_cons
-/

#print Mathlib.Vector.toList_ofFn /-
@[simp]
theorem Mathlib.Vector.toList_ofFn :
    ∀ {n} (f : Fin n → α), Mathlib.Vector.toList (Mathlib.Vector.ofFn f) = List.ofFn f
  | 0, f => rfl
  | n + 1, f => by rw [of_fn, List.ofFn_succ, to_list_cons, to_list_of_fn]
#align vector.to_list_of_fn Mathlib.Vector.toList_ofFn
-/

#print Mathlib.Vector.mk_toList /-
@[simp]
theorem Mathlib.Vector.mk_toList :
    ∀ (v : Mathlib.Vector α n) (h), (⟨Mathlib.Vector.toList v, h⟩ : Mathlib.Vector α n) = v
  | ⟨l, h₁⟩, h₂ => rfl
#align vector.mk_to_list Mathlib.Vector.mk_toList
-/

@[simp]
theorem Mathlib.Vector.length_coe (v : Mathlib.Vector α n) :
    ((coe : { l : List α // l.length = n } → List α) v).length = n :=
  v.2
#align vector.length_coe Mathlib.Vector.length_coe

#print Mathlib.Vector.toList_map /-
@[simp]
theorem Mathlib.Vector.toList_map {β : Type _} (v : Mathlib.Vector α n) (f : α → β) :
    (v.map f).toList = v.toList.map f := by cases v <;> rfl
#align vector.to_list_map Mathlib.Vector.toList_map
-/

#print Mathlib.Vector.head_map /-
@[simp]
theorem Mathlib.Vector.head_map {β : Type _} (v : Mathlib.Vector α (n + 1)) (f : α → β) :
    (v.map f).headI = f v.headI :=
  by
  obtain ⟨a, v', h⟩ := Mathlib.Vector.exists_eq_cons v
  rw [h, map_cons, head_cons, head_cons]
#align vector.head_map Mathlib.Vector.head_map
-/

#print Mathlib.Vector.tail_map /-
@[simp]
theorem Mathlib.Vector.tail_map {β : Type _} (v : Mathlib.Vector α (n + 1)) (f : α → β) :
    (v.map f).tail = v.tail.map f :=
  by
  obtain ⟨a, v', h⟩ := Mathlib.Vector.exists_eq_cons v
  rw [h, map_cons, tail_cons, tail_cons]
#align vector.tail_map Mathlib.Vector.tail_map
-/

theorem Mathlib.Vector.get_eq_get :
    ∀ (v : Mathlib.Vector α n) (i),
      Mathlib.Vector.get v i = v.toList.nthLe i.1 (by rw [to_list_length] <;> exact i.2)
  | ⟨l, h⟩, i => rfl
#align vector.nth_eq_nth_le Mathlib.Vector.get_eq_getₓ

/- warning: vector.nth_replicate clashes with vector.nth_repeat -> Mathlib.Vector.get_replicate
Case conversion may be inaccurate. Consider using '#align vector.nth_replicate Mathlib.Vector.get_replicateₓ'. -/
#print Mathlib.Vector.get_replicate /-
@[simp]
theorem Mathlib.Vector.get_replicate (a : α) (i : Fin n) :
    (Mathlib.Vector.replicate n a).get? i = a :=
  List.get_replicate _ _
#align vector.nth_replicate Mathlib.Vector.get_replicate
-/

#print Mathlib.Vector.get_map /-
@[simp]
theorem Mathlib.Vector.get_map {β : Type _} (v : Mathlib.Vector α n) (f : α → β) (i : Fin n) :
    (v.map f).get? i = f (v.get? i) := by simp [nth_eq_nth_le]
#align vector.nth_map Mathlib.Vector.get_map
-/

#print Mathlib.Vector.get_ofFn /-
@[simp]
theorem Mathlib.Vector.get_ofFn {n} (f : Fin n → α) (i) :
    Mathlib.Vector.get (Mathlib.Vector.ofFn f) i = f i := by
  rw [nth_eq_nth_le, ← List.nthLe_ofFn f] <;> congr <;> apply to_list_of_fn
#align vector.nth_of_fn Mathlib.Vector.get_ofFn
-/

#print Mathlib.Vector.ofFn_get /-
@[simp]
theorem Mathlib.Vector.ofFn_get (v : Mathlib.Vector α n) :
    Mathlib.Vector.ofFn (Mathlib.Vector.get v) = v :=
  by
  rcases v with ⟨l, rfl⟩
  apply to_list_injective
  change nth ⟨l, Eq.refl _⟩ with fun i => nth ⟨l, rfl⟩ i
  simpa only [to_list_of_fn] using List.ofFn_nthLe _
#align vector.of_fn_nth Mathlib.Vector.ofFn_get
-/

#print Equiv.vectorEquivFin /-
/-- The natural equivalence between length-`n` vectors and functions from `fin n`. -/
def Equiv.vectorEquivFin (α : Type _) (n : ℕ) : Mathlib.Vector α n ≃ (Fin n → α) :=
  ⟨Mathlib.Vector.get, Mathlib.Vector.ofFn, Mathlib.Vector.ofFn_get, fun f =>
    funext <| Mathlib.Vector.get_ofFn f⟩
#align equiv.vector_equiv_fin Equiv.vectorEquivFin
-/

#print Mathlib.Vector.get_tail /-
theorem Mathlib.Vector.get_tail (x : Mathlib.Vector α n) (i) :
    x.tail.get? i = x.get? ⟨i.1 + 1, lt_tsub_iff_right.mp i.2⟩ := by
  rcases x with ⟨_ | _, h⟩ <;> rfl
#align vector.nth_tail Mathlib.Vector.get_tail
-/

#print Mathlib.Vector.get_tail_succ /-
@[simp]
theorem Mathlib.Vector.get_tail_succ :
    ∀ (v : Mathlib.Vector α n.succ) (i : Fin n),
      Mathlib.Vector.get (Mathlib.Vector.tail v) i = Mathlib.Vector.get v i.succ
  | ⟨a :: l, e⟩, ⟨i, h⟩ => by simp [nth_eq_nth_le] <;> rfl
#align vector.nth_tail_succ Mathlib.Vector.get_tail_succ
-/

#print Mathlib.Vector.tail_val /-
@[simp]
theorem Mathlib.Vector.tail_val : ∀ v : Mathlib.Vector α n.succ, v.tail.val = v.val.tail
  | ⟨a :: l, e⟩ => rfl
#align vector.tail_val Mathlib.Vector.tail_val
-/

#print Mathlib.Vector.tail_nil /-
/-- The `tail` of a `nil` vector is `nil`. -/
@[simp]
theorem Mathlib.Vector.tail_nil : (@Mathlib.Vector.nil α).tail = Mathlib.Vector.nil :=
  rfl
#align vector.tail_nil Mathlib.Vector.tail_nil
-/

#print Mathlib.Vector.singleton_tail /-
/-- The `tail` of a vector made up of one element is `nil`. -/
@[simp]
theorem Mathlib.Vector.singleton_tail (v : Mathlib.Vector α 1) : v.tail = Mathlib.Vector.nil := by
  simp only [← cons_head_tail, eq_iff_true_of_subsingleton]
#align vector.singleton_tail Mathlib.Vector.singleton_tail
-/

#print Mathlib.Vector.tail_ofFn /-
@[simp]
theorem Mathlib.Vector.tail_ofFn {n : ℕ} (f : Fin n.succ → α) :
    Mathlib.Vector.tail (Mathlib.Vector.ofFn f) = Mathlib.Vector.ofFn fun i => f i.succ :=
  (Mathlib.Vector.ofFn_get _).symm.trans <| by congr; funext i; cases i; simp
#align vector.tail_of_fn Mathlib.Vector.tail_ofFn
-/

#print Mathlib.Vector.toList_empty /-
@[simp]
theorem Mathlib.Vector.toList_empty (v : Mathlib.Vector α 0) : v.toList = [] :=
  List.length_eq_zero.mp v.2
#align vector.to_list_empty Mathlib.Vector.toList_empty
-/

#print Mathlib.Vector.toList_singleton /-
/-- The list that makes up a `vector` made up of a single element,
retrieved via `to_list`, is equal to the list of that single element. -/
@[simp]
theorem Mathlib.Vector.toList_singleton (v : Mathlib.Vector α 1) : v.toList = [v.headI] :=
  by
  rw [← v.cons_head_tail]
  simp only [to_list_cons, to_list_nil, cons_head, eq_self_iff_true, and_self_iff, singleton_tail]
#align vector.to_list_singleton Mathlib.Vector.toList_singleton
-/

#print Mathlib.Vector.empty_toList_eq_ff /-
@[simp]
theorem Mathlib.Vector.empty_toList_eq_ff (v : Mathlib.Vector α (n + 1)) : v.toList.Empty = false :=
  match v with
  | ⟨a :: as, _⟩ => rfl
#align vector.empty_to_list_eq_ff Mathlib.Vector.empty_toList_eq_ff
-/

#print Mathlib.Vector.not_empty_toList /-
theorem Mathlib.Vector.not_empty_toList (v : Mathlib.Vector α (n + 1)) : ¬v.toList.Empty := by
  simp only [empty_to_list_eq_ff, Bool.coe_sort_false, not_false_iff]
#align vector.not_empty_to_list Mathlib.Vector.not_empty_toList
-/

#print Mathlib.Vector.map_id /-
/-- Mapping under `id` does not change a vector. -/
@[simp]
theorem Mathlib.Vector.map_id {n : ℕ} (v : Mathlib.Vector α n) : Mathlib.Vector.map id v = v :=
  Mathlib.Vector.eq _ _ (by simp only [List.map_id, Mathlib.Vector.toList_map])
#align vector.map_id Mathlib.Vector.map_id
-/

#print Mathlib.Vector.nodup_iff_injective_get /-
theorem Mathlib.Vector.nodup_iff_injective_get {v : Mathlib.Vector α n} :
    v.toList.Nodup ↔ Function.Injective v.get? :=
  by
  cases' v with l hl
  subst hl
  simp only [List.nodup_iff_nthLe_inj]
  constructor
  · intro h i j hij
    cases i; cases j; ext; apply h; simpa
  · intro h i j hi hj hij
    have := @h ⟨i, hi⟩ ⟨j, hj⟩; simp [nth_eq_nth_le] at *; tauto
#align vector.nodup_iff_nth_inj Mathlib.Vector.nodup_iff_injective_get
-/

#print Mathlib.Vector.head?_toList /-
theorem Mathlib.Vector.head?_toList :
    ∀ v : Mathlib.Vector α n.succ, (Mathlib.Vector.toList v).head? = some (Mathlib.Vector.head v)
  | ⟨a :: l, e⟩ => rfl
#align vector.head'_to_list Mathlib.Vector.head?_toList
-/

#print Mathlib.Vector.reverse /-
/-- Reverse a vector. -/
def Mathlib.Vector.reverse (v : Mathlib.Vector α n) : Mathlib.Vector α n :=
  ⟨v.toList.reverse, by simp⟩
#align vector.reverse Mathlib.Vector.reverse
-/

#print Mathlib.Vector.toList_reverse /-
/-- The `list` of a vector after a `reverse`, retrieved by `to_list` is equal
to the `list.reverse` after retrieving a vector's `to_list`. -/
theorem Mathlib.Vector.toList_reverse {v : Mathlib.Vector α n} :
    v.reverse.toList = v.toList.reverse :=
  rfl
#align vector.to_list_reverse Mathlib.Vector.toList_reverse
-/

#print Mathlib.Vector.reverse_reverse /-
@[simp]
theorem Mathlib.Vector.reverse_reverse {v : Mathlib.Vector α n} : v.reverse.reverse = v := by
  cases v; simp [Mathlib.Vector.reverse]
#align vector.reverse_reverse Mathlib.Vector.reverse_reverse
-/

#print Mathlib.Vector.get_zero /-
@[simp]
theorem Mathlib.Vector.get_zero :
    ∀ v : Mathlib.Vector α n.succ, Mathlib.Vector.get v 0 = Mathlib.Vector.head v
  | ⟨a :: l, e⟩ => rfl
#align vector.nth_zero Mathlib.Vector.get_zero
-/

#print Mathlib.Vector.head_ofFn /-
@[simp]
theorem Mathlib.Vector.head_ofFn {n : ℕ} (f : Fin n.succ → α) :
    Mathlib.Vector.head (Mathlib.Vector.ofFn f) = f 0 := by rw [← nth_zero, nth_of_fn]
#align vector.head_of_fn Mathlib.Vector.head_ofFn
-/

#print Mathlib.Vector.get_cons_zero /-
@[simp]
theorem Mathlib.Vector.get_cons_zero (a : α) (v : Mathlib.Vector α n) :
    Mathlib.Vector.get (a ::ᵥ v) 0 = a := by simp [nth_zero]
#align vector.nth_cons_zero Mathlib.Vector.get_cons_zero
-/

#print Mathlib.Vector.get_cons_nil /-
/-- Accessing the `nth` element of a vector made up
of one element `x : α` is `x` itself. -/
@[simp]
theorem Mathlib.Vector.get_cons_nil {ix : Fin 1} (x : α) :
    Mathlib.Vector.get (x ::ᵥ Mathlib.Vector.nil) ix = x := by convert nth_cons_zero x nil
#align vector.nth_cons_nil Mathlib.Vector.get_cons_nil
-/

#print Mathlib.Vector.get_cons_succ /-
@[simp]
theorem Mathlib.Vector.get_cons_succ (a : α) (v : Mathlib.Vector α n) (i : Fin n) :
    Mathlib.Vector.get (a ::ᵥ v) i.succ = Mathlib.Vector.get v i := by
  rw [← nth_tail_succ, tail_cons]
#align vector.nth_cons_succ Mathlib.Vector.get_cons_succ
-/

#print Mathlib.Vector.last /-
/-- The last element of a `vector`, given that the vector is at least one element. -/
def Mathlib.Vector.last (v : Mathlib.Vector α (n + 1)) : α :=
  v.get? (Fin.last n)
#align vector.last Mathlib.Vector.last
-/

#print Mathlib.Vector.last_def /-
/-- The last element of a `vector`, given that the vector is at least one element. -/
theorem Mathlib.Vector.last_def {v : Mathlib.Vector α (n + 1)} : v.getLast = v.get? (Fin.last n) :=
  rfl
#align vector.last_def Mathlib.Vector.last_def
-/

#print Mathlib.Vector.reverse_get_zero /-
/-- The `last` element of a vector is the `head` of the `reverse` vector. -/
theorem Mathlib.Vector.reverse_get_zero {v : Mathlib.Vector α (n + 1)} :
    v.reverse.headI = v.getLast :=
  by
  have : 0 = v.to_list.length - 1 - n := by
    simp only [Nat.add_succ_sub_one, add_zero, to_list_length, tsub_self, List.length_reverse]
  rw [← nth_zero, last_def, nth_eq_nth_le, nth_eq_nth_le]
  simp_rw [to_list_reverse, Fin.val_eq_coe, Fin.val_last, Fin.val_zero, this]
  rw [List.nthLe_reverse]
#align vector.reverse_nth_zero Mathlib.Vector.reverse_get_zero
-/

section Scan

variable {β : Type _}

variable (f : β → α → β) (b : β)

variable (v : Mathlib.Vector α n)

#print Mathlib.Vector.scanl /-
/-- Construct a `vector β (n + 1)` from a `vector α n` by scanning `f : β → α → β`
from the "left", that is, from 0 to `fin.last n`, using `b : β` as the starting value.
-/
def Mathlib.Vector.scanl : Mathlib.Vector β (n + 1) :=
  ⟨List.scanl f b v.toList, by rw [List.length_scanl, to_list_length]⟩
#align vector.scanl Mathlib.Vector.scanl
-/

#print Mathlib.Vector.scanl_nil /-
/-- Providing an empty vector to `scanl` gives the starting value `b : β`. -/
@[simp]
theorem Mathlib.Vector.scanl_nil :
    Mathlib.Vector.scanl f b Mathlib.Vector.nil = b ::ᵥ Mathlib.Vector.nil :=
  rfl
#align vector.scanl_nil Mathlib.Vector.scanl_nil
-/

#print Mathlib.Vector.scanl_cons /-
/-- The recursive step of `scanl` splits a vector `x ::ᵥ v : vector α (n + 1)`
into the provided starting value `b : β` and the recursed `scanl`
`f b x : β` as the starting value.

This lemma is the `cons` version of `scanl_nth`.
-/
@[simp]
theorem Mathlib.Vector.scanl_cons (x : α) :
    Mathlib.Vector.scanl f b (x ::ᵥ v) = b ::ᵥ Mathlib.Vector.scanl f (f b x) v := by
  simpa only [scanl, to_list_cons]
#align vector.scanl_cons Mathlib.Vector.scanl_cons
-/

#print Mathlib.Vector.scanl_val /-
/-- The underlying `list` of a `vector` after a `scanl` is the `list.scanl`
of the underlying `list` of the original `vector`.
-/
@[simp]
theorem Mathlib.Vector.scanl_val :
    ∀ {v : Mathlib.Vector α n}, (Mathlib.Vector.scanl f b v).val = List.scanl f b v.val
  | ⟨l, hl⟩ => rfl
#align vector.scanl_val Mathlib.Vector.scanl_val
-/

#print Mathlib.Vector.toList_scanl /-
/-- The `to_list` of a `vector` after a `scanl` is the `list.scanl`
of the `to_list` of the original `vector`.
-/
@[simp]
theorem Mathlib.Vector.toList_scanl :
    (Mathlib.Vector.scanl f b v).toList = List.scanl f b v.toList :=
  rfl
#align vector.to_list_scanl Mathlib.Vector.toList_scanl
-/

#print Mathlib.Vector.scanl_singleton /-
/-- The recursive step of `scanl` splits a vector made up of a single element
`x ::ᵥ nil : vector α 1` into a `vector` of the provided starting value `b : β`
and the mapped `f b x : β` as the last value.
-/
@[simp]
theorem Mathlib.Vector.scanl_singleton (v : Mathlib.Vector α 1) :
    Mathlib.Vector.scanl f b v = b ::ᵥ f b v.headI ::ᵥ Mathlib.Vector.nil :=
  by
  rw [← cons_head_tail v]
  simp only [scanl_cons, scanl_nil, cons_head, singleton_tail]
#align vector.scanl_singleton Mathlib.Vector.scanl_singleton
-/

#print Mathlib.Vector.scanl_head /-
/-- The first element of `scanl` of a vector `v : vector α n`,
retrieved via `head`, is the starting value `b : β`.
-/
@[simp]
theorem Mathlib.Vector.scanl_head : (Mathlib.Vector.scanl f b v).headI = b :=
  by
  cases n
  · have : v = nil := by simp only [eq_iff_true_of_subsingleton]
    simp only [this, scanl_nil, cons_head]
  · rw [← cons_head_tail v]
    simp only [← nth_zero, nth_eq_nth_le, to_list_scanl, to_list_cons, List.scanl, Fin.val_zero',
      List.nthLe]
#align vector.scanl_head Mathlib.Vector.scanl_head
-/

#print Mathlib.Vector.scanl_get /-
/-- For an index `i : fin n`, the `nth` element of `scanl` of a
vector `v : vector α n` at `i.succ`, is equal to the application
function `f : β → α → β` of the `i.cast_succ` element of
`scanl f b v` and `nth v i`.

This lemma is the `nth` version of `scanl_cons`.
-/
@[simp]
theorem Mathlib.Vector.scanl_get (i : Fin n) :
    (Mathlib.Vector.scanl f b v).get? i.succ =
      f ((Mathlib.Vector.scanl f b v).get? i.cast_succ) (v.get? i) :=
  by
  cases n
  · exact finZeroElim i
  induction' n with n hn generalizing b
  · have i0 : i = 0 := by simp only [eq_iff_true_of_subsingleton]
    simpa only [scanl_singleton, i0, nth_zero]
  · rw [← cons_head_tail v, scanl_cons, nth_cons_succ]
    refine' Fin.cases _ _ i
    · simp only [nth_zero, scanl_head, Fin.castSucc_zero', cons_head]
    · intro i'
      simp only [hn, Fin.castSucc_fin_succ, nth_cons_succ]
#align vector.scanl_nth Mathlib.Vector.scanl_get
-/

end Scan

#print Mathlib.Vector.mOfFn /-
/-- Monadic analog of `vector.of_fn`.
Given a monadic function on `fin n`, return a `vector α n` inside the monad. -/
def Mathlib.Vector.mOfFn {m} [Monad m] {α : Type u} : ∀ {n}, (Fin n → m α) → m (Mathlib.Vector α n)
  | 0, f => pure Mathlib.Vector.nil
  | n + 1, f => do
    let a ← f 0
    let v ← m_of_fn fun i => f i.succ
    pure (a ::ᵥ v)
#align vector.m_of_fn Mathlib.Vector.mOfFn
-/

#print Mathlib.Vector.mOfFn_pure /-
theorem Mathlib.Vector.mOfFn_pure {m} [Monad m] [LawfulMonad m] {α} :
    ∀ {n} (f : Fin n → α),
      (@Mathlib.Vector.mOfFn m _ _ _ fun i => pure (f i)) = pure (Mathlib.Vector.ofFn f)
  | 0, f => rfl
  | n + 1, f => by simp [m_of_fn, @m_of_fn_pure n, of_fn]
#align vector.m_of_fn_pure Mathlib.Vector.mOfFn_pure
-/

#print Mathlib.Vector.mmap /-
/-- Apply a monadic function to each component of a vector,
returning a vector inside the monad. -/
def Mathlib.Vector.mmap {m} [Monad m] {α} {β : Type u} (f : α → m β) :
    ∀ {n}, Mathlib.Vector α n → m (Mathlib.Vector β n)
  | 0, xs => pure Mathlib.Vector.nil
  | n + 1, xs => do
    let h' ← f xs.headI
    let t' ← @mmap n xs.tail
    pure (h' ::ᵥ t')
#align vector.mmap Mathlib.Vector.mmap
-/

#print Mathlib.Vector.mmap_nil /-
@[simp]
theorem Mathlib.Vector.mmap_nil {m} [Monad m] {α β} (f : α → m β) :
    Mathlib.Vector.mmap f Mathlib.Vector.nil = pure Mathlib.Vector.nil :=
  rfl
#align vector.mmap_nil Mathlib.Vector.mmap_nil
-/

#print Mathlib.Vector.mmap_cons /-
@[simp]
theorem Mathlib.Vector.mmap_cons {m} [Monad m] {α β} (f : α → m β) (a) :
    ∀ {n} (v : Mathlib.Vector α n),
      Mathlib.Vector.mmap f (a ::ᵥ v) = do
        let h' ← f a
        let t' ← Mathlib.Vector.mmap f v
        pure (h' ::ᵥ t')
  | _, ⟨l, rfl⟩ => rfl
#align vector.mmap_cons Mathlib.Vector.mmap_cons
-/

#print Mathlib.Vector.inductionOn /-
/-- Define `C v` by induction on `v : vector α n`.

This function has two arguments: `h_nil` handles the base case on `C nil`,
and `h_cons` defines the inductive step using `∀ x : α, C w → C (x ::ᵥ w)`.

This can be used as `induction v using vector.induction_on`. -/
@[elab_as_elim]
def Mathlib.Vector.inductionOn {C : ∀ {n : ℕ}, Mathlib.Vector α n → Sort _} {n : ℕ}
    (v : Mathlib.Vector α n) (h_nil : C Mathlib.Vector.nil)
    (h_cons : ∀ {n : ℕ} {x : α} {w : Mathlib.Vector α n}, C w → C (x ::ᵥ w)) : C v :=
  by
  induction' n with n ih generalizing v
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
  · rcases v with ⟨_ | ⟨a, v⟩, _⟩
    cases v_property
    apply @h_cons n _ ⟨v, (add_left_inj 1).mp v_property⟩
    apply ih
#align vector.induction_on Mathlib.Vector.inductionOn
-/

-- check that the above works with `induction ... using`
example (v : Mathlib.Vector α n) : True := by
  induction v using Mathlib.Vector.inductionOn <;> trivial

variable {β γ : Type _}

#print Mathlib.Vector.inductionOn₂ /-
/-- Define `C v w` by induction on a pair of vectors `v : vector α n` and `w : vector β n`. -/
@[elab_as_elim]
def Mathlib.Vector.inductionOn₂ {C : ∀ {n}, Mathlib.Vector α n → Mathlib.Vector β n → Sort _}
    (v : Mathlib.Vector α n) (w : Mathlib.Vector β n)
    (h_nil : C Mathlib.Vector.nil Mathlib.Vector.nil)
    (h_cons : ∀ {n a b} {x : Mathlib.Vector α n} {y}, C x y → C (a ::ᵥ x) (b ::ᵥ y)) : C v w :=
  by
  induction' n with n ih generalizing v w
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩; rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
  · rcases v with ⟨_ | ⟨a, v⟩, _⟩
    cases v_property
    rcases w with ⟨_ | ⟨b, w⟩, _⟩
    cases w_property
    apply @h_cons n _ _ ⟨v, (add_left_inj 1).mp v_property⟩ ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih
#align vector.induction_on₂ Mathlib.Vector.inductionOn₂
-/

#print Mathlib.Vector.inductionOn₃ /-
/-- Define `C u v w` by induction on a triplet of vectors
`u : vector α n`, `v : vector β n`, and `w : vector γ b`. -/
@[elab_as_elim]
def Mathlib.Vector.inductionOn₃
    {C : ∀ {n}, Mathlib.Vector α n → Mathlib.Vector β n → Mathlib.Vector γ n → Sort _}
    (u : Mathlib.Vector α n) (v : Mathlib.Vector β n) (w : Mathlib.Vector γ n)
    (h_nil : C Mathlib.Vector.nil Mathlib.Vector.nil Mathlib.Vector.nil)
    (h_cons :
      ∀ {n a b c} {x : Mathlib.Vector α n} {y z}, C x y z → C (a ::ᵥ x) (b ::ᵥ y) (c ::ᵥ z)) :
    C u v w := by
  induction' n with n ih generalizing u v w
  · rcases u with ⟨_ | ⟨-, -⟩, - | -⟩; rcases v with ⟨_ | ⟨-, -⟩, - | -⟩;
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
  · rcases u with ⟨_ | ⟨a, u⟩, _⟩
    cases u_property
    rcases v with ⟨_ | ⟨b, v⟩, _⟩
    cases v_property
    rcases w with ⟨_ | ⟨c, w⟩, _⟩
    cases w_property
    apply
      @h_cons n _ _ _ ⟨u, (add_left_inj 1).mp u_property⟩ ⟨v, (add_left_inj 1).mp v_property⟩
        ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih
#align vector.induction_on₃ Mathlib.Vector.inductionOn₃
-/

#print Mathlib.Vector.toArray /-
/-- Cast a vector to an array. -/
def Mathlib.Vector.toArray : Mathlib.Vector α n → Array' n α
  | ⟨xs, h⟩ => cast (by rw [h]) xs.toArray
#align vector.to_array Mathlib.Vector.toArray
-/

section InsertNth

variable {a : α}

#print Mathlib.Vector.insertNth /-
/-- `v.insert_nth a i` inserts `a` into the vector `v` at position `i`
(and shifting later components to the right). -/
def Mathlib.Vector.insertNth (a : α) (i : Fin (n + 1)) (v : Mathlib.Vector α n) :
    Mathlib.Vector α (n + 1) :=
  ⟨v.1.insertNth i a, by
    rw [List.length_insertNth, v.2]
    rw [v.2, ← Nat.succ_le_succ_iff]
    exact i.2⟩
#align vector.insert_nth Mathlib.Vector.insertNth
-/

#print Mathlib.Vector.insertNth_val /-
theorem Mathlib.Vector.insertNth_val {i : Fin (n + 1)} {v : Mathlib.Vector α n} :
    (v.insertNth a i).val = v.val.insertNth i.1 a :=
  rfl
#align vector.insert_nth_val Mathlib.Vector.insertNth_val
-/

#print Mathlib.Vector.eraseIdx_val /-
@[simp]
theorem Mathlib.Vector.eraseIdx_val {i : Fin n} :
    ∀ {v : Mathlib.Vector α n}, (Mathlib.Vector.eraseIdx i v).val = v.val.eraseIdx i
  | ⟨l, hl⟩ => rfl
#align vector.remove_nth_val Mathlib.Vector.eraseIdx_val
-/

#print Mathlib.Vector.eraseIdx_insertNth /-
theorem Mathlib.Vector.eraseIdx_insertNth {v : Mathlib.Vector α n} {i : Fin (n + 1)} :
    Mathlib.Vector.eraseIdx i (Mathlib.Vector.insertNth a i v) = v :=
  Subtype.eq <| List.eraseIdx_insertNth i.1 v.1
#align vector.remove_nth_insert_nth Mathlib.Vector.eraseIdx_insertNth
-/

#print Mathlib.Vector.eraseIdx_insertNth' /-
theorem Mathlib.Vector.eraseIdx_insertNth' {v : Mathlib.Vector α (n + 1)} :
    ∀ {i : Fin (n + 1)} {j : Fin (n + 2)},
      Mathlib.Vector.eraseIdx (j.succAboveOrderEmb i) (Mathlib.Vector.insertNth a j v) =
        Mathlib.Vector.insertNth a (i.predAbove j) (Mathlib.Vector.eraseIdx i v)
  | ⟨i, hi⟩, ⟨j, hj⟩ =>
    by
    dsimp [insert_nth, remove_nth, Fin.succAboveOrderEmb, Fin.predAbove]
    simp only [Subtype.mk_eq_mk]
    split_ifs
    · convert (List.insertNth_eraseIdx_of_ge i (j - 1) _ _ _).symm
      · convert (Nat.succ_pred_eq_of_pos _).symm; exact lt_of_le_of_lt (zero_le _) h
      · apply remove_nth_val
      · convert hi; exact v.2
      · exact Nat.le_pred_of_lt h
    · convert (List.insertNth_eraseIdx_of_le i j _ _ _).symm
      · apply remove_nth_val
      · convert hi; exact v.2
      · simpa using h
#align vector.remove_nth_insert_nth' Mathlib.Vector.eraseIdx_insertNth'
-/

#print Mathlib.Vector.insertNth_comm /-
theorem Mathlib.Vector.insertNth_comm (a b : α) (i j : Fin (n + 1)) (h : i ≤ j) :
    ∀ v : Mathlib.Vector α n,
      (v.insertNth a i).insertNth b j.succ = (v.insertNth b j).insertNth a i.cast_succ
  | ⟨l, hl⟩ => by
    refine' Subtype.eq _
    simp only [insert_nth_val, Fin.val_succ, Fin.castSuccEmb, Fin.val_eq_coe, Fin.coe_castAdd]
    apply List.insertNth_comm
    · assumption
    · rw [hl]; exact Nat.le_of_succ_le_succ j.2
#align vector.insert_nth_comm Mathlib.Vector.insertNth_comm
-/

end InsertNth

section UpdateNth

#print Mathlib.Vector.set /-
/-- `update_nth v n a` replaces the `n`th element of `v` with `a` -/
def Mathlib.Vector.set (v : Mathlib.Vector α n) (i : Fin n) (a : α) : Mathlib.Vector α n :=
  ⟨v.1.set i.1 a, by rw [List.length_set, v.2]⟩
#align vector.update_nth Mathlib.Vector.set
-/

#print Mathlib.Vector.toList_set /-
@[simp]
theorem Mathlib.Vector.toList_set (v : Mathlib.Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList = v.toList.set i a :=
  rfl
#align vector.to_list_update_nth Mathlib.Vector.toList_set
-/

#print Mathlib.Vector.get_set_same /-
@[simp]
theorem Mathlib.Vector.get_set_same (v : Mathlib.Vector α n) (i : Fin n) (a : α) :
    (v.set i a).get? i = a := by
  cases v <;> cases i <;> simp [Mathlib.Vector.set, Mathlib.Vector.get_eq_get]
#align vector.nth_update_nth_same Mathlib.Vector.get_set_same
-/

#print Mathlib.Vector.get_set_of_ne /-
theorem Mathlib.Vector.get_set_of_ne {v : Mathlib.Vector α n} {i j : Fin n} (h : i ≠ j) (a : α) :
    (v.set i a).get? j = v.get? j := by
  cases v <;> cases i <;> cases j <;>
    simp [Mathlib.Vector.set, Mathlib.Vector.get_eq_get, List.getElem_set_of_ne (Fin.vne_of_ne h)]
#align vector.nth_update_nth_of_ne Mathlib.Vector.get_set_of_ne
-/

#print Mathlib.Vector.get_set_eq_if /-
theorem Mathlib.Vector.get_set_eq_if {v : Mathlib.Vector α n} {i j : Fin n} (a : α) :
    (v.set i a).get? j = if i = j then a else v.get? j := by
  split_ifs <;> try simp [*] <;> try rw [nth_update_nth_of_ne] <;> assumption
#align vector.nth_update_nth_eq_if Mathlib.Vector.get_set_eq_if
-/

#print Mathlib.Vector.prod_set /-
@[to_additive]
theorem Mathlib.Vector.prod_set [Monoid α] (v : Mathlib.Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList.Prod = (v.take i).toList.Prod * a * (v.drop (i + 1)).toList.Prod :=
  by
  refine' (List.prod_set v.to_list i a).trans _
  have : ↑i < v.to_list.length := lt_of_lt_of_le i.2 (le_of_eq v.2.symm)
  simp_all
#align vector.prod_update_nth Mathlib.Vector.prod_set
#align vector.sum_update_nth Mathlib.Vector.sum_set
-/

#print Mathlib.Vector.prod_set' /-
@[to_additive]
theorem Mathlib.Vector.prod_set' [CommGroup α] (v : Mathlib.Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList.Prod = v.toList.Prod * (v.get? i)⁻¹ * a :=
  by
  refine' (List.prod_set' v.to_list i a).trans _
  have : ↑i < v.to_list.length := lt_of_lt_of_le i.2 (le_of_eq v.2.symm)
  simp [this, nth_eq_nth_le, mul_assoc]
#align vector.prod_update_nth' Mathlib.Vector.prod_set'
-/

end UpdateNth

end Mathlib.Vector

namespace Mathlib.Vector

section Traverse

variable {F G : Type u → Type u}

variable [Applicative F] [Applicative G]

open Applicative Functor

open List (cons)

open Nat

private def traverse_aux {α β : Type u} (f : α → F β) : ∀ x : List α, F (Mathlib.Vector β x.length)
  | [] => pure Mathlib.Vector.nil
  | x :: xs => Mathlib.Vector.cons <$> f x <*> traverse_aux xs

#print Mathlib.Vector.traverse /-
/-- Apply an applicative function to each component of a vector. -/
protected def Mathlib.Vector.traverse {α β : Type u} (f : α → F β) :
    Mathlib.Vector α n → F (Mathlib.Vector β n)
  | ⟨v, Hv⟩ => cast (by rw [Hv]) <| traverseAux f v
#align vector.traverse Mathlib.Vector.traverse
-/

section

variable {α β : Type u}

#print Mathlib.Vector.traverse_def /-
@[simp]
protected theorem Mathlib.Vector.traverse_def (f : α → F β) (x : α) :
    ∀ xs : Mathlib.Vector α n,
      (x ::ᵥ xs).traverse f = Mathlib.Vector.cons <$> f x <*> xs.traverse f :=
  by rintro ⟨xs, rfl⟩ <;> rfl
#align vector.traverse_def Mathlib.Vector.traverse_def
-/

#print Mathlib.Vector.id_traverse /-
protected theorem Mathlib.Vector.id_traverse : ∀ x : Mathlib.Vector α n, x.traverse id.mk = x :=
  by
  rintro ⟨x, rfl⟩; dsimp [Mathlib.Vector.traverse, cast]
  induction' x with x xs IH; · rfl
  simp! [IH]; rfl
#align vector.id_traverse Mathlib.Vector.id_traverse
-/

end

open Function

variable [LawfulApplicative F] [LawfulApplicative G]

variable {α β γ : Type u}

#print Mathlib.Vector.comp_traverse /-
-- We need to turn off the linter here as
-- the `is_lawful_traversable` instance below expects a particular signature.
@[nolint unused_arguments]
protected theorem Mathlib.Vector.comp_traverse (f : β → F γ) (g : α → G β) :
    ∀ x : Mathlib.Vector α n,
      Mathlib.Vector.traverse (Comp.mk ∘ Functor.map f ∘ g) x =
        Comp.mk (Mathlib.Vector.traverse f <$> Mathlib.Vector.traverse g x) :=
  by
  rintro ⟨x, rfl⟩ <;> dsimp [Mathlib.Vector.traverse, cast] <;> induction' x with x xs <;>
      simp! [cast, *, functor_norm] <;>
    [rfl; simp [(· ∘ ·)]]
#align vector.comp_traverse Mathlib.Vector.comp_traverse
-/

#print Mathlib.Vector.traverse_eq_map_id /-
protected theorem Mathlib.Vector.traverse_eq_map_id {α β} (f : α → β) :
    ∀ x : Mathlib.Vector α n, x.traverse (id.mk ∘ f) = id.mk (Mathlib.Vector.map f x) := by
  rintro ⟨x, rfl⟩ <;> simp! <;> induction x <;> simp! [*, functor_norm] <;> rfl
#align vector.traverse_eq_map_id Mathlib.Vector.traverse_eq_map_id
-/

variable (η : ApplicativeTransformation F G)

#print Mathlib.Vector.naturality /-
protected theorem Mathlib.Vector.naturality {α β : Type _} (f : α → F β) :
    ∀ x : Mathlib.Vector α n, η (x.traverse f) = x.traverse (@η _ ∘ f) := by
  rintro ⟨x, rfl⟩ <;> simp! [cast] <;> induction' x with x xs IH <;> simp! [*, functor_norm]
#align vector.naturality Mathlib.Vector.naturality
-/

end Traverse

instance : Traversable.{u} (flip Mathlib.Vector n)
    where
  traverse := @Mathlib.Vector.traverse n
  map α β := @Mathlib.Vector.map.{u, u} α β n

instance : LawfulTraversable.{u} (flip Mathlib.Vector n)
    where
  id_traverse := @Mathlib.Vector.id_traverse n
  comp_traverse := @Mathlib.Vector.comp_traverse n
  traverse_eq_map_id := @Mathlib.Vector.traverse_eq_map_id n
  naturality := @Mathlib.Vector.naturality n
  id_map := by intros <;> cases x <;> simp! [(· <$> ·)]
  comp_map := by intros <;> cases x <;> simp! [(· <$> ·)]

/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[] -/
/- ././././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[] -/
unsafe instance reflect [Lean.ToLevel.{u}] {α : Type u} [has_reflect α] [reflected _ α] {n : ℕ} :
    has_reflect (Mathlib.Vector α n) := fun v =>
  @Mathlib.Vector.inductionOn α (fun n => reflected _) n v
    ((by
          trace
            "././././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[]" :
          reflected _ @Mathlib.Vector.nil.{u}).subst
      q(α))
    fun n x xs ih =>
    (by
          trace
            "././././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `reflect_name #[]" :
          reflected _ @Mathlib.Vector.cons.{u}).subst₄
      q(α) q(n) q(x) ih
#align vector.reflect vector.reflect

end Mathlib.Vector

