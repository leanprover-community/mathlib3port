/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.vector.basic
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Leanbin.Data.Vector
import Mathbin.Data.List.Nodup
import Mathbin.Data.List.OfFn
import Mathbin.Control.Applicative
import Mathbin.Meta.Univs

/-!
# Additional theorems and definitions about the `vector` type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file introduces the infix notation `::ᵥ` for `vector.cons`.
-/


universe u

variable {n : ℕ}

namespace Vector

variable {α : Type _}

-- mathport name: «expr ::ᵥ »
infixr:67 " ::ᵥ " => Vector.cons

attribute [simp] head_cons tail_cons

instance [Inhabited α] : Inhabited (Vector α n) :=
  ⟨ofFn default⟩

#print Vector.toList_injective /-
theorem toList_injective : Function.Injective (@toList α n) :=
  Subtype.val_injective
#align vector.to_list_injective Vector.toList_injective
-/

#print Vector.ext /-
/-- Two `v w : vector α n` are equal iff they are equal at every single index. -/
@[ext]
theorem ext : ∀ {v w : Vector α n} (h : ∀ m : Fin n, Vector.get v m = Vector.get w m), v = w
  | ⟨v, hv⟩, ⟨w, hw⟩, h =>
    Subtype.eq (List.ext_nthLe (by rw [hv, hw]) fun m hm hn => h ⟨m, hv ▸ hm⟩)
#align vector.ext Vector.ext
-/

#print Vector.replicate /-
/-- A vector with `n` elements `a`. -/
def replicate (n : ℕ) (a : α) : Vector α n :=
  ⟨List.replicate n a, List.length_replicate n a⟩
#align vector.replicate Vector.replicate
-/

#print Vector.zero_subsingleton /-
/-- The empty `vector` is a `subsingleton`. -/
instance zero_subsingleton : Subsingleton (Vector α 0) :=
  ⟨fun _ _ => Vector.ext fun m => Fin.elim0 m⟩
#align vector.zero_subsingleton Vector.zero_subsingleton
-/

#print Vector.cons_val /-
@[simp]
theorem cons_val (a : α) : ∀ v : Vector α n, (a ::ᵥ v).val = a :: v.val
  | ⟨_, _⟩ => rfl
#align vector.cons_val Vector.cons_val
-/

/- warning: vector.cons_head clashes with vector.head_cons -> Vector.head_cons
warning: vector.cons_head -> Vector.head_cons is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} (a : α) (v : Vector.{u1} α n), Eq.{succ u1} α (Vector.head.{u1} α n (Vector.cons.{u1} α n a v)) a
but is expected to have type
  forall {n : Type.{u1}} {α : Nat} (a : n) (v : Vector.{u1} n α), Eq.{succ u1} n (Vector.head.{u1} n α (Vector.cons.{u1} n α a v)) a
Case conversion may be inaccurate. Consider using '#align vector.cons_head Vector.head_consₓ'. -/
@[simp]
theorem head_cons (a : α) : ∀ v : Vector α n, (a ::ᵥ v).head = a
  | ⟨_, _⟩ => rfl
#align vector.cons_head Vector.head_cons

/- warning: vector.cons_tail clashes with vector.tail_cons -> Vector.tail_cons
warning: vector.cons_tail -> Vector.tail_cons is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} (a : α) (v : Vector.{u1} α n), Eq.{succ u1} (Vector.{u1} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (Nat.succ n) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.tail.{u1} α (Nat.succ n) (Vector.cons.{u1} α n a v)) v
but is expected to have type
  forall {n : Type.{u1}} {α : Nat} (a : n) (v : Vector.{u1} n α), Eq.{succ u1} (Vector.{u1} n (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Nat.succ α) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.tail.{u1} n (Nat.succ α) (Vector.cons.{u1} n α a v)) v
Case conversion may be inaccurate. Consider using '#align vector.cons_tail Vector.tail_consₓ'. -/
@[simp]
theorem tail_cons (a : α) : ∀ v : Vector α n, (a ::ᵥ v).tail = v
  | ⟨_, _⟩ => rfl
#align vector.cons_tail Vector.tail_cons

#print Vector.eq_cons_iff /-
theorem eq_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v = a ::ᵥ v' ↔ v.head = a ∧ v.tail = v' :=
  ⟨fun h => h.symm ▸ ⟨head_cons a v', tail_cons a v'⟩, fun h =>
    trans (cons_head_tail v).symm (by rw [h.1, h.2])⟩
#align vector.eq_cons_iff Vector.eq_cons_iff
-/

#print Vector.ne_cons_iff /-
theorem ne_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v ≠ a ::ᵥ v' ↔ v.head ≠ a ∨ v.tail ≠ v' := by rw [Ne.def, eq_cons_iff a v v', not_and_or]
#align vector.ne_cons_iff Vector.ne_cons_iff
-/

#print Vector.exists_eq_cons /-
theorem exists_eq_cons (v : Vector α n.succ) : ∃ (a : α)(as : Vector α n), v = a ::ᵥ as :=
  ⟨v.head, v.tail, (eq_cons_iff v.head v v.tail).2 ⟨rfl, rfl⟩⟩
#align vector.exists_eq_cons Vector.exists_eq_cons
-/

#print Vector.toList_ofFn /-
@[simp]
theorem toList_ofFn : ∀ {n} (f : Fin n → α), toList (ofFn f) = List.ofFn f
  | 0, f => rfl
  | n + 1, f => by rw [of_fn, List.ofFn_succ, to_list_cons, to_list_of_fn]
#align vector.to_list_of_fn Vector.toList_ofFn
-/

#print Vector.mk_toList /-
@[simp]
theorem mk_toList : ∀ (v : Vector α n) (h), (⟨toList v, h⟩ : Vector α n) = v
  | ⟨l, h₁⟩, h₂ => rfl
#align vector.mk_to_list Vector.mk_toList
-/

/- warning: vector.length_coe clashes with [anonymous] -> [anonymous]
warning: vector.length_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u_1}} (v : Vector.{u_1} α n), Eq.{1} Nat (List.length.{u_1} α ((fun (a : Sort.{max 1 (succ u_1)}) (b : Type.{u_1}) [self : HasLiftT.{max 1 (succ u_1), succ u_1} a b] => self.0) (Subtype.{succ u_1} (List.{u_1} α) (fun (l : List.{u_1} α) => Eq.{1} Nat (List.length.{u_1} α l) n)) (List.{u_1} α) (HasLiftT.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} (List.{u_1} α) (fun (l : List.{u_1} α) => Eq.{1} Nat (List.length.{u_1} α l) n)) (List.{u_1} α) (CoeTCₓ.coe.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} (List.{u_1} α) (fun (l : List.{u_1} α) => Eq.{1} Nat (List.length.{u_1} α l) n)) (List.{u_1} α) (coeBase.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} (List.{u_1} α) (fun (l : List.{u_1} α) => Eq.{1} Nat (List.length.{u_1} α l) n)) (List.{u_1} α) (coeSubtype.{succ u_1} (List.{u_1} α) (fun (l : List.{u_1} α) => Eq.{1} Nat (List.length.{u_1} α l) n))))) v)) n
but is expected to have type
  forall {n : Type.{u}} {α : Type.{v}}, (Nat -> n -> α) -> Nat -> (List.{u} n) -> (List.{v} α)
Case conversion may be inaccurate. Consider using '#align vector.length_coe [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (v : Vector α n) :
    ((coe : { l : List α // l.length = n } → List α) v).length = n :=
  v.2
#align vector.length_coe [anonymous]

#print Vector.toList_map /-
@[simp]
theorem toList_map {β : Type _} (v : Vector α n) (f : α → β) : (v.map f).toList = v.toList.map f :=
  by cases v <;> rfl
#align vector.to_list_map Vector.toList_map
-/

#print Vector.head_map /-
@[simp]
theorem head_map {β : Type _} (v : Vector α (n + 1)) (f : α → β) : (v.map f).head = f v.head :=
  by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h, map_cons, head_cons, head_cons]
#align vector.head_map Vector.head_map
-/

#print Vector.tail_map /-
@[simp]
theorem tail_map {β : Type _} (v : Vector α (n + 1)) (f : α → β) : (v.map f).tail = v.tail.map f :=
  by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h, map_cons, tail_cons, tail_cons]
#align vector.tail_map Vector.tail_map
-/

#print Vector.get_eq_get /-
theorem get_eq_get :
    ∀ (v : Vector α n) (i), get v i = v.toList.nthLe i.1 (by rw [to_list_length] <;> exact i.2)
  | ⟨l, h⟩, i => rfl
#align vector.nth_eq_nth_le Vector.get_eq_get
-/

/- warning: vector.nth_replicate clashes with vector.nth_repeat -> Vector.get_replicate
Case conversion may be inaccurate. Consider using '#align vector.nth_replicate Vector.get_replicateₓ'. -/
#print Vector.get_replicate /-
@[simp]
theorem get_replicate (a : α) (i : Fin n) : (Vector.replicate n a).nth i = a :=
  List.nthLe_replicate _ _
#align vector.nth_replicate Vector.get_replicate
-/

#print Vector.get_map /-
@[simp]
theorem get_map {β : Type _} (v : Vector α n) (f : α → β) (i : Fin n) :
    (v.map f).nth i = f (v.nth i) := by simp [nth_eq_nth_le]
#align vector.nth_map Vector.get_map
-/

#print Vector.get_ofFn /-
@[simp]
theorem get_ofFn {n} (f : Fin n → α) (i) : get (ofFn f) i = f i := by
  rw [nth_eq_nth_le, ← List.nthLe_ofFn f] <;> congr <;> apply to_list_of_fn
#align vector.nth_of_fn Vector.get_ofFn
-/

#print Vector.ofFn_get /-
@[simp]
theorem ofFn_get (v : Vector α n) : ofFn (get v) = v :=
  by
  rcases v with ⟨l, rfl⟩
  apply to_list_injective
  change nth ⟨l, Eq.refl _⟩ with fun i => nth ⟨l, rfl⟩ i
  simpa only [to_list_of_fn] using List.ofFn_nthLe _
#align vector.of_fn_nth Vector.ofFn_get
-/

#print Equiv.vectorEquivFin /-
/-- The natural equivalence between length-`n` vectors and functions from `fin n`. -/
def Equiv.vectorEquivFin (α : Type _) (n : ℕ) : Vector α n ≃ (Fin n → α) :=
  ⟨Vector.get, Vector.ofFn, Vector.ofFn_get, fun f => funext <| Vector.get_ofFn f⟩
#align equiv.vector_equiv_fin Equiv.vectorEquivFin
-/

#print Vector.get_tail /-
theorem get_tail (x : Vector α n) (i) : x.tail.nth i = x.nth ⟨i.1 + 1, lt_tsub_iff_right.mp i.2⟩ :=
  by rcases x with ⟨_ | _, h⟩ <;> rfl
#align vector.nth_tail Vector.get_tail
-/

#print Vector.get_tail_succ /-
@[simp]
theorem get_tail_succ : ∀ (v : Vector α n.succ) (i : Fin n), get (tail v) i = get v i.succ
  | ⟨a :: l, e⟩, ⟨i, h⟩ => by simp [nth_eq_nth_le] <;> rfl
#align vector.nth_tail_succ Vector.get_tail_succ
-/

#print Vector.tail_val /-
@[simp]
theorem tail_val : ∀ v : Vector α n.succ, v.tail.val = v.val.tail
  | ⟨a :: l, e⟩ => rfl
#align vector.tail_val Vector.tail_val
-/

#print Vector.tail_nil /-
/-- The `tail` of a `nil` vector is `nil`. -/
@[simp]
theorem tail_nil : (@nil α).tail = nil :=
  rfl
#align vector.tail_nil Vector.tail_nil
-/

#print Vector.singleton_tail /-
/-- The `tail` of a vector made up of one element is `nil`. -/
@[simp]
theorem singleton_tail (v : Vector α 1) : v.tail = Vector.nil := by
  simp only [← cons_head_tail, eq_iff_true_of_subsingleton]
#align vector.singleton_tail Vector.singleton_tail
-/

#print Vector.tail_ofFn /-
@[simp]
theorem tail_ofFn {n : ℕ} (f : Fin n.succ → α) : tail (ofFn f) = ofFn fun i => f i.succ :=
  (ofFn_get _).symm.trans <| by
    congr
    funext i
    cases i
    simp
#align vector.tail_of_fn Vector.tail_ofFn
-/

#print Vector.toList_empty /-
@[simp]
theorem toList_empty (v : Vector α 0) : v.toList = [] :=
  List.length_eq_zero.mp v.2
#align vector.to_list_empty Vector.toList_empty
-/

#print Vector.toList_singleton /-
/-- The list that makes up a `vector` made up of a single element,
retrieved via `to_list`, is equal to the list of that single element. -/
@[simp]
theorem toList_singleton (v : Vector α 1) : v.toList = [v.head] :=
  by
  rw [← v.cons_head_tail]
  simp only [to_list_cons, to_list_nil, cons_head, eq_self_iff_true, and_self_iff, singleton_tail]
#align vector.to_list_singleton Vector.toList_singleton
-/

#print Vector.empty_toList_eq_ff /-
@[simp]
theorem empty_toList_eq_ff (v : Vector α (n + 1)) : v.toList.Empty = ff :=
  match v with
  | ⟨a :: as, _⟩ => rfl
#align vector.empty_to_list_eq_ff Vector.empty_toList_eq_ff
-/

#print Vector.not_empty_toList /-
theorem not_empty_toList (v : Vector α (n + 1)) : ¬v.toList.Empty := by
  simp only [empty_to_list_eq_ff, Bool.coe_sort_false, not_false_iff]
#align vector.not_empty_to_list Vector.not_empty_toList
-/

#print Vector.map_id /-
/-- Mapping under `id` does not change a vector. -/
@[simp]
theorem map_id {n : ℕ} (v : Vector α n) : Vector.map id v = v :=
  Vector.eq _ _ (by simp only [List.map_id, Vector.toList_map])
#align vector.map_id Vector.map_id
-/

#print Vector.nodup_iff_injective_get /-
theorem nodup_iff_injective_get {v : Vector α n} : v.toList.Nodup ↔ Function.Injective v.nth :=
  by
  cases' v with l hl
  subst hl
  simp only [List.nodup_iff_nthLe_inj]
  constructor
  · intro h i j hij
    cases i
    cases j
    ext
    apply h
    simpa
  · intro h i j hi hj hij
    have := @h ⟨i, hi⟩ ⟨j, hj⟩
    simp [nth_eq_nth_le] at *
    tauto
#align vector.nodup_iff_nth_inj Vector.nodup_iff_injective_get
-/

#print Vector.head?_toList /-
theorem head?_toList : ∀ v : Vector α n.succ, (toList v).head' = some (head v)
  | ⟨a :: l, e⟩ => rfl
#align vector.head'_to_list Vector.head?_toList
-/

#print Vector.reverse /-
/-- Reverse a vector. -/
def reverse (v : Vector α n) : Vector α n :=
  ⟨v.toList.reverse, by simp⟩
#align vector.reverse Vector.reverse
-/

#print Vector.toList_reverse /-
/-- The `list` of a vector after a `reverse`, retrieved by `to_list` is equal
to the `list.reverse` after retrieving a vector's `to_list`. -/
theorem toList_reverse {v : Vector α n} : v.reverse.toList = v.toList.reverse :=
  rfl
#align vector.to_list_reverse Vector.toList_reverse
-/

#print Vector.reverse_reverse /-
@[simp]
theorem reverse_reverse {v : Vector α n} : v.reverse.reverse = v :=
  by
  cases v
  simp [Vector.reverse]
#align vector.reverse_reverse Vector.reverse_reverse
-/

/- warning: vector.nth_zero -> Vector.get_zero is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} (v : Vector.{u1} α (Nat.succ n)), Eq.{succ u1} α (Vector.get.{u1} α (Nat.succ n) v (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))) (Vector.head.{u1} α n v)
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} (v : Vector.{u1} α (Nat.succ n)), Eq.{succ u1} α (Vector.get.{u1} α (Nat.succ n) v (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))) (Vector.head.{u1} α n v)
Case conversion may be inaccurate. Consider using '#align vector.nth_zero Vector.get_zeroₓ'. -/
@[simp]
theorem get_zero : ∀ v : Vector α n.succ, get v 0 = head v
  | ⟨a :: l, e⟩ => rfl
#align vector.nth_zero Vector.get_zero

/- warning: vector.head_of_fn -> Vector.head_ofFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} (f : (Fin (Nat.succ n)) -> α), Eq.{succ u1} α (Vector.head.{u1} α n (Vector.ofFn.{u1} α (Nat.succ n) f)) (f (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n))))))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} (f : (Fin (Nat.succ n)) -> α), Eq.{succ u1} α (Vector.head.{u1} α n (Vector.ofFn.{u1} α (Nat.succ n) f)) (f (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n))))
Case conversion may be inaccurate. Consider using '#align vector.head_of_fn Vector.head_ofFnₓ'. -/
@[simp]
theorem head_ofFn {n : ℕ} (f : Fin n.succ → α) : head (ofFn f) = f 0 := by
  rw [← nth_zero, nth_of_fn]
#align vector.head_of_fn Vector.head_ofFn

/- warning: vector.nth_cons_zero -> Vector.get_cons_zero is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} (a : α) (v : Vector.{u1} α n), Eq.{succ u1} α (Vector.get.{u1} α (Nat.succ n) (Vector.cons.{u1} α n a v) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (OfNat.mk.{0} (Fin (Nat.succ n)) 0 (Zero.zero.{0} (Fin (Nat.succ n)) (Fin.hasZeroOfNeZero (Nat.succ n) (NeZero.succ n)))))) a
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} (a : α) (v : Vector.{u1} α n), Eq.{succ u1} α (Vector.get.{u1} α (Nat.succ n) (Vector.cons.{u1} α n a v) (OfNat.ofNat.{0} (Fin (Nat.succ n)) 0 (Fin.instOfNatFin (Nat.succ n) 0 (NeZero.succ n)))) a
Case conversion may be inaccurate. Consider using '#align vector.nth_cons_zero Vector.get_cons_zeroₓ'. -/
@[simp]
theorem get_cons_zero (a : α) (v : Vector α n) : get (a ::ᵥ v) 0 = a := by simp [nth_zero]
#align vector.nth_cons_zero Vector.get_cons_zero

#print Vector.get_cons_nil /-
/-- Accessing the `nth` element of a vector made up
of one element `x : α` is `x` itself. -/
@[simp]
theorem get_cons_nil {ix : Fin 1} (x : α) : get (x ::ᵥ nil) ix = x := by convert nth_cons_zero x nil
#align vector.nth_cons_nil Vector.get_cons_nil
-/

#print Vector.get_cons_succ /-
@[simp]
theorem get_cons_succ (a : α) (v : Vector α n) (i : Fin n) : get (a ::ᵥ v) i.succ = get v i := by
  rw [← nth_tail_succ, tail_cons]
#align vector.nth_cons_succ Vector.get_cons_succ
-/

#print Vector.last /-
/-- The last element of a `vector`, given that the vector is at least one element. -/
def last (v : Vector α (n + 1)) : α :=
  v.nth (Fin.last n)
#align vector.last Vector.last
-/

#print Vector.last_def /-
/-- The last element of a `vector`, given that the vector is at least one element. -/
theorem last_def {v : Vector α (n + 1)} : v.last = v.nth (Fin.last n) :=
  rfl
#align vector.last_def Vector.last_def
-/

#print Vector.reverse_get_zero /-
/-- The `last` element of a vector is the `head` of the `reverse` vector. -/
theorem reverse_get_zero {v : Vector α (n + 1)} : v.reverse.head = v.last :=
  by
  have : 0 = v.to_list.length - 1 - n := by
    simp only [Nat.add_succ_sub_one, add_zero, to_list_length, tsub_self, List.length_reverse]
  rw [← nth_zero, last_def, nth_eq_nth_le, nth_eq_nth_le]
  simp_rw [to_list_reverse, [anonymous], Fin.val_last, Fin.val_zero, this]
  rw [List.nthLe_reverse]
#align vector.reverse_nth_zero Vector.reverse_get_zero
-/

section Scan

variable {β : Type _}

variable (f : β → α → β) (b : β)

variable (v : Vector α n)

#print Vector.scanl /-
/-- Construct a `vector β (n + 1)` from a `vector α n` by scanning `f : β → α → β`
from the "left", that is, from 0 to `fin.last n`, using `b : β` as the starting value.
-/
def scanl : Vector β (n + 1) :=
  ⟨List.scanl f b v.toList, by rw [List.length_scanl, to_list_length]⟩
#align vector.scanl Vector.scanl
-/

#print Vector.scanl_nil /-
/-- Providing an empty vector to `scanl` gives the starting value `b : β`. -/
@[simp]
theorem scanl_nil : scanl f b nil = b ::ᵥ nil :=
  rfl
#align vector.scanl_nil Vector.scanl_nil
-/

#print Vector.scanl_cons /-
/-- The recursive step of `scanl` splits a vector `x ::ᵥ v : vector α (n + 1)`
into the provided starting value `b : β` and the recursed `scanl`
`f b x : β` as the starting value.

This lemma is the `cons` version of `scanl_nth`.
-/
@[simp]
theorem scanl_cons (x : α) : scanl f b (x ::ᵥ v) = b ::ᵥ scanl f (f b x) v := by
  simpa only [scanl, to_list_cons]
#align vector.scanl_cons Vector.scanl_cons
-/

/- warning: vector.scanl_val -> Vector.scanl_val is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} {β : Type.{u2}} (f : β -> α -> β) (b : β) {v : Vector.{u1} α n}, Eq.{succ u2} (List.{u2} β) (Subtype.val.{succ u2} (List.{u2} β) (fun (l : List.{u2} β) => Eq.{1} Nat (List.length.{u2} β l) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.scanl.{u1, u2} n α β f b v)) (List.scanl.{u2, u1} β α f b (Subtype.val.{succ u1} (List.{u1} α) (fun (l : List.{u1} α) => Eq.{1} Nat (List.length.{u1} α l) n) v))
but is expected to have type
  forall {n : Nat} {α : Type.{u2}} {β : Type.{u1}} (f : β -> α -> β) (b : β) {v : Vector.{u2} α n}, Eq.{succ u1} (List.{u1} β) (Subtype.val.{succ u1} (List.{u1} β) (fun (l : List.{u1} β) => Eq.{1} Nat (List.length.{u1} β l) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.scanl.{u2, u1} n α β f b v)) (List.scanl.{u1, u2} β α f b (Subtype.val.{succ u2} (List.{u2} α) (fun (l : List.{u2} α) => Eq.{1} Nat (List.length.{u2} α l) n) v))
Case conversion may be inaccurate. Consider using '#align vector.scanl_val Vector.scanl_valₓ'. -/
/-- The underlying `list` of a `vector` after a `scanl` is the `list.scanl`
of the underlying `list` of the original `vector`.
-/
@[simp]
theorem scanl_val : ∀ {v : Vector α n}, (scanl f b v).val = List.scanl f b v.val
  | ⟨l, hl⟩ => rfl
#align vector.scanl_val Vector.scanl_val

#print Vector.toList_scanl /-
/-- The `to_list` of a `vector` after a `scanl` is the `list.scanl`
of the `to_list` of the original `vector`.
-/
@[simp]
theorem toList_scanl : (scanl f b v).toList = List.scanl f b v.toList :=
  rfl
#align vector.to_list_scanl Vector.toList_scanl
-/

/- warning: vector.scanl_singleton -> Vector.scanl_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : β -> α -> β) (b : β) (v : Vector.{u1} α (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))), Eq.{succ u2} (Vector.{u2} β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.scanl.{u1, u2} (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) α β f b v) (Vector.cons.{u2} β (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) b (Vector.cons.{u2} β (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (f b (Vector.head.{u1} α (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) v)) (Vector.nil.{u2} β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : β -> α -> β) (b : β) (v : Vector.{u2} α (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))), Eq.{succ u1} (Vector.{u1} β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.scanl.{u2, u1} (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) α β f b v) (Vector.cons.{u1} β (Nat.succ (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) b (Vector.cons.{u1} β (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (f b (Vector.head.{u2} α (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) v)) (Vector.nil.{u1} β)))
Case conversion may be inaccurate. Consider using '#align vector.scanl_singleton Vector.scanl_singletonₓ'. -/
/-- The recursive step of `scanl` splits a vector made up of a single element
`x ::ᵥ nil : vector α 1` into a `vector` of the provided starting value `b : β`
and the mapped `f b x : β` as the last value.
-/
@[simp]
theorem scanl_singleton (v : Vector α 1) : scanl f b v = b ::ᵥ f b v.head ::ᵥ nil :=
  by
  rw [← cons_head_tail v]
  simp only [scanl_cons, scanl_nil, cons_head, singleton_tail]
#align vector.scanl_singleton Vector.scanl_singleton

#print Vector.scanl_head /-
/-- The first element of `scanl` of a vector `v : vector α n`,
retrieved via `head`, is the starting value `b : β`.
-/
@[simp]
theorem scanl_head : (scanl f b v).head = b :=
  by
  cases n
  · have : v = nil := by simp only [eq_iff_true_of_subsingleton]
    simp only [this, scanl_nil, cons_head]
  · rw [← cons_head_tail v]
    simp only [← nth_zero, nth_eq_nth_le, to_list_scanl, to_list_cons, List.scanl, Fin.val_zero,
      List.nthLe]
#align vector.scanl_head Vector.scanl_head
-/

/- warning: vector.scanl_nth -> Vector.scanl_get is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} {β : Type.{u2}} (f : β -> α -> β) (b : β) (v : Vector.{u1} α n) (i : Fin n), Eq.{succ u2} β (Vector.get.{u2} β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Vector.scanl.{u1, u2} n α β f b v) (Fin.succ n i)) (f (Vector.get.{u2} β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Vector.scanl.{u1, u2} n α β f b v) (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe n) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin n) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin n) (Fin.hasLe n)) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc n) i)) (Vector.get.{u1} α n v i))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} {β : Type.{u2}} (f : β -> α -> β) (b : β) (v : Vector.{u1} α n) (i : Fin n), Eq.{succ u2} β (Vector.get.{u2} β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Vector.scanl.{u1, u2} n α β f b v) (Fin.succ n i)) (f (Vector.get.{u2} β (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Vector.scanl.{u1, u2} n α β f b v) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (fun (_x : Fin n) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin n) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin n) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin n) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin n) => LE.le.{0} (Fin n) (instLEFin n) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.castSucc n)) i)) (Vector.get.{u1} α n v i))
Case conversion may be inaccurate. Consider using '#align vector.scanl_nth Vector.scanl_getₓ'. -/
/-- For an index `i : fin n`, the `nth` element of `scanl` of a
vector `v : vector α n` at `i.succ`, is equal to the application
function `f : β → α → β` of the `i.cast_succ` element of
`scanl f b v` and `nth v i`.

This lemma is the `nth` version of `scanl_cons`.
-/
@[simp]
theorem scanl_get (i : Fin n) :
    (scanl f b v).nth i.succ = f ((scanl f b v).nth i.cast_succ) (v.nth i) :=
  by
  cases n
  · exact finZeroElim i
  induction' n with n hn generalizing b
  · have i0 : i = 0 := by simp only [eq_iff_true_of_subsingleton]
    simpa only [scanl_singleton, i0, nth_zero]
  · rw [← cons_head_tail v, scanl_cons, nth_cons_succ]
    refine' Fin.cases _ _ i
    · simp only [nth_zero, scanl_head, Fin.castSucc_zero, cons_head]
    · intro i'
      simp only [hn, Fin.castSucc_fin_succ, nth_cons_succ]
#align vector.scanl_nth Vector.scanl_get

end Scan

#print Vector.mOfFn /-
/-- Monadic analog of `vector.of_fn`.
Given a monadic function on `fin n`, return a `vector α n` inside the monad. -/
def mOfFn {m} [Monad m] {α : Type u} : ∀ {n}, (Fin n → m α) → m (Vector α n)
  | 0, f => pure nil
  | n + 1, f => do
    let a ← f 0
    let v ← m_of_fn fun i => f i.succ
    pure (a ::ᵥ v)
#align vector.m_of_fn Vector.mOfFn
-/

/- warning: vector.m_of_fn_pure -> Vector.mOfFn_pure is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] [_inst_2 : LawfulMonad.{u1, u2} m _inst_1] {α : Type.{u1}} {n : Nat} (f : (Fin n) -> α), Eq.{succ u2} (m (Vector.{u1} α n)) (Vector.mOfFn.{u1, u2} m _inst_1 α n (fun (i : Fin n) => Pure.pure.{u1, u2} m (Applicative.toHasPure.{u1, u2} m (Monad.toApplicative.{u1, u2} m _inst_1)) α (f i))) (Pure.pure.{u1, u2} m (Applicative.toHasPure.{u1, u2} m (Monad.toApplicative.{u1, u2} m _inst_1)) (Vector.{u1} α n) (Vector.ofFn.{u1} α n f))
but is expected to have type
  forall {m : Type.{u2} -> Type.{u1}} [_inst_1 : Monad.{u2, u1} m] [_inst_2 : LawfulMonad.{u2, u1} m _inst_1] {α : Type.{u2}} {n : Nat} (f : (Fin n) -> α), Eq.{succ u1} (m (Vector.{u2} α n)) (Vector.mOfFn.{u2, u1} m _inst_1 α n (fun (i : Fin n) => Pure.pure.{u2, u1} m (Applicative.toPure.{u2, u1} m (Monad.toApplicative.{u2, u1} m _inst_1)) α (f i))) (Pure.pure.{u2, u1} m (Applicative.toPure.{u2, u1} m (Monad.toApplicative.{u2, u1} m _inst_1)) (Vector.{u2} α n) (Vector.ofFn.{u2} α n f))
Case conversion may be inaccurate. Consider using '#align vector.m_of_fn_pure Vector.mOfFn_pureₓ'. -/
theorem mOfFn_pure {m} [Monad m] [LawfulMonad m] {α} :
    ∀ {n} (f : Fin n → α), (@mOfFn m _ _ _ fun i => pure (f i)) = pure (ofFn f)
  | 0, f => rfl
  | n + 1, f => by simp [m_of_fn, @m_of_fn_pure n, of_fn]
#align vector.m_of_fn_pure Vector.mOfFn_pure

#print Vector.mmap /-
/-- Apply a monadic function to each component of a vector,
returning a vector inside the monad. -/
def mmap {m} [Monad m] {α} {β : Type u} (f : α → m β) : ∀ {n}, Vector α n → m (Vector β n)
  | 0, xs => pure nil
  | n + 1, xs => do
    let h' ← f xs.head
    let t' ← @mmap n xs.tail
    pure (h' ::ᵥ t')
#align vector.mmap Vector.mmap
-/

/- warning: vector.mmap_nil -> Vector.mmap_nil is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}} (f : α -> (m β)), Eq.{succ u2} (m (Vector.{u1} β (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) (Vector.mmap.{u1, u2, u3} m _inst_1 α β f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Vector.nil.{u3} α)) (Pure.pure.{u1, u2} m (Applicative.toHasPure.{u1, u2} m (Monad.toApplicative.{u1, u2} m _inst_1)) (Vector.{u1} β (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Vector.nil.{u1} β))
but is expected to have type
  forall {m : Type.{u3} -> Type.{u2}} [_inst_1 : Monad.{u3, u2} m] {α : Type.{u1}} {β : Type.{u3}} (f : α -> (m β)), Eq.{succ u2} (m (Vector.{u3} β (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) (Vector.mmap.{u3, u2, u1} m _inst_1 α β f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Vector.nil.{u1} α)) (Pure.pure.{u3, u2} m (Applicative.toPure.{u3, u2} m (Monad.toApplicative.{u3, u2} m _inst_1)) (Vector.{u3} β (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Vector.nil.{u3} β))
Case conversion may be inaccurate. Consider using '#align vector.mmap_nil Vector.mmap_nilₓ'. -/
@[simp]
theorem mmap_nil {m} [Monad m] {α β} (f : α → m β) : mmap f nil = pure nil :=
  rfl
#align vector.mmap_nil Vector.mmap_nil

/- warning: vector.mmap_cons -> Vector.mmap_cons is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}} (f : α -> (m β)) (a : α) {n : Nat} (v : Vector.{u3} α n), Eq.{succ u2} (m (Vector.{u1} β (Nat.succ n))) (Vector.mmap.{u1, u2, u3} m _inst_1 α β f (Nat.succ n) (Vector.cons.{u3} α n a v)) (Bind.bind.{u1, u2} m (Monad.toHasBind.{u1, u2} m _inst_1) β (Vector.{u1} β (Nat.succ n)) (f a) (fun (h' : β) => Bind.bind.{u1, u2} m (Monad.toHasBind.{u1, u2} m _inst_1) (Vector.{u1} β n) (Vector.{u1} β (Nat.succ n)) (Vector.mmap.{u1, u2, u3} m _inst_1 α β f n v) (fun (t' : Vector.{u1} β n) => Pure.pure.{u1, u2} m (Applicative.toHasPure.{u1, u2} m (Monad.toApplicative.{u1, u2} m _inst_1)) (Vector.{u1} β (Nat.succ n)) (Vector.cons.{u1} β n h' t'))))
but is expected to have type
  forall {m : Type.{u3} -> Type.{u2}} [_inst_1 : Monad.{u3, u2} m] {α : Type.{u1}} {β : Type.{u3}} (f : α -> (m β)) (a : α) {n : Nat} (v : Vector.{u1} α n), Eq.{succ u2} (m (Vector.{u3} β (Nat.succ n))) (Vector.mmap.{u3, u2, u1} m _inst_1 α β f (Nat.succ n) (Vector.cons.{u1} α n a v)) (Bind.bind.{u3, u2} m (Monad.toBind.{u3, u2} m _inst_1) β (Vector.{u3} β (Nat.succ n)) (f a) (fun (h' : β) => Bind.bind.{u3, u2} m (Monad.toBind.{u3, u2} m _inst_1) (Vector.{u3} β n) (Vector.{u3} β (Nat.succ n)) (Vector.mmap.{u3, u2, u1} m _inst_1 α β f n v) (fun (t' : Vector.{u3} β n) => Pure.pure.{u3, u2} m (Applicative.toPure.{u3, u2} m (Monad.toApplicative.{u3, u2} m _inst_1)) (Vector.{u3} β (Nat.succ n)) (Vector.cons.{u3} β n h' t'))))
Case conversion may be inaccurate. Consider using '#align vector.mmap_cons Vector.mmap_consₓ'. -/
@[simp]
theorem mmap_cons {m} [Monad m] {α β} (f : α → m β) (a) :
    ∀ {n} (v : Vector α n),
      mmap f (a ::ᵥ v) = do
        let h' ← f a
        let t' ← mmap f v
        pure (h' ::ᵥ t')
  | _, ⟨l, rfl⟩ => rfl
#align vector.mmap_cons Vector.mmap_cons

#print Vector.inductionOn /-
/-- Define `C v` by induction on `v : vector α n`.

This function has two arguments: `h_nil` handles the base case on `C nil`,
and `h_cons` defines the inductive step using `∀ x : α, C w → C (x ::ᵥ w)`.

This can be used as `induction v using vector.induction_on`. -/
@[elab_as_elim]
def inductionOn {C : ∀ {n : ℕ}, Vector α n → Sort _} {n : ℕ} (v : Vector α n) (h_nil : C nil)
    (h_cons : ∀ {n : ℕ} {x : α} {w : Vector α n}, C w → C (x ::ᵥ w)) : C v :=
  by
  induction' n with n ih generalizing v
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
  · rcases v with ⟨_ | ⟨a, v⟩, _⟩
    cases v_property
    apply @h_cons n _ ⟨v, (add_left_inj 1).mp v_property⟩
    apply ih
#align vector.induction_on Vector.inductionOn
-/

-- check that the above works with `induction ... using`
example (v : Vector α n) : True := by induction v using Vector.inductionOn <;> trivial

variable {β γ : Type _}

#print Vector.inductionOn₂ /-
/-- Define `C v w` by induction on a pair of vectors `v : vector α n` and `w : vector β n`. -/
@[elab_as_elim]
def inductionOn₂ {C : ∀ {n}, Vector α n → Vector β n → Sort _} (v : Vector α n) (w : Vector β n)
    (h_nil : C nil nil) (h_cons : ∀ {n a b} {x : Vector α n} {y}, C x y → C (a ::ᵥ x) (b ::ᵥ y)) :
    C v w := by
  induction' n with n ih generalizing v w
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact h_nil
  · rcases v with ⟨_ | ⟨a, v⟩, _⟩
    cases v_property
    rcases w with ⟨_ | ⟨b, w⟩, _⟩
    cases w_property
    apply @h_cons n _ _ ⟨v, (add_left_inj 1).mp v_property⟩ ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih
#align vector.induction_on₂ Vector.inductionOn₂
-/

#print Vector.inductionOn₃ /-
/-- Define `C u v w` by induction on a triplet of vectors
`u : vector α n`, `v : vector β n`, and `w : vector γ b`. -/
@[elab_as_elim]
def inductionOn₃ {C : ∀ {n}, Vector α n → Vector β n → Vector γ n → Sort _} (u : Vector α n)
    (v : Vector β n) (w : Vector γ n) (h_nil : C nil nil nil)
    (h_cons : ∀ {n a b c} {x : Vector α n} {y z}, C x y z → C (a ::ᵥ x) (b ::ᵥ y) (c ::ᵥ z)) :
    C u v w := by
  induction' n with n ih generalizing u v w
  · rcases u with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
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
#align vector.induction_on₃ Vector.inductionOn₃
-/

/- warning: vector.to_array -> Vector.toArray is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}}, (Vector.{u1} α n) -> (Array'.{u1} n α)
but is expected to have type
  forall {n : Nat} {α : Type.{u1}}, (Vector.{u1} α n) -> (Array.{u1} α)
Case conversion may be inaccurate. Consider using '#align vector.to_array Vector.toArrayₓ'. -/
/-- Cast a vector to an array. -/
def toArray : Vector α n → Array' n α
  | ⟨xs, h⟩ => cast (by rw [h]) xs.toArray
#align vector.to_array Vector.toArray

section InsertNth

variable {a : α}

#print Vector.insertNth /-
/-- `v.insert_nth a i` inserts `a` into the vector `v` at position `i`
(and shifting later components to the right). -/
def insertNth (a : α) (i : Fin (n + 1)) (v : Vector α n) : Vector α (n + 1) :=
  ⟨v.1.insertNth i a, by
    rw [List.length_insertNth, v.2]
    rw [v.2, ← Nat.succ_le_succ_iff]
    exact i.2⟩
#align vector.insert_nth Vector.insertNth
-/

#print Vector.insertNth_val /-
theorem insertNth_val {i : Fin (n + 1)} {v : Vector α n} :
    (v.insertNth a i).val = v.val.insertNth i.1 a :=
  rfl
#align vector.insert_nth_val Vector.insertNth_val
-/

#print Vector.removeNth_val /-
@[simp]
theorem removeNth_val {i : Fin n} : ∀ {v : Vector α n}, (removeNth i v).val = v.val.removeNth i
  | ⟨l, hl⟩ => rfl
#align vector.remove_nth_val Vector.removeNth_val
-/

#print Vector.removeNth_insertNth /-
theorem removeNth_insertNth {v : Vector α n} {i : Fin (n + 1)} :
    removeNth i (insertNth a i v) = v :=
  Subtype.eq <| List.removeNth_insertNth i.1 v.1
#align vector.remove_nth_insert_nth Vector.removeNth_insertNth
-/

/- warning: vector.remove_nth_insert_nth' -> Vector.removeNth_insertNth' is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} {a : α} {v : Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))} {j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))}, Eq.{succ u1} (Vector.{u1} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.removeNth.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))) (fun (_x : RelEmbedding.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) => (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Preorder.toLE.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (PartialOrder.toPreorder.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.partialOrder (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))) (Fin.succAbove (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) j) i) (Vector.insertNth.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α a j v)) (Vector.insertNth.{u1} n α a (Fin.predAbove (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i j) (Vector.removeNth.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i v))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} {a : α} {v : Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} {j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))}, Eq.{succ u1} (Vector.{u1} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.removeNth.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (_x : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.succAbove (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) j)) i) (Vector.insertNth.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α a j v)) (Vector.insertNth.{u1} n α a (Fin.predAbove (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i j) (Vector.removeNth.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i v))
Case conversion may be inaccurate. Consider using '#align vector.remove_nth_insert_nth' Vector.removeNth_insertNth'ₓ'. -/
theorem removeNth_insertNth' {v : Vector α (n + 1)} :
    ∀ {i : Fin (n + 1)} {j : Fin (n + 2)},
      removeNth (j.succAbove i) (insertNth a j v) = insertNth a (i.predAbove j) (removeNth i v)
  | ⟨i, hi⟩, ⟨j, hj⟩ =>
    by
    dsimp [insert_nth, remove_nth, Fin.succAbove, Fin.predAbove]
    simp only [Subtype.mk_eq_mk]
    split_ifs
    · convert (List.insertNth_removeNth_of_ge i (j - 1) _ _ _).symm
      · convert (Nat.succ_pred_eq_of_pos _).symm
        exact lt_of_le_of_lt (zero_le _) h
      · apply remove_nth_val
      · convert hi
        exact v.2
      · exact Nat.le_pred_of_lt h
    · convert (List.insertNth_removeNth_of_le i j _ _ _).symm
      · apply remove_nth_val
      · convert hi
        exact v.2
      · simpa using h
#align vector.remove_nth_insert_nth' Vector.removeNth_insertNth'

/- warning: vector.insert_nth_comm -> Vector.insertNth_comm is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} (a : α) (b : α) (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) i j) -> (forall (v : Vector.{u1} α n), Eq.{succ u1} (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.insertNth.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α b (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) j) (Vector.insertNth.{u1} n α a i v)) (Vector.insertNth.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) α a (coeFn.{1, 1} (OrderEmbedding.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (fun (_x : RelEmbedding.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) => (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (RelEmbedding.hasCoeToFun.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Fin.hasLe (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (Fin.castSucc (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) i) (Vector.insertNth.{u1} n α b j v)))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} (a : α) (b : α) (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), (LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) i j) -> (forall (v : Vector.{u1} α n), Eq.{succ u1} (Vector.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.insertNth.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α b (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) j) (Vector.insertNth.{u1} n α a i v)) (Vector.insertNth.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) α a (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (_x : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (RelEmbedding.toEmbedding.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => LE.le.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (instLEFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Fin.castSucc (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) i) (Vector.insertNth.{u1} n α b j v)))
Case conversion may be inaccurate. Consider using '#align vector.insert_nth_comm Vector.insertNth_commₓ'. -/
theorem insertNth_comm (a b : α) (i j : Fin (n + 1)) (h : i ≤ j) :
    ∀ v : Vector α n,
      (v.insertNth a i).insertNth b j.succ = (v.insertNth b j).insertNth a i.cast_succ
  | ⟨l, hl⟩ => by
    refine' Subtype.eq _
    simp only [insert_nth_val, Fin.val_succ, Fin.castSucc, [anonymous], Fin.coe_castAdd]
    apply List.insertNth_comm
    · assumption
    · rw [hl]
      exact Nat.le_of_succ_le_succ j.2
#align vector.insert_nth_comm Vector.insertNth_comm

end InsertNth

section UpdateNth

#print Vector.set /-
/-- `update_nth v n a` replaces the `n`th element of `v` with `a` -/
def set (v : Vector α n) (i : Fin n) (a : α) : Vector α n :=
  ⟨v.1.updateNth i.1 a, by rw [List.length_set, v.2]⟩
#align vector.update_nth Vector.set
-/

#print Vector.toList_set /-
@[simp]
theorem toList_set (v : Vector α n) (i : Fin n) (a : α) :
    (v.updateNth i a).toList = v.toList.updateNth i a :=
  rfl
#align vector.to_list_update_nth Vector.toList_set
-/

#print Vector.get_set_same /-
@[simp]
theorem get_set_same (v : Vector α n) (i : Fin n) (a : α) : (v.updateNth i a).nth i = a := by
  cases v <;> cases i <;> simp [Vector.set, Vector.get_eq_get]
#align vector.nth_update_nth_same Vector.get_set_same
-/

#print Vector.get_set_of_ne /-
theorem get_set_of_ne {v : Vector α n} {i j : Fin n} (h : i ≠ j) (a : α) :
    (v.updateNth i a).nth j = v.nth j := by
  cases v <;> cases i <;> cases j <;>
    simp [Vector.set, Vector.get_eq_get, List.nthLe_set_of_ne (Fin.vne_of_ne h)]
#align vector.nth_update_nth_of_ne Vector.get_set_of_ne
-/

/- warning: vector.nth_update_nth_eq_if -> Vector.get_set_eq_if is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} {v : Vector.{u1} α n} {i : Fin n} {j : Fin n} (a : α), Eq.{succ u1} α (Vector.get.{u1} α n (Vector.set.{u1} n α v i a) j) (ite.{succ u1} α (Eq.{1} (Fin n) i j) (Fin.decidableEq n i j) a (Vector.get.{u1} α n v j))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} {v : Vector.{u1} α n} {i : Fin n} {j : Fin n} (a : α), Eq.{succ u1} α (Vector.get.{u1} α n (Vector.set.{u1} n α v i a) j) (ite.{succ u1} α (Eq.{1} (Fin n) i j) (instDecidableEqFin n i j) a (Vector.get.{u1} α n v j))
Case conversion may be inaccurate. Consider using '#align vector.nth_update_nth_eq_if Vector.get_set_eq_ifₓ'. -/
theorem get_set_eq_if {v : Vector α n} {i j : Fin n} (a : α) :
    (v.updateNth i a).nth j = if i = j then a else v.nth j := by
  split_ifs <;> try simp [*] <;> try rw [nth_update_nth_of_ne] <;> assumption
#align vector.nth_update_nth_eq_if Vector.get_set_eq_if

/- warning: vector.prod_update_nth -> Vector.prod_set is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (v : Vector.{u1} α n) (i : Fin n) (a : α), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Vector.toList.{u1} α n (Vector.set.{u1} n α v i a))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Vector.toList.{u1} α (LinearOrder.min.{0} Nat Nat.linearOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) n) (Vector.take.{u1} α n ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) v))) a) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Vector.toList.{u1} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Vector.drop.{u1} α n (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin n) Nat (HasLiftT.mk.{1, 1} (Fin n) Nat (CoeTCₓ.coe.{1, 1} (Fin n) Nat (coeBase.{1, 1} (Fin n) Nat (Fin.coeToNat n)))) i) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) v))))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] (v : Vector.{u1} α n) (i : Fin n) (a : α), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (Vector.toList.{u1} α n (Vector.set.{u1} n α v i a))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (Vector.toList.{u1} α (Min.min.{0} Nat instMinNat (Fin.val n i) n) (Vector.take.{u1} α n (Fin.val n i) v))) a) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (Monoid.toOne.{u1} α _inst_1) (Vector.toList.{u1} α (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val n i) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Vector.drop.{u1} α n (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Fin.val n i) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) v))))
Case conversion may be inaccurate. Consider using '#align vector.prod_update_nth Vector.prod_setₓ'. -/
@[to_additive]
theorem prod_set [Monoid α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.updateNth i a).toList.Prod = (v.take i).toList.Prod * a * (v.drop (i + 1)).toList.Prod :=
  by
  refine' (List.prod_set v.to_list i a).trans _
  have : ↑i < v.to_list.length := lt_of_lt_of_le i.2 (le_of_eq v.2.symm)
  simp_all
#align vector.prod_update_nth Vector.prod_set
#align vector.sum_update_nth Vector.sum_set

/- warning: vector.prod_update_nth' -> Vector.prod_set' is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] (v : Vector.{u1} α n) (i : Fin n) (a : α), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (Vector.toList.{u1} α n (Vector.set.{u1} n α v i a))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (Vector.toList.{u1} α n v)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) (Vector.get.{u1} α n v i))) a)
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] (v : Vector.{u1} α n) (i : Fin n) (a : α), Eq.{succ u1} α (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (Vector.toList.{u1} α n (Vector.set.{u1} n α v i a))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (Vector.toList.{u1} α n v)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (Vector.get.{u1} α n v i))) a)
Case conversion may be inaccurate. Consider using '#align vector.prod_update_nth' Vector.prod_set'ₓ'. -/
@[to_additive]
theorem prod_set' [CommGroup α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.updateNth i a).toList.Prod = v.toList.Prod * (v.nth i)⁻¹ * a :=
  by
  refine' (List.prod_set' v.to_list i a).trans _
  have : ↑i < v.to_list.length := lt_of_lt_of_le i.2 (le_of_eq v.2.symm)
  simp [this, nth_eq_nth_le, mul_assoc]
#align vector.prod_update_nth' Vector.prod_set'

end UpdateNth

end Vector

namespace Vector

section Traverse

variable {F G : Type u → Type u}

variable [Applicative F] [Applicative G]

open Applicative Functor

open List (cons)

open Nat

private def traverse_aux {α β : Type u} (f : α → F β) : ∀ x : List α, F (Vector β x.length)
  | [] => pure Vector.nil
  | x :: xs => Vector.cons <$> f x <*> traverse_aux xs
#align vector.traverse_aux vector.traverse_aux

#print Vector.traverse /-
/-- Apply an applicative function to each component of a vector. -/
protected def traverse {α β : Type u} (f : α → F β) : Vector α n → F (Vector β n)
  | ⟨v, Hv⟩ => cast (by rw [Hv]) <| traverseAux f v
#align vector.traverse Vector.traverse
-/

section

variable {α β : Type u}

/- warning: vector.traverse_def -> Vector.traverse_def is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] {α : Type.{u1}} {β : Type.{u1}} (f : α -> (F β)) (x : α) (xs : Vector.{u1} α n), Eq.{succ u1} (F (Vector.{u1} β (Nat.succ n))) (Vector.traverse.{u1} (Nat.succ n) F _inst_1 α β f (Vector.cons.{u1} α n x xs)) (Seq.seq.{u1, u1} F (Applicative.toHasSeq.{u1, u1} F _inst_1) (Vector.{u1} β n) (Vector.{u1} β (Nat.succ n)) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_1) β ((Vector.{u1} β n) -> (Vector.{u1} β (Nat.succ n))) (Vector.cons.{u1} β n) (f x)) (Vector.traverse.{u1} n F _inst_1 α β f xs))
but is expected to have type
  forall {n : Nat} {F : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] {α : Type.{u1}} {β : Type.{u1}} (f : α -> (F β)) (x : α) (xs : Vector.{u1} α n), Eq.{succ u1} (F (Vector.{u1} β (Nat.succ n))) (Vector.traverse.{u1} (Nat.succ n) F _inst_1 α β f (Vector.cons.{u1} α n x xs)) (Seq.seq.{u1, u1} F (Applicative.toSeq.{u1, u1} F _inst_1) (Vector.{u1} β n) (Vector.{u1} β (Nat.succ n)) (Functor.map.{u1, u1} F (Applicative.toFunctor.{u1, u1} F _inst_1) β ((Vector.{u1} β n) -> (Vector.{u1} β (Nat.succ n))) (Vector.cons.{u1} β n) (f x)) (fun (x._@.Mathlib.Data.Vector.Basic._hyg.6210 : Unit) => Vector.traverse.{u1} n F _inst_1 α β f xs))
Case conversion may be inaccurate. Consider using '#align vector.traverse_def Vector.traverse_defₓ'. -/
@[simp]
protected theorem traverse_def (f : α → F β) (x : α) :
    ∀ xs : Vector α n, (x ::ᵥ xs).traverse f = cons <$> f x <*> xs.traverse f := by
  rintro ⟨xs, rfl⟩ <;> rfl
#align vector.traverse_def Vector.traverse_def

/- warning: vector.id_traverse -> Vector.id_traverse is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} (x : Vector.{u1} α n), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (Vector.{u1} α n)) (Vector.traverse.{u1} n (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α α (id.mk.{succ u1} α) x) x
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} (x : Vector.{u1} α n), Eq.{succ u1} (Id.{u1} (Vector.{u1} α n)) (Vector.traverse.{u1} n Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α α (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) α) x) x
Case conversion may be inaccurate. Consider using '#align vector.id_traverse Vector.id_traverseₓ'. -/
protected theorem id_traverse : ∀ x : Vector α n, x.traverse id.mk = x :=
  by
  rintro ⟨x, rfl⟩; dsimp [Vector.traverse, cast]
  induction' x with x xs IH; · rfl
  simp! [IH]; rfl
#align vector.id_traverse Vector.id_traverse

end

open Function

variable [LawfulApplicative F] [LawfulApplicative G]

variable {α β γ : Type u}

/- warning: vector.comp_traverse -> Vector.comp_traverse is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] [_inst_2 : Applicative.{u1, u1} G] [_inst_3 : LawfulApplicative.{u1, u1} F _inst_1] [_inst_4 : LawfulApplicative.{u1, u1} G _inst_2] {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (f : β -> (F γ)) (g : α -> (G β)) (x : Vector.{u1} α n), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F (Vector.{u1} γ n)) (Vector.traverse.{u1} n (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F) (Functor.Comp.applicative.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F _inst_2 _inst_1) α γ (Function.comp.{succ u1, succ u1, succ u1} α (G (F γ)) (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F γ) (Functor.Comp.mk.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F γ) (Function.comp.{succ u1, succ u1, succ u1} α (G β) (G (F γ)) (Functor.map.{u1, u1} (fun {β : Type.{u1}} => G β) (Applicative.toFunctor.{u1, u1} (fun {β : Type.{u1}} => G β) _inst_2) β (F γ) f) g)) x) (Functor.Comp.mk.{u1, u1, u1} (fun {β : Type.{u1}} => G β) F (Vector.{u1} γ n) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_2) (Vector.{u1} β n) (F (Vector.{u1} γ n)) (Vector.traverse.{u1} n F _inst_1 β γ f) (Vector.traverse.{u1} n G _inst_2 α β g x)))
but is expected to have type
  forall {n : Nat} {F : Type.{u1} -> Type.{u1}} {G : Type.{u1} -> Type.{u1}} [_inst_1 : Applicative.{u1, u1} F] [_inst_2 : Applicative.{u1, u1} G] [_inst_3 : LawfulApplicative.{u1, u1} G _inst_2] {_inst_4 : Type.{u1}} {α : Type.{u1}} {β : Type.{u1}} (γ : α -> (F β)) (f : _inst_4 -> (G α)) (g : Vector.{u1} _inst_4 n), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} G F (Vector.{u1} β n)) (Vector.traverse.{u1} n (Functor.Comp.{u1, u1, u1} G F) (Functor.Comp.instApplicativeComp.{u1, u1, u1} G F _inst_2 _inst_1) _inst_4 β (Function.comp.{succ u1, succ u1, succ u1} _inst_4 (G (F β)) (Functor.Comp.{u1, u1, u1} G F β) (Functor.Comp.mk.{u1, u1, u1} G F β) (Function.comp.{succ u1, succ u1, succ u1} _inst_4 (G α) (G (F β)) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_2) α (F β) γ) f)) g) (Functor.Comp.mk.{u1, u1, u1} G F (Vector.{u1} β n) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_2) (Vector.{u1} α n) (F (Vector.{u1} β n)) (Vector.traverse.{u1} n F _inst_1 α β γ) (Vector.traverse.{u1} n G _inst_2 _inst_4 α f g)))
Case conversion may be inaccurate. Consider using '#align vector.comp_traverse Vector.comp_traverseₓ'. -/
-- We need to turn off the linter here as
-- the `is_lawful_traversable` instance below expects a particular signature.
@[nolint unused_arguments]
protected theorem comp_traverse (f : β → F γ) (g : α → G β) :
    ∀ x : Vector α n,
      Vector.traverse (comp.mk ∘ Functor.map f ∘ g) x =
        Comp.mk (Vector.traverse f <$> Vector.traverse g x) :=
  by
  rintro ⟨x, rfl⟩ <;> dsimp [Vector.traverse, cast] <;> induction' x with x xs <;>
      simp! [cast, *, functor_norm] <;>
    [rfl, simp [(· ∘ ·)]]
#align vector.comp_traverse Vector.comp_traverse

/- warning: vector.traverse_eq_map_id -> Vector.traverse_eq_map_id is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : Vector.{u1} α n), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (Vector.{u1} β n)) (Vector.traverse.{u1} n (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) α β (Function.comp.{succ u1, succ u1, succ u1} α β (id.{succ (succ u1)} Type.{u1} β) (id.mk.{succ u1} β) f) x) (id.mk.{succ u1} (Vector.{u1} β n) (Vector.map.{u1, u1} α β n f x))
but is expected to have type
  forall {n : Nat} {α : Type.{u1}} {β : Type.{u1}} (f : α -> β) (x : Vector.{u1} α n), Eq.{succ u1} (Id.{u1} (Vector.{u1} β n)) (Vector.traverse.{u1} n Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) α β (Function.comp.{succ u1, succ u1, succ u1} α β (Id.{u1} β) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) β) f) x) (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) (Vector.{u1} β n) (Vector.map.{u1, u1} α β n f x))
Case conversion may be inaccurate. Consider using '#align vector.traverse_eq_map_id Vector.traverse_eq_map_idₓ'. -/
protected theorem traverse_eq_map_id {α β} (f : α → β) :
    ∀ x : Vector α n, x.traverse (id.mk ∘ f) = id.mk (map f x) := by
  rintro ⟨x, rfl⟩ <;> simp! <;> induction x <;> simp! [*, functor_norm] <;> rfl
#align vector.traverse_eq_map_id Vector.traverse_eq_map_id

variable (η : ApplicativeTransformation F G)

#print Vector.naturality /-
protected theorem naturality {α β : Type _} (f : α → F β) :
    ∀ x : Vector α n, η (x.traverse f) = x.traverse (@η _ ∘ f) := by
  rintro ⟨x, rfl⟩ <;> simp! [cast] <;> induction' x with x xs IH <;> simp! [*, functor_norm]
#align vector.naturality Vector.naturality
-/

end Traverse

instance : Traversable.{u} (flip Vector n)
    where
  traverse := @Vector.traverse n
  map α β := @Vector.map.{u, u} α β n

instance : IsLawfulTraversable.{u} (flip Vector n)
    where
  id_traverse := @Vector.id_traverse n
  comp_traverse := @Vector.comp_traverse n
  traverse_eq_map_id := @Vector.traverse_eq_map_id n
  naturality := @Vector.naturality n
  id_map := by intros <;> cases x <;> simp! [(· <$> ·)]
  comp_map := by intros <;> cases x <;> simp! [(· <$> ·)]

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[] -/
unsafe instance reflect [reflected_univ.{u}] {α : Type u} [has_reflect α] [reflected _ α] {n : ℕ} :
    has_reflect (Vector α n) := fun v =>
  @Vector.inductionOn α (fun n => reflected _) n v
    ((by
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[]" :
          reflected _ @Vector.nil.{u}).subst
      q(α))
    fun n x xs ih =>
    (by
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:76:14: unsupported tactic `reflect_name #[]" :
          reflected _ @Vector.cons.{u}).subst₄
      q(α) q(n) q(x) ih
#align vector.reflect vector.reflect

end Vector

