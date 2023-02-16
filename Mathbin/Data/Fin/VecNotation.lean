/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module data.fin.vec_notation
! leanprover-community/mathlib commit 32253a1a1071173b33dc7d6a218cf722c6feb514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Tuple.Basic
import Mathbin.Data.List.Range
import Mathbin.GroupTheory.GroupAction.Pi
import Mathbin.Meta.Univs

/-!
# Matrix and vector notation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print Matrix.vecEmpty /-
/-- `![]` is the vector with no entries. -/
def vecEmpty : Fin 0 → α :=
  Fin.elim0'
#align matrix.vec_empty Matrix.vecEmpty
-/

#print Matrix.vecCons /-
/-- `vec_cons h t` prepends an entry `h` to a vector `t`.

The inverse functions are `vec_head` and `vec_tail`.
The notation `![a, b, ...]` expands to `vec_cons a (vec_cons b ...)`.
-/
def vecCons {n : ℕ} (h : α) (t : Fin n → α) : Fin n.succ → α :=
  Fin.cons h t
#align matrix.vec_cons Matrix.vecCons
-/

-- mathport name: «expr![ ,]»
notation3"!["(l", "* => foldr (h t => vecCons h t) vecEmpty)"]" => l

#print Matrix.vecHead /-
/-- `vec_head v` gives the first entry of the vector `v` -/
def vecHead {n : ℕ} (v : Fin n.succ → α) : α :=
  v 0
#align matrix.vec_head Matrix.vecHead
-/

#print Matrix.vecTail /-
/-- `vec_tail v` gives a vector consisting of all entries of `v` except the first -/
def vecTail {n : ℕ} (v : Fin n.succ → α) : Fin n → α :=
  v ∘ Fin.succ
#align matrix.vec_tail Matrix.vecTail
-/

variable {m n : ℕ}

#print PiFin.hasRepr /-
/-- Use `![...]` notation for displaying a vector `fin n → α`, for example:

```
#eval ![1, 2] + ![3, 4] -- ![4, 6]
```
-/
instance PiFin.hasRepr [Repr α] : Repr (Fin n → α)
    where repr f :=
    "![" ++ String.intercalate ", " ((List.finRange n).map fun n => repr (f n)) ++ "]"
#align pi_fin.has_repr PiFin.hasRepr
-/

end MatrixNotation

variable {m n o : ℕ} {m' n' o' : Type _}

#print Matrix.empty_eq /-
theorem empty_eq (v : Fin 0 → α) : v = ![] :=
  Subsingleton.elim _ _
#align matrix.empty_eq Matrix.empty_eq
-/

section Val

#print Matrix.head_fin_const /-
@[simp]
theorem head_fin_const (a : α) : (vecHead fun i : Fin (n + 1) => a) = a :=
  rfl
#align matrix.head_fin_const Matrix.head_fin_const
-/

/- warning: matrix.cons_val_zero -> Matrix.cons_val_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Nat} (x : α) (u : (Fin m) -> α), Eq.{succ u1} α (Matrix.vecCons.{u1} α m x u (OfNat.ofNat.{0} (Fin (Nat.succ m)) 0 (OfNat.mk.{0} (Fin (Nat.succ m)) 0 (Zero.zero.{0} (Fin (Nat.succ m)) (Fin.hasZeroOfNeZero (Nat.succ m) (NeZero.succ m)))))) x
but is expected to have type
  forall {α : Type.{u1}} {m : Nat} (x : α) (u : (Fin m) -> α), Eq.{succ u1} α (Matrix.vecCons.{u1} α m x u (OfNat.ofNat.{0} (Fin (Nat.succ m)) 0 (Fin.instOfNatFin (Nat.succ m) 0 (NeZero.succ m)))) x
Case conversion may be inaccurate. Consider using '#align matrix.cons_val_zero Matrix.cons_val_zeroₓ'. -/
@[simp]
theorem cons_val_zero (x : α) (u : Fin m → α) : vecCons x u 0 = x :=
  rfl
#align matrix.cons_val_zero Matrix.cons_val_zero

#print Matrix.cons_val_zero' /-
theorem cons_val_zero' (h : 0 < m.succ) (x : α) (u : Fin m → α) : vecCons x u ⟨0, h⟩ = x :=
  rfl
#align matrix.cons_val_zero' Matrix.cons_val_zero'
-/

#print Matrix.cons_val_succ /-
@[simp]
theorem cons_val_succ (x : α) (u : Fin m → α) (i : Fin m) : vecCons x u i.succ = u i := by
  simp [vec_cons]
#align matrix.cons_val_succ Matrix.cons_val_succ
-/

#print Matrix.cons_val_succ' /-
@[simp]
theorem cons_val_succ' {i : ℕ} (h : i.succ < m.succ) (x : α) (u : Fin m → α) :
    vecCons x u ⟨i.succ, h⟩ = u ⟨i, Nat.lt_of_succ_lt_succ h⟩ := by
  simp only [vec_cons, Fin.cons, Fin.cases_succ']
#align matrix.cons_val_succ' Matrix.cons_val_succ'
-/

#print Matrix.head_cons /-
@[simp]
theorem head_cons (x : α) (u : Fin m → α) : vecHead (vecCons x u) = x :=
  rfl
#align matrix.head_cons Matrix.head_cons
-/

#print Matrix.tail_cons /-
@[simp]
theorem tail_cons (x : α) (u : Fin m → α) : vecTail (vecCons x u) = u :=
  by
  ext
  simp [vec_tail]
#align matrix.tail_cons Matrix.tail_cons
-/

/- warning: matrix.empty_val' -> Matrix.empty_val' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n' : Type.{u2}} (j : n'), Eq.{succ u1} ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) => Matrix.vecEmpty.{max u2 u1} (n' -> α) i j) (Matrix.vecEmpty.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {n' : Type.{u1}} (j : n'), Eq.{succ u2} ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => Matrix.vecEmpty.{max u2 u1} (n' -> α) i j) (Matrix.vecEmpty.{u2} α)
Case conversion may be inaccurate. Consider using '#align matrix.empty_val' Matrix.empty_val'ₓ'. -/
@[simp]
theorem empty_val' {n' : Type _} (j : n') : (fun i => (![] : Fin 0 → n' → α) i j) = ![] :=
  empty_eq _
#align matrix.empty_val' Matrix.empty_val'

#print Matrix.cons_head_tail /-
@[simp]
theorem cons_head_tail (u : Fin m.succ → α) : vecCons (vecHead u) (vecTail u) = u :=
  Fin.cons_self_tail _
#align matrix.cons_head_tail Matrix.cons_head_tail
-/

/- warning: matrix.range_cons -> Matrix.range_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} (x : α) (u : (Fin n) -> α), Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, 1} α (Fin (Nat.succ n)) (Matrix.vecCons.{u1} α n x u)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x) (Set.range.{u1, 1} α (Fin n) u))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} (x : α) (u : (Fin n) -> α), Eq.{succ u1} (Set.{u1} α) (Set.range.{u1, 1} α (Fin (Nat.succ n)) (Matrix.vecCons.{u1} α n x u)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x) (Set.range.{u1, 1} α (Fin n) u))
Case conversion may be inaccurate. Consider using '#align matrix.range_cons Matrix.range_consₓ'. -/
@[simp]
theorem range_cons (x : α) (u : Fin n → α) : Set.range (vecCons x u) = {x} ∪ Set.range u :=
  Set.ext fun y => by simp [Fin.exists_fin_succ, eq_comm]
#align matrix.range_cons Matrix.range_cons

#print Matrix.range_empty /-
@[simp]
theorem range_empty (u : Fin 0 → α) : Set.range u = ∅ :=
  Set.range_eq_empty _
#align matrix.range_empty Matrix.range_empty
-/

#print Matrix.range_cons_empty /-
@[simp]
theorem range_cons_empty (x : α) (u : Fin 0 → α) : Set.range (Matrix.vecCons x u) = {x} := by
  rw [range_cons, range_empty, Set.union_empty]
#align matrix.range_cons_empty Matrix.range_cons_empty
-/

#print Matrix.range_cons_cons_empty /-
@[simp]
theorem range_cons_cons_empty (x y : α) (u : Fin 0 → α) :
    Set.range (vecCons x <| vecCons y u) = {x, y} := by
  rw [range_cons, range_cons_empty, Set.singleton_union]
#align matrix.range_cons_cons_empty Matrix.range_cons_cons_empty
-/

#print Matrix.vecCons_const /-
@[simp]
theorem vecCons_const (a : α) : (vecCons a fun k : Fin n => a) = fun _ => a :=
  funext <| Fin.forall_fin_succ.2 ⟨rfl, cons_val_succ _ _⟩
#align matrix.vec_cons_const Matrix.vecCons_const
-/

#print Matrix.vec_single_eq_const /-
theorem vec_single_eq_const (a : α) : ![a] = fun _ => a :=
  funext <| Unique.forall_iff.2 rfl
#align matrix.vec_single_eq_const Matrix.vec_single_eq_const
-/

#print Matrix.cons_val_one /-
/-- `![a, b, ...] 1` is equal to `b`.

  The simplifier needs a special lemma for length `≥ 2`, in addition to
  `cons_val_succ`, because `1 : fin 1 = 0 : fin 1`.
-/
@[simp]
theorem cons_val_one (x : α) (u : Fin m.succ → α) : vecCons x u 1 = vecHead u :=
  by
  rw [← Fin.succ_zero_eq_one, cons_val_succ]
  rfl
#align matrix.cons_val_one Matrix.cons_val_one
-/

#print Matrix.cons_val_fin_one /-
@[simp]
theorem cons_val_fin_one (x : α) (u : Fin 0 → α) (i : Fin 1) : vecCons x u i = x :=
  by
  refine' Fin.forall_fin_one.2 _ i
  rfl
#align matrix.cons_val_fin_one Matrix.cons_val_fin_one
-/

#print Matrix.cons_fin_one /-
theorem cons_fin_one (x : α) (u : Fin 0 → α) : vecCons x u = fun _ => x :=
  funext (cons_val_fin_one x u)
#align matrix.cons_fin_one Matrix.cons_fin_one
-/

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


#print Matrix.vecAppend /-
/-- `vec_append ho u v` appends two vectors of lengths `m` and `n` to produce
one of length `o = m + n`. This is a variant of `fin.append` with an additional `ho` argument,
which provides control of definitional equality for the vector length.

This turns out to be helpful when providing simp lemmas to reduce `![a, b, c] n`, and also means
that `vec_append ho u v 0` is valid. `fin.append u v 0` is not valid in this case because there is
no `has_zero (fin (m + n))` instance. -/
def vecAppend {α : Type _} {o : ℕ} (ho : o = m + n) (u : Fin m → α) (v : Fin n → α) : Fin o → α :=
  Fin.append u v ∘ Fin.cast ho
#align matrix.vec_append Matrix.vecAppend
-/

/- warning: matrix.vec_append_eq_ite -> Matrix.vecAppend_eq_ite is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat} {α : Type.{u1}} {o : Nat} (ho : Eq.{1} Nat o (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n)) (u : (Fin m) -> α) (v : (Fin n) -> α), Eq.{succ u1} ((Fin o) -> α) (Matrix.vecAppend.{u1} m n α o ho u v) (fun (i : Fin o) => dite.{succ u1} α (LT.lt.{0} Nat Nat.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin o) Nat (HasLiftT.mk.{1, 1} (Fin o) Nat (CoeTCₓ.coe.{1, 1} (Fin o) Nat (coeBase.{1, 1} (Fin o) Nat (Fin.coeToNat o)))) i) m) (Nat.decidableLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin o) Nat (HasLiftT.mk.{1, 1} (Fin o) Nat (CoeTCₓ.coe.{1, 1} (Fin o) Nat (coeBase.{1, 1} (Fin o) Nat (Fin.coeToNat o)))) i) m) (fun (h : LT.lt.{0} Nat Nat.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin o) Nat (HasLiftT.mk.{1, 1} (Fin o) Nat (CoeTCₓ.coe.{1, 1} (Fin o) Nat (coeBase.{1, 1} (Fin o) Nat (Fin.coeToNat o)))) i) m) => u (Fin.mk m ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin o) Nat (HasLiftT.mk.{1, 1} (Fin o) Nat (CoeTCₓ.coe.{1, 1} (Fin o) Nat (coeBase.{1, 1} (Fin o) Nat (Fin.coeToNat o)))) i) h)) (fun (h : Not (LT.lt.{0} Nat Nat.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin o) Nat (HasLiftT.mk.{1, 1} (Fin o) Nat (CoeTCₓ.coe.{1, 1} (Fin o) Nat (coeBase.{1, 1} (Fin o) Nat (Fin.coeToNat o)))) i) m)) => v (Fin.mk n (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin o) Nat (HasLiftT.mk.{1, 1} (Fin o) Nat (CoeTCₓ.coe.{1, 1} (Fin o) Nat (coeBase.{1, 1} (Fin o) Nat (Fin.coeToNat o)))) i) m) (Iff.mpr (LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (LinearOrder.toPartialOrder.{0} Nat Nat.linearOrder))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin o) Nat (HasLiftT.mk.{1, 1} (Fin o) Nat (CoeTCₓ.coe.{1, 1} (Fin o) Nat (coeBase.{1, 1} (Fin o) Nat (Fin.coeToNat o)))) i) m) n) (LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (LinearOrder.toPartialOrder.{0} Nat Nat.linearOrder))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin o) Nat (HasLiftT.mk.{1, 1} (Fin o) Nat (CoeTCₓ.coe.{1, 1} (Fin o) Nat (coeBase.{1, 1} (Fin o) Nat (Fin.coeToNat o)))) i) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toHasAdd.{0} Nat (AddCommSemigroup.toAddSemigroup.{0} Nat Nat.addCommSemigroup))) m n)) (tsub_lt_iff_left.{0} Nat Nat.addCommSemigroup (LinearOrder.toPartialOrder.{0} Nat Nat.linearOrder) (CanonicallyOrderedAddMonoid.existsAddOfLE.{0} Nat (CanonicallyOrderedCommSemiring.toCanonicallyOrderedAddMonoid.{0} Nat Nat.canonicallyOrderedCommSemiring)) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)) Nat.hasSub Nat.hasOrderedSub ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin o) Nat (HasLiftT.mk.{1, 1} (Fin o) Nat (CoeTCₓ.coe.{1, 1} (Fin o) Nat (coeBase.{1, 1} (Fin o) Nat (Fin.coeToNat o)))) i) m n (AddLeftCancelSemigroup.contravariant_add_le_of_contravariant_add_lt.{0} Nat (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Nat (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)) (OrderedCancelAddCommMonoid.to_contravariantClass_left.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (le_of_not_lt.{0} Nat Nat.linearOrder m ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin o) Nat (HasLiftT.mk.{1, 1} (Fin o) Nat (CoeTCₓ.coe.{1, 1} (Fin o) Nat (coeBase.{1, 1} (Fin o) Nat (Fin.coeToNat o)))) i) h)) (Eq.subst.{1} Nat (fun (_x : Nat) => LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (LinearOrder.toPartialOrder.{0} Nat Nat.linearOrder))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin o) Nat (HasLiftT.mk.{1, 1} (Fin o) Nat (CoeTCₓ.coe.{1, 1} (Fin o) Nat (coeBase.{1, 1} (Fin o) Nat (Fin.coeToNat o)))) i) _x) o (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m n) ho (Fin.property o i))))))
but is expected to have type
  forall {m : Nat} {n : Nat} {α : Type.{u1}} {o : Nat} (ho : Eq.{1} Nat o (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n)) (u : (Fin m) -> α) (v : (Fin n) -> α), Eq.{succ u1} ((Fin o) -> α) (Matrix.vecAppend.{u1} m n α o ho u v) (fun (i : Fin o) => dite.{succ u1} α (LT.lt.{0} Nat instLTNat (Fin.val o i) m) (Nat.decLt (Fin.val o i) m) (fun (h : LT.lt.{0} Nat instLTNat (Fin.val o i) m) => u (Fin.mk m (Fin.val o i) h)) (fun (h : Not (LT.lt.{0} Nat instLTNat (Fin.val o i) m)) => v (Fin.mk n (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fin.val o i) m) (Iff.mpr (LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (LinearOrder.toPartialOrder.{0} Nat Nat.linearOrder))) (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) (Fin.val o i) m) n) (LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (LinearOrder.toPartialOrder.{0} Nat Nat.linearOrder))) (Fin.val o i) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddSemigroup.toAdd.{0} Nat (AddCommSemigroup.toAddSemigroup.{0} Nat Nat.addCommSemigroup))) m n)) (tsub_lt_iff_left.{0} Nat Nat.addCommSemigroup (LinearOrder.toPartialOrder.{0} Nat Nat.linearOrder) (CanonicallyOrderedAddMonoid.existsAddOfLE.{0} Nat (CanonicallyOrderedCommSemiring.toCanonicallyOrderedAddMonoid.{0} Nat Nat.canonicallyOrderedCommSemiring)) (OrderedAddCommMonoid.to_covariantClass_left.{0} Nat (OrderedSemiring.toOrderedAddCommMonoid.{0} Nat Nat.orderedSemiring)) instSubNat Nat.instOrderedSubNatInstLENatInstAddNatInstSubNat (Fin.val o i) m n (AddLeftCancelSemigroup.contravariant_add_le_of_contravariant_add_lt.{0} Nat (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Nat (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring) (OrderedCancelAddCommMonoid.to_contravariantClass_left.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (le_of_not_lt.{0} Nat Nat.linearOrder m (Fin.val o i) h)) (Eq.rec.{0, 1} Nat o (fun (x._@.Mathlib.Data.Fin.VecNotation._hyg.1667 : Nat) (h._@.Mathlib.Data.Fin.VecNotation._hyg.1668 : Eq.{1} Nat o x._@.Mathlib.Data.Fin.VecNotation._hyg.1667) => LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (LinearOrder.toPartialOrder.{0} Nat Nat.linearOrder))) (Fin.val o i) x._@.Mathlib.Data.Fin.VecNotation._hyg.1667) (Fin.isLt o i) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m n) ho)))))
Case conversion may be inaccurate. Consider using '#align matrix.vec_append_eq_ite Matrix.vecAppend_eq_iteₓ'. -/
theorem vecAppend_eq_ite {α : Type _} {o : ℕ} (ho : o = m + n) (u : Fin m → α) (v : Fin n → α) :
    vecAppend ho u v = fun i =>
      if h : (i : ℕ) < m then u ⟨i, h⟩
      else v ⟨(i : ℕ) - m, (tsub_lt_iff_left (le_of_not_lt h)).2 (ho ▸ i.property)⟩ :=
  by
  ext i
  rw [vec_append, Fin.append, Function.comp_apply, Fin.addCases]
  congr with hi
  simp only [eq_rec_constant]
  rfl
#align matrix.vec_append_eq_ite Matrix.vecAppend_eq_ite

/- warning: matrix.vec_append_apply_zero -> Matrix.vecAppend_apply_zero is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat} {α : Type.{u1}} {o : Nat} (ho : Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) o (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) n)) (u : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> α) (v : (Fin n) -> α), Eq.{succ u1} α (Matrix.vecAppend.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) n α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) o (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) ho u v (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) o (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) o (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) o (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) o (One.one.{0} Nat Nat.hasOne)) (NeZero.succ o)))))) (u (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (One.one.{0} Nat Nat.hasOne)) (NeZero.succ m))))))
but is expected to have type
  forall {m : Nat} {n : Nat} {α : Type.{u1}} {o : Nat} (ho : Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) o (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) n)) (u : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> α) (v : (Fin n) -> α), Eq.{succ u1} α (Matrix.vecAppend.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) n α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) o (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) ho u v (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) o (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) o (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ o)))) (u (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 0 (NeZero.succ m))))
Case conversion may be inaccurate. Consider using '#align matrix.vec_append_apply_zero Matrix.vecAppend_apply_zeroₓ'. -/
@[simp]
theorem vecAppend_apply_zero {α : Type _} {o : ℕ} (ho : o + 1 = m + 1 + n) (u : Fin (m + 1) → α)
    (v : Fin n → α) : vecAppend ho u v 0 = u 0 :=
  rfl
#align matrix.vec_append_apply_zero Matrix.vecAppend_apply_zero

/- warning: matrix.empty_vec_append -> Matrix.empty_vecAppend is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} (v : (Fin n) -> α), Eq.{succ u1} ((Fin n) -> α) (Matrix.vecAppend.{u1} (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat (AddZeroClass.toHasZero.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid))))) n α n (Eq.symm.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddZeroClass.toHasAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat (AddZeroClass.toHasZero.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid))))) n) n (zero_add.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) n)) (Matrix.vecEmpty.{u1} α) v) v
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} (v : (Fin n) -> α), Eq.{succ u1} ((Fin n) -> α) (Matrix.vecAppend.{u1} (OfNat.ofNat.{0} Nat 0 (Zero.toOfNat0.{0} Nat (AddZeroClass.toZero.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) n α n (Eq.symm.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat (AddZeroClass.toAdd.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid))) (OfNat.ofNat.{0} Nat 0 (Zero.toOfNat0.{0} Nat (AddZeroClass.toZero.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid)))) n) n (zero_add.{0} Nat (AddMonoid.toAddZeroClass.{0} Nat Nat.addMonoid) n)) (Matrix.vecEmpty.{u1} α) v) v
Case conversion may be inaccurate. Consider using '#align matrix.empty_vec_append Matrix.empty_vecAppendₓ'. -/
@[simp]
theorem empty_vecAppend (v : Fin n → α) : vecAppend (zero_add _).symm ![] v = v :=
  by
  ext
  simp [vec_append_eq_ite]
#align matrix.empty_vec_append Matrix.empty_vecAppend

#print Matrix.cons_vecAppend /-
@[simp]
theorem cons_vecAppend (ho : o + 1 = m + 1 + n) (x : α) (u : Fin m → α) (v : Fin n → α) :
    vecAppend ho (vecCons x u) v =
      vecCons x
        (vecAppend (by rwa [add_assoc, add_comm 1, ← add_assoc, add_right_cancel_iff] at ho) u v) :=
  by
  ext i
  simp_rw [vec_append_eq_ite]
  split_ifs with h
  · rcases i with ⟨⟨⟩ | i, hi⟩
    · simp
    · simp only [Nat.succ_eq_add_one, add_lt_add_iff_right, Fin.val_mk] at h
      simp [h]
  · rcases i with ⟨⟨⟩ | i, hi⟩
    · simpa using h
    · rw [not_lt, Fin.val_mk, Nat.succ_eq_add_one, add_le_add_iff_right] at h
      simp [h]
#align matrix.cons_vec_append Matrix.cons_vecAppend
-/

#print Matrix.vecAlt0 /-
/-- `vec_alt0 v` gives a vector with half the length of `v`, with
only alternate elements (even-numbered). -/
def vecAlt0 (hm : m = n + n) (v : Fin m → α) (k : Fin n) : α :=
  v ⟨(k : ℕ) + k, hm.symm ▸ add_lt_add k.property k.property⟩
#align matrix.vec_alt0 Matrix.vecAlt0
-/

#print Matrix.vecAlt1 /-
/-- `vec_alt1 v` gives a vector with half the length of `v`, with
only alternate elements (odd-numbered). -/
def vecAlt1 (hm : m = n + n) (v : Fin m → α) (k : Fin n) : α :=
  v ⟨(k : ℕ) + k + 1, hm.symm ▸ Nat.add_succ_lt_add k.property k.property⟩
#align matrix.vec_alt1 Matrix.vecAlt1
-/

#print Matrix.vecAlt0_vecAppend /-
theorem vecAlt0_vecAppend (v : Fin n → α) : vecAlt0 rfl (vecAppend rfl v v) = v ∘ bit0 :=
  by
  ext i
  simp_rw [Function.comp, bit0, vec_alt0, vec_append_eq_ite]
  split_ifs with h <;> congr
  · rw [Fin.val_mk] at h
    simp only [Fin.ext_iff, Fin.val_add, Fin.val_mk]
    exact (Nat.mod_eq_of_lt h).symm
  · rw [Fin.val_mk, not_lt] at h
    simp only [Fin.ext_iff, Fin.val_add, Fin.val_mk, Nat.mod_eq_sub_mod h]
    refine' (Nat.mod_eq_of_lt _).symm
    rw [tsub_lt_iff_left h]
    exact add_lt_add i.property i.property
#align matrix.vec_alt0_vec_append Matrix.vecAlt0_vecAppend
-/

#print Matrix.vecAlt1_vecAppend /-
theorem vecAlt1_vecAppend (v : Fin (n + 1) → α) : vecAlt1 rfl (vecAppend rfl v v) = v ∘ bit1 :=
  by
  ext i
  simp_rw [Function.comp, vec_alt1, vec_append_eq_ite]
  cases n
  · simp
    congr
  · split_ifs with h <;> simp_rw [bit1, bit0] <;> congr
    · simp only [Fin.ext_iff, Fin.val_add, Fin.val_mk]
      rw [Fin.val_mk] at h
      rw [Fin.val_one]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_succ_lt h)]
      rw [Nat.mod_eq_of_lt h]
    · rw [Fin.val_mk, not_lt] at h
      simp only [Fin.ext_iff, Fin.val_add, Fin.val_mk, Nat.mod_add_mod, Fin.val_one,
        Nat.mod_eq_sub_mod h]
      refine' (Nat.mod_eq_of_lt _).symm
      rw [tsub_lt_iff_left h]
      exact Nat.add_succ_lt_add i.property i.property
#align matrix.vec_alt1_vec_append Matrix.vecAlt1_vecAppend
-/

/- warning: matrix.vec_head_vec_alt0 -> Matrix.vecHead_vecAlt0 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {m : Nat} {n : Nat} (hm : Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (v : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) -> α), Eq.{succ u1} α (Matrix.vecHead.{u1} α n (Matrix.vecAlt0.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Nat.succ n) hm v)) (v (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 0 (OfNat.mk.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) 0 (Zero.zero.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) (Fin.hasZeroOfNeZero (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (NeZero.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) m (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {α : Type.{u1}} {m : Nat} {n : Nat} (hm : Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (v : (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) -> α), Eq.{succ u1} α (Matrix.vecHead.{u1} α n (Matrix.vecAlt0.{u1} α (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Nat.succ n) hm v)) (v (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) 0 (Fin.instOfNatFin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (NeZero.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) m (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align matrix.vec_head_vec_alt0 Matrix.vecHead_vecAlt0ₓ'. -/
@[simp]
theorem vecHead_vecAlt0 (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) → α) :
    vecHead (vecAlt0 hm v) = v 0 :=
  rfl
#align matrix.vec_head_vec_alt0 Matrix.vecHead_vecAlt0

#print Matrix.vecHead_vecAlt1 /-
@[simp]
theorem vecHead_vecAlt1 (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) → α) :
    vecHead (vecAlt1 hm v) = v 1 := by simp [vec_head, vec_alt1]
#align matrix.vec_head_vec_alt1 Matrix.vecHead_vecAlt1
-/

#print Matrix.cons_vec_bit0_eq_alt0 /-
@[simp]
theorem cons_vec_bit0_eq_alt0 (x : α) (u : Fin n → α) (i : Fin (n + 1)) :
    vecCons x u (bit0 i) = vecAlt0 rfl (vecAppend rfl (vecCons x u) (vecCons x u)) i := by
  rw [vec_alt0_vec_append]
#align matrix.cons_vec_bit0_eq_alt0 Matrix.cons_vec_bit0_eq_alt0
-/

#print Matrix.cons_vec_bit1_eq_alt1 /-
@[simp]
theorem cons_vec_bit1_eq_alt1 (x : α) (u : Fin n → α) (i : Fin (n + 1)) :
    vecCons x u (bit1 i) = vecAlt1 rfl (vecAppend rfl (vecCons x u) (vecCons x u)) i := by
  rw [vec_alt1_vec_append]
#align matrix.cons_vec_bit1_eq_alt1 Matrix.cons_vec_bit1_eq_alt1
-/

#print Matrix.cons_vecAlt0 /-
@[simp]
theorem cons_vecAlt0 (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m → α) :
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
#align matrix.cons_vec_alt0 Matrix.cons_vecAlt0
-/

#print Matrix.empty_vecAlt0 /-
-- Although proved by simp, extracting element 8 of a five-element
-- vector does not work by simp unless this lemma is present.
@[simp]
theorem empty_vecAlt0 (α) {h} : vecAlt0 h (![] : Fin 0 → α) = ![] := by simp
#align matrix.empty_vec_alt0 Matrix.empty_vecAlt0
-/

#print Matrix.cons_vecAlt1 /-
@[simp]
theorem cons_vecAlt1 (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m → α) :
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
#align matrix.cons_vec_alt1 Matrix.cons_vecAlt1
-/

#print Matrix.empty_vecAlt1 /-
-- Although proved by simp, extracting element 9 of a five-element
-- vector does not work by simp unless this lemma is present.
@[simp]
theorem empty_vecAlt1 (α) {h} : vecAlt1 h (![] : Fin 0 → α) = ![] := by simp
#align matrix.empty_vec_alt1 Matrix.empty_vecAlt1
-/

end Val

section Smul

variable {M : Type _} [SMul M α]

/- warning: matrix.smul_empty -> Matrix.smul_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : SMul.{u2, u1} M α] (x : M) (v : (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α), Eq.{succ u1} ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α) (SMul.smul.{u2, u1} M ((Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> α) (Function.hasSMul.{0, u2, u1} (Fin (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) M α _inst_1) x v) (Matrix.vecEmpty.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : SMul.{u1, u2} M α] (x : M) (v : (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α), Eq.{succ u2} ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) (HSMul.hSMul.{u1, u2, u2} M ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) (instHSMul.{u1, u2} M ((Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α) (Pi.instSMul.{0, u2, u1} (Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) M (fun (a._@.Mathlib.Data.Fin.VecNotation._hyg.3286 : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => α) (fun (i : Fin (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) => _inst_1))) x v) (Matrix.vecEmpty.{u2} α)
Case conversion may be inaccurate. Consider using '#align matrix.smul_empty Matrix.smul_emptyₓ'. -/
@[simp]
theorem smul_empty (x : M) (v : Fin 0 → α) : x • v = ![] :=
  empty_eq _
#align matrix.smul_empty Matrix.smul_empty

/- warning: matrix.smul_cons -> Matrix.smul_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} {M : Type.{u2}} [_inst_1 : SMul.{u2, u1} M α] (x : M) (y : α) (v : (Fin n) -> α), Eq.{succ u1} ((Fin (Nat.succ n)) -> α) (SMul.smul.{u2, u1} M ((Fin (Nat.succ n)) -> α) (Function.hasSMul.{0, u2, u1} (Fin (Nat.succ n)) M α _inst_1) x (Matrix.vecCons.{u1} α n y v)) (Matrix.vecCons.{u1} α n (SMul.smul.{u2, u1} M α _inst_1 x y) (SMul.smul.{u2, u1} M ((Fin n) -> α) (Function.hasSMul.{0, u2, u1} (Fin n) M α _inst_1) x v))
but is expected to have type
  forall {α : Type.{u2}} {n : Nat} {M : Type.{u1}} [_inst_1 : SMul.{u1, u2} M α] (x : M) (y : α) (v : (Fin n) -> α), Eq.{succ u2} ((Fin (Nat.succ n)) -> α) (HSMul.hSMul.{u1, u2, u2} M ((Fin (Nat.succ n)) -> α) ((Fin (Nat.succ n)) -> α) (instHSMul.{u1, u2} M ((Fin (Nat.succ n)) -> α) (Pi.instSMul.{0, u2, u1} (Fin (Nat.succ n)) M (fun (a._@.Mathlib.Data.Fin.VecNotation._hyg.29 : Fin (Nat.succ n)) => α) (fun (i : Fin (Nat.succ n)) => _inst_1))) x (Matrix.vecCons.{u2} α n y v)) (Matrix.vecCons.{u2} α n (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α _inst_1) x y) (HSMul.hSMul.{u1, u2, u2} M ((Fin n) -> α) ((Fin n) -> α) (instHSMul.{u1, u2} M ((Fin n) -> α) (Pi.instSMul.{0, u2, u1} (Fin n) M (fun (a._@.Mathlib.Data.Fin.VecNotation._hyg.3324 : Fin n) => α) (fun (i : Fin n) => _inst_1))) x v))
Case conversion may be inaccurate. Consider using '#align matrix.smul_cons Matrix.smul_consₓ'. -/
@[simp]
theorem smul_cons (x : M) (y : α) (v : Fin n → α) : x • vecCons y v = vecCons (x • y) (x • v) :=
  by
  ext i
  refine' Fin.cases _ _ i <;> simp
#align matrix.smul_cons Matrix.smul_cons

end Smul

section Add

variable [Add α]

#print Matrix.empty_add_empty /-
@[simp]
theorem empty_add_empty (v w : Fin 0 → α) : v + w = ![] :=
  empty_eq _
#align matrix.empty_add_empty Matrix.empty_add_empty
-/

#print Matrix.cons_add /-
@[simp]
theorem cons_add (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    vecCons x v + w = vecCons (x + vecHead w) (v + vecTail w) :=
  by
  ext i
  refine' Fin.cases _ _ i <;> simp [vec_head, vec_tail]
#align matrix.cons_add Matrix.cons_add
-/

#print Matrix.add_cons /-
@[simp]
theorem add_cons (v : Fin n.succ → α) (y : α) (w : Fin n → α) :
    v + vecCons y w = vecCons (vecHead v + y) (vecTail v + w) :=
  by
  ext i
  refine' Fin.cases _ _ i <;> simp [vec_head, vec_tail]
#align matrix.add_cons Matrix.add_cons
-/

#print Matrix.cons_add_cons /-
@[simp]
theorem cons_add_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    vecCons x v + vecCons y w = vecCons (x + y) (v + w) := by simp
#align matrix.cons_add_cons Matrix.cons_add_cons
-/

#print Matrix.head_add /-
@[simp]
theorem head_add (a b : Fin n.succ → α) : vecHead (a + b) = vecHead a + vecHead b :=
  rfl
#align matrix.head_add Matrix.head_add
-/

#print Matrix.tail_add /-
@[simp]
theorem tail_add (a b : Fin n.succ → α) : vecTail (a + b) = vecTail a + vecTail b :=
  rfl
#align matrix.tail_add Matrix.tail_add
-/

end Add

section Sub

variable [Sub α]

#print Matrix.empty_sub_empty /-
@[simp]
theorem empty_sub_empty (v w : Fin 0 → α) : v - w = ![] :=
  empty_eq _
#align matrix.empty_sub_empty Matrix.empty_sub_empty
-/

#print Matrix.cons_sub /-
@[simp]
theorem cons_sub (x : α) (v : Fin n → α) (w : Fin n.succ → α) :
    vecCons x v - w = vecCons (x - vecHead w) (v - vecTail w) :=
  by
  ext i
  refine' Fin.cases _ _ i <;> simp [vec_head, vec_tail]
#align matrix.cons_sub Matrix.cons_sub
-/

#print Matrix.sub_cons /-
@[simp]
theorem sub_cons (v : Fin n.succ → α) (y : α) (w : Fin n → α) :
    v - vecCons y w = vecCons (vecHead v - y) (vecTail v - w) :=
  by
  ext i
  refine' Fin.cases _ _ i <;> simp [vec_head, vec_tail]
#align matrix.sub_cons Matrix.sub_cons
-/

#print Matrix.cons_sub_cons /-
@[simp]
theorem cons_sub_cons (x : α) (v : Fin n → α) (y : α) (w : Fin n → α) :
    vecCons x v - vecCons y w = vecCons (x - y) (v - w) := by simp
#align matrix.cons_sub_cons Matrix.cons_sub_cons
-/

#print Matrix.head_sub /-
@[simp]
theorem head_sub (a b : Fin n.succ → α) : vecHead (a - b) = vecHead a - vecHead b :=
  rfl
#align matrix.head_sub Matrix.head_sub
-/

#print Matrix.tail_sub /-
@[simp]
theorem tail_sub (a b : Fin n.succ → α) : vecTail (a - b) = vecTail a - vecTail b :=
  rfl
#align matrix.tail_sub Matrix.tail_sub
-/

end Sub

section Zero

variable [Zero α]

#print Matrix.zero_empty /-
@[simp]
theorem zero_empty : (0 : Fin 0 → α) = ![] :=
  empty_eq _
#align matrix.zero_empty Matrix.zero_empty
-/

#print Matrix.cons_zero_zero /-
@[simp]
theorem cons_zero_zero : vecCons (0 : α) (0 : Fin n → α) = 0 :=
  by
  ext (i j)
  refine' Fin.cases _ _ i
  · rfl
  simp
#align matrix.cons_zero_zero Matrix.cons_zero_zero
-/

#print Matrix.head_zero /-
@[simp]
theorem head_zero : vecHead (0 : Fin n.succ → α) = 0 :=
  rfl
#align matrix.head_zero Matrix.head_zero
-/

#print Matrix.tail_zero /-
@[simp]
theorem tail_zero : vecTail (0 : Fin n.succ → α) = 0 :=
  rfl
#align matrix.tail_zero Matrix.tail_zero
-/

#print Matrix.cons_eq_zero_iff /-
@[simp]
theorem cons_eq_zero_iff {v : Fin n → α} {x : α} : vecCons x v = 0 ↔ x = 0 ∧ v = 0 :=
  ⟨fun h =>
    ⟨congr_fun h 0, by
      convert congr_arg vec_tail h
      simp⟩,
    fun ⟨hx, hv⟩ => by simp [hx, hv]⟩
#align matrix.cons_eq_zero_iff Matrix.cons_eq_zero_iff
-/

open Classical

#print Matrix.cons_nonzero_iff /-
theorem cons_nonzero_iff {v : Fin n → α} {x : α} : vecCons x v ≠ 0 ↔ x ≠ 0 ∨ v ≠ 0 :=
  ⟨fun h => not_and_or.mp (h ∘ cons_eq_zero_iff.mpr), fun h =>
    mt cons_eq_zero_iff.mp (not_and_or.mpr h)⟩
#align matrix.cons_nonzero_iff Matrix.cons_nonzero_iff
-/

end Zero

section Neg

variable [Neg α]

#print Matrix.neg_empty /-
@[simp]
theorem neg_empty (v : Fin 0 → α) : -v = ![] :=
  empty_eq _
#align matrix.neg_empty Matrix.neg_empty
-/

#print Matrix.neg_cons /-
@[simp]
theorem neg_cons (x : α) (v : Fin n → α) : -vecCons x v = vecCons (-x) (-v) :=
  by
  ext i
  refine' Fin.cases _ _ i <;> simp
#align matrix.neg_cons Matrix.neg_cons
-/

#print Matrix.head_neg /-
@[simp]
theorem head_neg (a : Fin n.succ → α) : vecHead (-a) = -vecHead a :=
  rfl
#align matrix.head_neg Matrix.head_neg
-/

#print Matrix.tail_neg /-
@[simp]
theorem tail_neg (a : Fin n.succ → α) : vecTail (-a) = -vecTail a :=
  rfl
#align matrix.tail_neg Matrix.tail_neg
-/

end Neg

end Matrix

