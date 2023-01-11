/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fin.fin2
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

/-!
# Inductive type variant of `fin`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`fin` is defined as a subtype of `ℕ`. This file defines an equivalent type, `fin2`, which is
defined inductively. This is useful for its induction principle and different definitional
equalities.

## Main declarations

* `fin2 n`: Inductive type variant of `fin n`. `fz` corresponds to `0` and `fs n` corresponds to
  `n`.
* `to_nat`, `opt_of_nat`, `of_nat'`: Conversions to and from `ℕ`. `of_nat' m` takes a proof that
  `m < n` through the class `is_lt`.
* `add k`: Takes `i : fin2 n` to `i + k : fin2 (n + k)`.
* `left`: Embeds `fin2 n` into `fin2 (n + k)`.
* `insert_perm a`: Permutation of `fin2 n` which cycles `0, ..., a - 1` and leaves `a, ..., n - 1`
  unchanged.
* `remap_left f`: Function `fin2 (m + k) → fin2 (n + k)` by applying `f : fin m → fin n` to
  `0, ..., m - 1` and sending `m + i` to `n + i`.
-/


open Nat

universe u

#print Fin2 /-
/-- An alternate definition of `fin n` defined as an inductive type instead of a subtype of `ℕ`. -/
inductive Fin2 : ℕ → Type/-- `0` as a member of `fin (succ n)` (`fin 0` is empty) -/

  | fz {n} : Fin2 (succ n)/-- `n` as a member of `fin (succ n)` -/

  | fs {n} : Fin2 n → Fin2 (succ n)
#align fin2 Fin2
-/

namespace Fin2

#print Fin2.cases' /-
/-- Define a dependent function on `fin2 (succ n)` by giving its value at
zero (`H1`) and by giving a dependent function on the rest (`H2`). -/
@[elab_as_elim]
protected def cases' {n} {C : Fin2 (succ n) → Sort u} (H1 : C fz) (H2 : ∀ n, C (fs n)) :
    ∀ i : Fin2 (succ n), C i
  | fz => H1
  | fs n => H2 n
#align fin2.cases' Fin2.cases'
-/

#print Fin2.elim0 /-
/-- Ex falso. The dependent eliminator for the empty `fin2 0` type. -/
def elim0 {C : Fin2 0 → Sort u} : ∀ i : Fin2 0, C i :=
  fun.
#align fin2.elim0 Fin2.elim0
-/

#print Fin2.toNat /-
/-- Converts a `fin2` into a natural. -/
def toNat : ∀ {n}, Fin2 n → ℕ
  | _, @fz n => 0
  | _, @fs n i => succ (to_nat i)
#align fin2.to_nat Fin2.toNat
-/

#print Fin2.optOfNat /-
/-- Converts a natural into a `fin2` if it is in range -/
def optOfNat : ∀ {n} (k : ℕ), Option (Fin2 n)
  | 0, _ => none
  | succ n, 0 => some fz
  | succ n, succ k => fs <$> @opt_of_nat n k
#align fin2.opt_of_nat Fin2.optOfNat
-/

#print Fin2.add /-
/-- `i + k : fin2 (n + k)` when `i : fin2 n` and `k : ℕ` -/
def add {n} (i : Fin2 n) : ∀ k, Fin2 (n + k)
  | 0 => i
  | succ k => fs (add k)
#align fin2.add Fin2.add
-/

#print Fin2.left /-
/-- `left k` is the embedding `fin2 n → fin2 (k + n)` -/
def left (k) : ∀ {n}, Fin2 n → Fin2 (k + n)
  | _, @fz n => fz
  | _, @fs n i => fs (left i)
#align fin2.left Fin2.left
-/

#print Fin2.insertPerm /-
/-- `insert_perm a` is a permutation of `fin2 n` with the following properties:
  * `insert_perm a i = i+1` if `i < a`
  * `insert_perm a a = 0`
  * `insert_perm a i = i` if `i > a` -/
def insertPerm : ∀ {n}, Fin2 n → Fin2 n → Fin2 n
  | _, @fz n, @fz _ => fz
  | _, @fz n, @fs _ j => fs j
  | _, @fs (succ n) i, @fz _ => fs fz
  | _, @fs (succ n) i, @fs _ j =>
    match insert_perm i j with
    | fz => fz
    | fs k => fs (fs k)
#align fin2.insert_perm Fin2.insertPerm
-/

#print Fin2.remapLeft /-
/-- `remap_left f k : fin2 (m + k) → fin2 (n + k)` applies the function
  `f : fin2 m → fin2 n` to inputs less than `m`, and leaves the right part
  on the right (that is, `remap_left f k (m + i) = n + i`). -/
def remapLeft {m n} (f : Fin2 m → Fin2 n) : ∀ k, Fin2 (m + k) → Fin2 (n + k)
  | 0, i => f i
  | succ k, @fz _ => fz
  | succ k, @fs _ i => fs (remap_left _ i)
#align fin2.remap_left Fin2.remapLeft
-/

/-- This is a simple type class inference prover for proof obligations
  of the form `m < n` where `m n : ℕ`. -/
class IsLt (m n : ℕ) where
  h : m < n
#align fin2.is_lt Fin2.IsLt

instance IsLt.zero (n) : IsLt 0 (succ n) :=
  ⟨succ_pos _⟩
#align fin2.is_lt.zero Fin2.IsLt.zero

instance IsLt.succ (m n) [l : IsLt m n] : IsLt (succ m) (succ n) :=
  ⟨succ_lt_succ l.h⟩
#align fin2.is_lt.succ Fin2.IsLt.succ

/- warning: fin2.of_nat' -> Fin2.ofNat' is a dubious translation:
lean 3 declaration is
  forall {n : Nat} (m : Nat) [_inst_1 : Fin2.IsLt m n], Fin2 n
but is expected to have type
  forall {n : Nat} (m : Nat) [_inst_1 : Fin2.IsLT m n], Fin2 n
Case conversion may be inaccurate. Consider using '#align fin2.of_nat' Fin2.ofNat'ₓ'. -/
/-- Use type class inference to infer the boundedness proof, so that we can directly convert a
`nat` into a `fin2 n`. This supports notation like `&1 : fin 3`. -/
def ofNat' : ∀ {n} (m) [IsLt m n], Fin2 n
  | 0, m, ⟨h⟩ => absurd h (Nat.not_lt_zero _)
  | succ n, 0, ⟨h⟩ => fz
  | succ n, succ m, ⟨h⟩ => fs (@of_nat' n m ⟨lt_of_succ_lt_succ h⟩)
#align fin2.of_nat' Fin2.ofNat'

-- mathport name: «expr& »
local prefix:arg "&" => ofNat'

instance : Inhabited (Fin2 1) :=
  ⟨fz⟩

end Fin2

