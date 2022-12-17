/-
Copyright (c) 2021 Yakov Pechersky All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Mario Carneiro

! This file was ported from Lean 3 source module tactic.norm_fin
! leanprover-community/mathlib commit 11bb0c9152e5d14278fb0ac5e0be6d50e2c8fa05
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Basic
import Mathbin.Tactic.NormNum

/-!
# `norm_fin`

This file defines functions for dealing with `fin n` numbers as expressions.

## Main definitions

* `tactic.norm_fin.eval_ineq` is a `norm_num` plugin for normalizing equalities and inequalities of
  type `fin n`.

* `tactic.interactive.norm_fin` is a standalone tactic like `norm_num` for normalizing `fin n`
  expressions anywhere in the goal.

-/


namespace Tactic

namespace NormFin

open NormNum

/-- `normalize_fin n a b` means that `a : fin n` is equivalent to `b : ℕ` in the modular sense -
that is, `↑a ≡ b (mod n)`. This is used for translating the algebraic operations: addition,
multiplication, zero and one, which use modulo for reduction. -/
def NormalizeFin (n : ℕ) (a : Fin n) (b : ℕ) :=
  a.1 = b % n
#align tactic.norm_fin.normalize_fin Tactic.NormFin.NormalizeFin

/-- `normalize_fin_lt n a b` means that `a : fin n` is equivalent to `b : ℕ` in the embedding
sense - that is, `↑a = b`. This is used for operations that treat `fin n` as the subset
`{0, ..., n-1}` of `ℕ`. For example, `fin.succ : fin n → fin (n+1)` is thought of as the successor
function, but it does not lift to a map `zmod n → zmod (n+1)`; this addition only makes sense if
the input is strictly less than `n`.

`normalize_fin_lt n a b` is equivalent to `normalize_fin n a b ∧ b < n`. -/
def NormalizeFinLt (n : ℕ) (a : Fin n) (b : ℕ) :=
  a.1 = b
#align tactic.norm_fin.normalize_fin_lt Tactic.NormFin.NormalizeFinLt

theorem NormalizeFinLt.coe {n} {a : Fin n} {b : ℕ} (h : NormalizeFinLt n a b) : ↑a = b :=
  h
#align tactic.norm_fin.normalize_fin_lt.coe Tactic.NormFin.NormalizeFinLt.coe

theorem normalize_fin_iff {n : ℕ} [NeZero n] {a b} : NormalizeFin n a b ↔ a = Fin.ofNat' b :=
  Iff.symm (Fin.eq_iff_veq _ _)
#align tactic.norm_fin.normalize_fin_iff Tactic.NormFin.normalize_fin_iff

theorem NormalizeFinLt.mk {n a b n'} (hn : n = n') (h : NormalizeFin n a b) (h2 : b < n') :
    NormalizeFinLt n a b :=
  h.trans <| Nat.mod_eq_of_lt <| by rw [hn] <;> exact h2
#align tactic.norm_fin.normalize_fin_lt.mk Tactic.NormFin.NormalizeFinLt.mk

theorem NormalizeFinLt.lt {n a b} (h : NormalizeFinLt n a b) : b < n := by
  rw [← h.coe] <;> exact a.2
#align tactic.norm_fin.normalize_fin_lt.lt Tactic.NormFin.NormalizeFinLt.lt

theorem NormalizeFinLt.of {n a b} (h : NormalizeFinLt n a b) : NormalizeFin n a b :=
  h.trans <| Eq.symm <| Nat.mod_eq_of_lt h.lt
#align tactic.norm_fin.normalize_fin_lt.of Tactic.NormFin.NormalizeFinLt.of

theorem NormalizeFin.zero (n) : NormalizeFin (n + 1) 0 0 := by
  rw [normalize_fin]
  norm_num
#align tactic.norm_fin.normalize_fin.zero Tactic.NormFin.NormalizeFin.zero

theorem NormalizeFinLt.zero (n) : NormalizeFinLt (n + 1) 0 0 :=
  refl _
#align tactic.norm_fin.normalize_fin_lt.zero Tactic.NormFin.NormalizeFinLt.zero

theorem NormalizeFin.one (n) : NormalizeFin (n + 1) 1 1 :=
  refl _
#align tactic.norm_fin.normalize_fin.one Tactic.NormFin.NormalizeFin.one

theorem NormalizeFin.add {n} {a b : Fin n} {a' b' c' : ℕ} (ha : NormalizeFin n a a')
    (hb : NormalizeFin n b b') (h : a' + b' = c') : NormalizeFin n (a + b) c' := by
  simp only [normalize_fin, ← h] at * <;> rw [Nat.add_mod, ← ha, ← hb, Fin.add_def]
#align tactic.norm_fin.normalize_fin.add Tactic.NormFin.NormalizeFin.add

theorem NormalizeFin.mul {n} {a b : Fin n} {a' b' c' : ℕ} (ha : NormalizeFin n a a')
    (hb : NormalizeFin n b b') (h : a' * b' = c') : NormalizeFin n (a * b) c' := by
  simp only [normalize_fin, ← h] at * <;> rw [Nat.mul_mod, ← ha, ← hb, Fin.mul_def]
#align tactic.norm_fin.normalize_fin.mul Tactic.NormFin.NormalizeFin.mul

theorem NormalizeFin.bit0 {n} {a : Fin n} {a' : ℕ} (h : NormalizeFin n a a') :
    NormalizeFin n (bit0 a) (bit0 a') :=
  h.add h rfl
#align tactic.norm_fin.normalize_fin.bit0 Tactic.NormFin.NormalizeFin.bit0

theorem NormalizeFin.bit1 {n} {a : Fin (n + 1)} {a' : ℕ} (h : NormalizeFin (n + 1) a a') :
    NormalizeFin (n + 1) (bit1 a) (bit1 a') :=
  h.bit0.add (NormalizeFin.one _) rfl
#align tactic.norm_fin.normalize_fin.bit1 Tactic.NormFin.NormalizeFin.bit1

theorem NormalizeFinLt.succ {n} {a : Fin n} {a' b : ℕ} (h : NormalizeFinLt n a a')
    (e : a' + 1 = b) : NormalizeFinLt n.succ (Fin.succ a) b := by
  simpa [normalize_fin_lt, ← e] using h
#align tactic.norm_fin.normalize_fin_lt.succ Tactic.NormFin.NormalizeFinLt.succ

theorem NormalizeFinLt.cast_lt {n m} {a : Fin m} {ha} {a' : ℕ} (h : NormalizeFinLt m a a') :
    NormalizeFinLt n (Fin.castLt a ha) a' := by simpa [normalize_fin_lt] using h
#align tactic.norm_fin.normalize_fin_lt.cast_lt Tactic.NormFin.NormalizeFinLt.cast_lt

theorem NormalizeFinLt.cast_le {n m} {nm} {a : Fin m} {a' : ℕ} (h : NormalizeFinLt m a a') :
    NormalizeFinLt n (Fin.castLe nm a) a' := by simpa [normalize_fin_lt] using h
#align tactic.norm_fin.normalize_fin_lt.cast_le Tactic.NormFin.NormalizeFinLt.cast_le

theorem NormalizeFinLt.cast {n m} {nm} {a : Fin m} {a' : ℕ} (h : NormalizeFinLt m a a') :
    NormalizeFinLt n (Fin.cast nm a) a' := by simpa [normalize_fin_lt] using h
#align tactic.norm_fin.normalize_fin_lt.cast Tactic.NormFin.NormalizeFinLt.cast

theorem NormalizeFin.cast {n m} {nm} {a : Fin m} {a' : ℕ} (h : NormalizeFin m a a') :
    NormalizeFin n (Fin.cast nm a) a' := by convert ← normalize_fin_lt.cast h
#align tactic.norm_fin.normalize_fin.cast Tactic.NormFin.NormalizeFin.cast

theorem NormalizeFinLt.cast_add {n m} {a : Fin n} {a' : ℕ} (h : NormalizeFinLt n a a') :
    NormalizeFinLt (n + m) (Fin.castAdd m a) a' := by simpa [normalize_fin_lt] using h
#align tactic.norm_fin.normalize_fin_lt.cast_add Tactic.NormFin.NormalizeFinLt.cast_add

theorem NormalizeFinLt.cast_succ {n} {a : Fin n} {a' : ℕ} (h : NormalizeFinLt n a a') :
    NormalizeFinLt (n + 1) (Fin.castSucc a) a' :=
  NormalizeFinLt.cast_add h
#align tactic.norm_fin.normalize_fin_lt.cast_succ Tactic.NormFin.NormalizeFinLt.cast_succ

theorem NormalizeFinLt.add_nat {n m m'} (hm : m = m') {a : Fin n} {a' b : ℕ}
    (h : NormalizeFinLt n a a') (e : a' + m' = b) : NormalizeFinLt (n + m) (@Fin.addNat n m a) b :=
  by simpa [normalize_fin_lt, ← e, ← hm] using h
#align tactic.norm_fin.normalize_fin_lt.add_nat Tactic.NormFin.NormalizeFinLt.add_nat

theorem NormalizeFinLt.nat_add {n m n'} (hn : n = n') {a : Fin m} {a' b : ℕ}
    (h : NormalizeFinLt m a a') (e : n' + a' = b) : NormalizeFinLt (n + m) (@Fin.natAdd n m a) b :=
  by simpa [normalize_fin_lt, ← e, ← hn] using h
#align tactic.norm_fin.normalize_fin_lt.nat_add Tactic.NormFin.NormalizeFinLt.nat_add

theorem NormalizeFin.reduce {n} {a : Fin n} {n' a' b k nk : ℕ} (hn : n = n')
    (h : NormalizeFin n a a') (e1 : n' * k = nk) (e2 : nk + b = a') : NormalizeFin n a b := by
  rwa [← e2, ← e1, ← hn, normalize_fin, add_comm, Nat.add_mul_mod_self_left] at h
#align tactic.norm_fin.normalize_fin.reduce Tactic.NormFin.NormalizeFin.reduce

theorem NormalizeFinLt.reduce {n} {a : Fin n} {n' a' b k nk : ℕ} (hn : n = n')
    (h : NormalizeFin n a a') (e1 : n' * k = nk) (e2 : nk + b = a') (hl : b < n') :
    NormalizeFinLt n a b :=
  NormalizeFinLt.mk hn (h.reduce hn e1 e2) hl
#align tactic.norm_fin.normalize_fin_lt.reduce Tactic.NormFin.NormalizeFinLt.reduce

theorem NormalizeFin.eq {n} {a b : Fin n} {c : ℕ} (ha : NormalizeFin n a c)
    (hb : NormalizeFin n b c) : a = b :=
  Fin.eq_of_veq <| ha.trans hb.symm
#align tactic.norm_fin.normalize_fin.eq Tactic.NormFin.NormalizeFin.eq

theorem NormalizeFin.lt {n} {a b : Fin n} {a' b' : ℕ} (ha : NormalizeFin n a a')
    (hb : NormalizeFinLt n b b') (h : a' < b') : a < b := by
  have ha' := normalize_fin_lt.mk rfl ha (h.trans hb.lt) <;> rwa [← hb.coe, ← ha'.coe] at h
#align tactic.norm_fin.normalize_fin.lt Tactic.NormFin.NormalizeFin.lt

theorem NormalizeFin.le {n} {a b : Fin n} {a' b' : ℕ} (ha : NormalizeFin n a a')
    (hb : NormalizeFinLt n b b') (h : a' ≤ b') : a ≤ b := by
  have ha' := normalize_fin_lt.mk rfl ha (h.trans_lt hb.lt) <;> rwa [← hb.coe, ← ha'.coe] at h
#align tactic.norm_fin.normalize_fin.le Tactic.NormFin.NormalizeFin.le

/-- The monad for the `norm_fin` internal tactics. The state consists of an instance cache for `ℕ`,
and a tuple `(nn, n', p)` where `p` is a proof of `n = n'` and `nn` is `n` evaluated to a natural
number. (`n` itself is implicit.)  It is in an `option` because it is lazily initialized - for many
`n` we will never need this information, and indeed eagerly computing it would make some reductions
fail spuriously if `n` is not a numeral. -/
unsafe def eval_fin_m (α : Type) : Type :=
  StateT (instance_cache × Option (ℕ × expr × expr)) tactic α deriving Monad, Alternative
#align tactic.norm_fin.eval_fin_m tactic.norm_fin.eval_fin_m

/-- Lifts a tactic into the `eval_fin_m` monad. -/
@[inline]
unsafe def eval_fin_m.lift {α} (m : tactic α) : eval_fin_m α :=
  ⟨fun ⟨ic, r⟩ => do
    let a ← m
    pure (a, ic, r)⟩
#align tactic.norm_fin.eval_fin_m.lift tactic.norm_fin.eval_fin_m.lift

unsafe instance {α} : Coe (tactic α) (eval_fin_m α) :=
  ⟨eval_fin_m.lift⟩

/-- Lifts an `instance_cache` tactic into the `eval_fin_m` monad. -/
@[inline]
unsafe def eval_fin_m.lift_ic {α} (m : instance_cache → tactic (instance_cache × α)) :
    eval_fin_m α :=
  ⟨fun ⟨ic, r⟩ => do
    let (ic, a) ← m ic
    pure (a, ic, r)⟩
#align tactic.norm_fin.eval_fin_m.lift_ic tactic.norm_fin.eval_fin_m.lift_ic

/-- Evaluates a monadic action with a fresh `n` cache, and restore the old cache on completion of
the action. This is used when evaluating a tactic in the context of a different `n` than the parent
context. For example if we are evaluating `fin.succ a`, then `a : fin n` and
`fin.succ a : fin (n+1)`, so the parent cache will be about `n+1` and we need a separate cache for
`n`. -/
@[inline]
unsafe def eval_fin_m.reset {α} (m : eval_fin_m α) : eval_fin_m α :=
  ⟨fun ⟨ic, r⟩ => do
    let (a, ic, _) ← m.run ⟨ic, none⟩
    pure (a, ic, r)⟩
#align tactic.norm_fin.eval_fin_m.reset tactic.norm_fin.eval_fin_m.reset

/-- Given `n`, returns a tuple `(nn, n', p)` where `p` is a proof of `n = n'` and `nn` is `n`
evaluated to a natural number. The result of the evaluation is cached for future references.
Future calls to this function must use the same value of `n`, unless it is in a sub-context
created by `eval_fin_m.reset`. -/
unsafe def eval_fin_m.eval_n (n : expr) : eval_fin_m (ℕ × expr × expr) :=
  ⟨fun ⟨ic, r⟩ =>
    match r with
    | none => do
      let (n', p) ← or_refl_conv norm_num.derive n
      let nn ← n'.toNat
      let np := (nn, n', p)
      pure (np, ic, some np)
    | some np => pure (np, ic, some np)⟩
#align tactic.norm_fin.eval_fin_m.eval_n tactic.norm_fin.eval_fin_m.eval_n

/-- Run an `eval_fin_m` action with a new cache and discard the cache after evaluation. -/
@[inline]
unsafe def eval_fin_m.run {α} (m : eval_fin_m α) : tactic α := do
  let ic ← mk_instance_cache q(ℕ)
  let (a, _) ← StateT.run m (ic, none)
  pure a
#align tactic.norm_fin.eval_fin_m.run tactic.norm_fin.eval_fin_m.run

/-- The expression constructors recognized by the `eval_fin` evaluator. This is used instead of a
direct expr pattern match because expr pattern matches generate very large terms under the
hood so going via an intermediate inductive type like this is more efficient. -/
unsafe inductive match_fin_result
  | zero (n : expr)-- `(0 : fin (n+1))`

  | one (n : expr)-- `(1 : fin (n+1))`

  | add (n a b : expr)-- `(a + b : fin n)`

  | mul (n a b : expr)-- `(a * b : fin n)`

  | bit0 (n a : expr)-- `(bit0 a : fin n)`

  | bit1 (n a : expr)-- `(bit1 a : fin (n+1))`

  | succ (n a : expr)-- `(fin.succ a : fin n.succ)`

  | cast_lt (n m i h : expr)-- `(fin.cast_lt (i : fin m) (h : i.val < n) : fin n)`

  | cast_le (n m h a : expr)-- `(fin.cast_le (h : n ≤ m) (a : fin n) : fin m)`

  | cast (n m h a : expr)-- `(fin.cast_le (h : n = m) (a : fin n) : fin m)`

  | cast_add (n m a : expr)-- `(fin.cast_add m (a : fin n) : fin (n + m))`

  | cast_succ (n a : expr)-- `(fin.cast_succ (a : fin n) : fin (n + 1))`

  | add_nat (n m a : expr)-- `(fin.add_nat m (a : fin n) : fin (n + m))`

  | nat_add (n m a : expr)
#align tactic.norm_fin.match_fin_result tactic.norm_fin.match_fin_result

-- `(fin.nat_add n (a : fin m) : fin (n + m))`
section

open MatchFinResult

/-- Match a fin expression of the form `(coe_fn f a)` where `f` is some fin function. Several fin
functions are written this way: for example `cast_le : n ≤ m → fin n ↪o fin m` is not actually a
function but rather an order embedding with a coercion to a function. -/
unsafe def match_fin_coe_fn (a : expr) : expr → Option match_fin_result
  | q(@Fin.castLe $(n) $(m) $(h)) => some (cast_le n m h a)
  | q(@Fin.cast $(m) $(n) $(h)) => some (cast n m h a)
  | q(@Fin.castAdd $(n) $(m)) => some (cast_add n m a)
  | q(@Fin.castSucc $(n)) => some (cast_succ n a)
  | q(@Fin.addNat $(n) $(m)) => some (add_nat n m a)
  | q(@Fin.natAdd $(n) $(m)) => some (nat_add n m a)
  | _ => none
#align tactic.norm_fin.match_fin_coe_fn tactic.norm_fin.match_fin_coe_fn

/-- Match a fin expression to a `match_fin_result`, for easier pattern matching in the
evaluator. -/
unsafe def match_fin : expr → Option match_fin_result
  | q(@Zero.zero _ (@Fin.hasZero $(n))) => some (zero n)
  | q(@One.one _ (@Fin.hasOne $(n))) => some (one n)
  | q(@Add.add (Fin $(n)) _ $(a) $(b)) => some (add n a b)
  | q(@Mul.mul (Fin $(n)) _ $(a) $(b)) => some (mul n a b)
  | q(@bit0 (Fin $(n)) _ $(a)) => some (bit0 n a)
  | q(@bit1 _ (@Fin.hasOne $(n)) _ $(a)) => some (bit1 n a)
  | q(@Fin.succ $(n) $(a)) => some (succ n a)
  | q(@Fin.castLt $(n) $(m) $(a) $(h)) => some (cast_lt n m a h)
  | expr.app q(@coeFn _ _ _ $(f)) a => match_fin_coe_fn a f
  | _ => none
#align tactic.norm_fin.match_fin tactic.norm_fin.match_fin

end

/-- `reduce_fin lt n a (a', pa)` expects that `pa : normalize_fin n a a'` where `a'`
is a natural numeral, and produces `(b, pb)` where `pb : normalize_fin n a b` if `lt` is false, or
`pb : normalize_fin_lt n a b` if `lt` is true. In either case, `b` will be chosen to be less than
`n`, but if `lt` is true then we also prove it. This requires that `n` can be evaluated to a
numeral. -/
unsafe def reduce_fin' : Bool → expr → expr → expr × expr → eval_fin_m (expr × expr)
  | lt, n, a, (a', pa) => do
    let (nn, n', pn) ← eval_fin_m.eval_n n
    let na ← expr.to_nat a'
    if na < nn then
        if lt then do
          let p ← eval_fin_m.lift_ic fun ic => prove_lt_nat ic a' n'
          pure (a', q(@NormalizeFinLt.mk).mk_app [n, a, a', n', pn, pa, p])
        else pure (a', pa)
      else
        let nb := na % nn
        let nk := (na - nb) / nn
        eval_fin_m.lift_ic fun ic => do
          let (ic, k) ← ic nk
          let (ic, b) ← ic nb
          let (ic, nk, pe1) ← prove_mul_nat ic n' k
          let (ic, pe2) ← prove_add_nat ic nk b a'
          if lt then do
              let (ic, p) ← prove_lt_nat ic b n'
              pure
                  (ic, b,
                    q(@NormalizeFinLt.reduce).mk_app [n, a, n', a', b, k, nk, pn, pa, pe1, pe2, p])
            else
              pure
                (ic, b, q(@NormalizeFin.reduce).mk_app [n, a, n', a', b, k, nk, pn, pa, pe1, pe2])
#align tactic.norm_fin.reduce_fin' tactic.norm_fin.reduce_fin'

/-- `eval_fin_lt' eval_fin n a` expects that `a : fin n`, and produces `(b, p)` where
`p : normalize_fin_lt n a b`. (It is mutually recursive with `eval_fin` which is why it takes the
function as an argument.) -/
unsafe def eval_fin_lt' (eval_fin : expr → eval_fin_m (expr × expr)) :
    expr → expr → eval_fin_m (expr × expr)
  | n, a => do
    let e ← match_fin a
    match e with
      | match_fin_result.succ n a => do
        let (a', pa) ← (eval_fin_lt' n a).reset
        let (b, pb) ← eval_fin_m.lift_ic fun ic => prove_succ' ic a'
        pure (b, q(@NormalizeFinLt.succ).mk_app [n, a, a', b, pa, pb])
      | match_fin_result.cast_lt _ m a h => do
        let (a', pa) ← (eval_fin_lt' m a).reset
        pure (a', q(@NormalizeFinLt.cast_lt).mk_app [n, m, a, h, a', pa])
      | match_fin_result.cast_le _ m nm a => do
        let (a', pa) ← (eval_fin_lt' m a).reset
        pure (a', q(@NormalizeFinLt.cast_le).mk_app [n, m, nm, a, a', pa])
      | match_fin_result.cast m _ nm a => do
        let (a', pa) ← (eval_fin_lt' m a).reset
        pure (a', q(@NormalizeFinLt.cast).mk_app [n, m, nm, a, a', pa])
      | match_fin_result.cast_add n m a => do
        let (a', pa) ← (eval_fin_lt' m a).reset
        pure (a', q(@NormalizeFinLt.cast_add).mk_app [n, m, a, a', pa])
      | match_fin_result.cast_succ n a => do
        let (a', pa) ← (eval_fin_lt' n a).reset
        pure (a', q(@NormalizeFinLt.cast_succ).mk_app [n, a, a', pa])
      | match_fin_result.add_nat n m a => do
        let (a', pa) ← (eval_fin_lt' n a).reset
        let (m', pm) ← or_refl_conv norm_num.derive m
        let (b, pb) ← eval_fin_m.lift_ic fun ic => prove_add_nat' ic a' m'
        pure (b, q(@NormalizeFinLt.add_nat).mk_app [n, m, m', pm, a, a', b, pa, pb])
      | match_fin_result.nat_add n m a => do
        let (a', pa) ← (eval_fin_lt' m a).reset
        let (n', pn) ← or_refl_conv norm_num.derive n
        let (b, pb) ← eval_fin_m.lift_ic fun ic => prove_add_nat' ic n' a'
        pure (b, q(@NormalizeFinLt.nat_add).mk_app [n, m, n', pn, a, a', b, pa, pb])
      | _ => do
        let (_, n', pn) ← eval_fin_m.eval_n n
        let (a', pa) ← eval_fin a >>= reduce_fin' tt n a
        let p ← eval_fin_m.lift_ic fun ic => prove_lt_nat ic a' n'
        pure (a', q(@NormalizeFinLt.mk).mk_app [n, a, a', n', pn, pa, p])
#align tactic.norm_fin.eval_fin_lt' tactic.norm_fin.eval_fin_lt'

/-- Get `n` such that `a : fin n`. -/
unsafe def get_fin_type (a : expr) : tactic expr := do
  let q(Fin $(n)) ← infer_type a
  pure n
#align tactic.norm_fin.get_fin_type tactic.norm_fin.get_fin_type

/-- Given `a : fin n`, `eval_fin a` returns `(b, p)` where `p : normalize_fin n a b`. This function
does no reduction of the numeral `b`; for example `eval_fin (5 + 5 : fin 6)` returns `10`. It works
even if `n` is a variable, for example `eval_fin (5 + 5 : fin (n+1))` also returns `10`. -/
unsafe def eval_fin : expr → eval_fin_m (expr × expr)
  | a => do
    let m ← match_fin a
    match m with
      | match_fin_result.zero n => pure (q((0 : ℕ)), q(NormalizeFin.zero).mk_app [n])
      | match_fin_result.one n => pure (q((1 : ℕ)), q(NormalizeFin.one).mk_app [n])
      | match_fin_result.add n a b => do
        let (a', pa) ← eval_fin a
        let (b', pb) ← eval_fin b
        let (c, pc) ← eval_fin_m.lift_ic fun ic => prove_add_nat' ic a' b'
        pure (c, q(@NormalizeFin.add).mk_app [n, a, b, a', b', c, pa, pb, pc])
      | match_fin_result.mul n a b => do
        let (a', pa) ← eval_fin a
        let (b', pb) ← eval_fin b
        let (c, pc) ← eval_fin_m.lift_ic fun ic => prove_mul_nat ic a' b'
        pure (c, q(@NormalizeFin.mul).mk_app [n, a, b, a', b', c, pa, pb, pc])
      | match_fin_result.bit0 n a => do
        let (a', pa) ← eval_fin a
        pure (q(@bit0 ℕ _).mk_app [a'], q(@NormalizeFin.bit0).mk_app [n, a, a', pa])
      | match_fin_result.bit1 n a => do
        let (a', pa) ← eval_fin a
        pure (q(@bit1 ℕ _ _).mk_app [a'], q(@NormalizeFin.bit1).mk_app [n, a, a', pa])
      | match_fin_result.cast m n nm a => do
        let (a', pa) ← (eval_fin a).reset
        pure (a', q(@NormalizeFin.cast).mk_app [n, m, nm, a, a', pa])
      | _ => do
        let n ← get_fin_type a
        let (a', pa) ← eval_fin_lt' eval_fin n a
        pure (a', q(@NormalizeFinLt.of).mk_app [n, a, a', pa])
#align tactic.norm_fin.eval_fin tactic.norm_fin.eval_fin

/-- `eval_fin_lt n a` expects that `a : fin n`, and produces `(b, p)` where
`p : normalize_fin_lt n a b`. -/
unsafe def eval_fin_lt : expr → expr → eval_fin_m (expr × expr) :=
  eval_fin_lt' eval_fin
#align tactic.norm_fin.eval_fin_lt tactic.norm_fin.eval_fin_lt

/-- Given `a : fin n`, `eval_fin ff n a` returns `(b, p)` where `p : normalize_fin n a b`, and
`eval_fin tt n a` returns `p : normalize_fin_lt n a b`. Unlike `eval_fin`, this also does reduction
of the numeral `b`; for example `reduce_fin ff 6 (5 + 5 : fin 6)` returns `4`. As a result, it
fails if `n` is a variable, for example `reduce_fin ff (n+1) (5 + 5 : fin (n+1))` fails. -/
unsafe def reduce_fin (lt : Bool) (n a : expr) : eval_fin_m (expr × expr) :=
  eval_fin a >>= reduce_fin' lt n a
#align tactic.norm_fin.reduce_fin tactic.norm_fin.reduce_fin

/-- If `a b : fin n` and `a'` and `b'` are as returned by `eval_fin`,
then `prove_lt_fin' n a b a' b'` proves `a < b`. -/
unsafe def prove_lt_fin' : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr
  | n, a, b, a', b' => do
    let (a', pa) ← reduce_fin' false n a a'
    let (b', pb) ← reduce_fin' true n b b'
    let p ← eval_fin_m.lift_ic fun ic => prove_lt_nat ic a' b'
    pure (q(@NormalizeFin.lt).mk_app [n, a, b, a', b', pa, pb, p])
#align tactic.norm_fin.prove_lt_fin' tactic.norm_fin.prove_lt_fin'

/-- If `a b : fin n` and `a'` and `b'` are as returned by `eval_fin`,
then `prove_le_fin' n a b a' b'` proves `a ≤ b`. -/
unsafe def prove_le_fin' : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr
  | n, a, b, a', b' => do
    let (a', pa) ← reduce_fin' false n a a'
    let (b', pb) ← reduce_fin' true n b b'
    let p ← eval_fin_m.lift_ic fun ic => prove_le_nat ic a' b'
    pure (q(@NormalizeFin.le).mk_app [n, a, b, a', b', pa, pb, p])
#align tactic.norm_fin.prove_le_fin' tactic.norm_fin.prove_le_fin'

/-- If `a b : fin n` and `a'` and `b'` are as returned by `eval_fin`,
then `prove_eq_fin' n a b a' b'` proves `a = b`. -/
unsafe def prove_eq_fin' : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr
  | n, a, b, (a', pa), (b', pb) =>
    if a' == b' then do
      pure (q(@NormalizeFin.eq).mk_app [n, a, b, a', pa, pb])
    else do
      let (a', pa) ← reduce_fin' false n a (a', pa)
      let (b', pb) ← reduce_fin' false n b (b', pb)
      guard (a' == b')
      pure (q(@NormalizeFin.eq).mk_app [n, a, b, a', pa, pb])
#align tactic.norm_fin.prove_eq_fin' tactic.norm_fin.prove_eq_fin'

/-- Given a function with the type of `prove_eq_fin'`, evaluates it with the given `a` and `b`. -/
unsafe def eval_prove_fin (f : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr)
    (a b : expr) : tactic expr := do
  let n ← get_fin_type a
  eval_fin_m.run <| eval_fin a >>= fun a' => eval_fin b >>= f n a b a'
#align tactic.norm_fin.eval_prove_fin tactic.norm_fin.eval_prove_fin

/-- If `a b : fin n`, then `prove_eq_fin a b` proves `a = b`. -/
unsafe def prove_eq_fin : expr → expr → tactic expr :=
  eval_prove_fin prove_eq_fin'
#align tactic.norm_fin.prove_eq_fin tactic.norm_fin.prove_eq_fin

/-- If `a b : fin n`, then `prove_lt_fin a b` proves `a < b`. -/
unsafe def prove_lt_fin : expr → expr → tactic expr :=
  eval_prove_fin prove_lt_fin'
#align tactic.norm_fin.prove_lt_fin tactic.norm_fin.prove_lt_fin

/-- If `a b : fin n`, then `prove_le_fin a b` proves `a ≤ b`. -/
unsafe def prove_le_fin : expr → expr → tactic expr :=
  eval_prove_fin prove_le_fin'
#align tactic.norm_fin.prove_le_fin tactic.norm_fin.prove_le_fin

section

open NormNum.MatchNumeralResult

/-- Given expressions `n` and `m` such that `n` is definitionally equal to `m.succ`, and
a natural numeral `a`, proves `(b, ⊢ normalize_fin n b a)`, where `n` and `m` are both used
in the construction of the numeral `b : fin n`. -/
unsafe def mk_fin_numeral (n m : expr) : expr → Option (expr × expr)
  | a =>
    match match_numeral a with
    | zero =>
      some (expr.app q(@Zero.zero (Fin $(n))) q(@Fin.hasZero $(m)), expr.app q(NormalizeFin.zero) m)
    | one =>
      some (expr.app q(@One.one (Fin $(n))) q(@Fin.hasOne $(m)), expr.app q(NormalizeFin.one) m)
    | bit0 a => do
      let (a', p) ← mk_fin_numeral a
      some (q((bit0 $(a') : Fin $(n))), q(@NormalizeFin.bit0).mk_app [n, a', a, p])
    | bit1 a => do
      let (a', p) ← mk_fin_numeral a
      some
          (q(@bit1 (Fin $(n))).mk_app [q(@Fin.hasOne $(m)), q(@Fin.hasAdd $(n)), a'],
            q(@NormalizeFin.bit1).mk_app [m, a', a, p])
    | _ => none
#align tactic.norm_fin.mk_fin_numeral tactic.norm_fin.mk_fin_numeral

end

/-- The common prep work for the cases in `eval_ineq`. Given inputs `a b : fin n`, it calls
`f n a' b' na nb` where `a'` and `b'` are the result of `eval_fin` and `na` and `nb` are
`a' % n` and `b' % n` as natural numbers. -/
unsafe def eval_rel {α} (a b : expr) (f : expr → expr × expr → expr × expr → ℕ → ℕ → eval_fin_m α) :
    tactic α := do
  let n ← get_fin_type a
  eval_fin_m.run do
      let (nn, n', pn) ← eval_fin_m.eval_n n
      let (a', pa) ← eval_fin a
      let (b', pb) ← eval_fin b
      let na ← eval_fin_m.lift a'
      let nb ← eval_fin_m.lift b'
      f n (a', pa) (b', pb) (na % nn) (nb % nn)
#align tactic.norm_fin.eval_rel tactic.norm_fin.eval_rel

/-- Given `a b : fin n`, proves either `(n, tt, p)` where `p : a < b` or
`(n, ff, p)` where `p : b ≤ a`. -/
unsafe def prove_lt_ge_fin : expr → expr → tactic (expr × Bool × expr)
  | a, b =>
    (eval_rel a b) fun n a' b' na nb =>
      if na < nb then Prod.mk n <$> Prod.mk true <$> prove_lt_fin' n a b a' b'
      else Prod.mk n <$> Prod.mk false <$> prove_le_fin' n b a b' a'
#align tactic.norm_fin.prove_lt_ge_fin tactic.norm_fin.prove_lt_ge_fin

/-- Given `a b : fin n`, proves either `(n, tt, p)` where `p : a = b` or
`(n, ff, p)` where `p : a ≠ b`. -/
unsafe def prove_eq_ne_fin : expr → expr → tactic (expr × Bool × expr)
  | a, b =>
    (eval_rel a b) fun n a' b' na nb =>
      if na = nb then Prod.mk n <$> Prod.mk true <$> prove_eq_fin' n a b a' b'
      else
        if na < nb then do
          let p ← prove_lt_fin' n a b a' b'
          pure (n, ff, q(@ne_of_lt (Fin $(n)) _).mk_app [a, b, p])
        else do
          let p ← prove_lt_fin' n b a b' a'
          pure (n, ff, q(@ne_of_gt (Fin $(n)) _).mk_app [a, b, p])
#align tactic.norm_fin.prove_eq_ne_fin tactic.norm_fin.prove_eq_ne_fin

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      A `norm_num` extension that evaluates equalities and inequalities on the type `fin n`.
      
      ```
      example : (5 : fin 7) = fin.succ (fin.succ 3) := by norm_num
      ```
      -/
    @[ norm_num ]
    unsafe
  def
    eval_ineq
    : expr → tactic ( expr × expr )
    |
        q( $ ( a ) < $ ( b ) )
        =>
        do
          let ( n , lt , p ) ← prove_lt_ge_fin a b
            if
              lt
              then
              true_intro p
              else
              false_intro ( q( @ not_lt_of_ge ( Fin $ ( n ) ) _ ) . mk_app [ a , b , p ] )
      |
        q( $ ( a ) ≤ $ ( b ) )
        =>
        do
          let ( n , lt , p ) ← prove_lt_ge_fin b a
            if
              lt
              then
              false_intro ( q( @ not_le_of_gt ( Fin $ ( n ) ) _ ) . mk_app [ a , b , p ] )
              else
              true_intro p
      |
        q( $ ( a ) = $ ( b ) )
        =>
        do let ( n , Eq , p ) ← prove_eq_ne_fin a b if Eq then true_intro p else false_intro p
      | q( $ ( a ) > $ ( b ) ) => mk_app ` ` LT.lt [ b , a ] >>= eval_ineq
      | q( $ ( a ) ≥ $ ( b ) ) => mk_app ` ` LE.le [ b , a ] >>= eval_ineq
      |
        q( $ ( a ) ≠ $ ( b ) )
        =>
        do
          let ( n , Eq , p ) ← prove_eq_ne_fin a b
            if
              Eq
              then
              false_intro q( not_not_intro ( $ ( p ) : ( $ ( a ) : Fin $ ( n ) ) = $ ( b ) ) )
              else
              true_intro p
      | _ => failed
#align tactic.norm_fin.eval_ineq tactic.norm_fin.eval_ineq

/-- Evaluates `e : fin n` to a natural number less than `n`. Returns `none` if it is not a natural
number or greater than `n`. -/
unsafe def as_numeral (n e : expr) : eval_fin_m (Option ℕ) :=
  match e.toNat with
  | none => pure none
  | some Ne => do
    let (nn, _) ← eval_fin_m.eval_n n
    pure <| if Ne < nn then some Ne else none
#align tactic.norm_fin.as_numeral tactic.norm_fin.as_numeral

/-- Given `a : fin n`, returns `(b, ⊢ a = b)` where `b` is a normalized fin numeral. Fails if `a`
is already normalized. -/
unsafe def eval_fin_num (a : expr) : tactic (expr × expr) := do
  let n ← get_fin_type a
  eval_fin_m.run do
      as_numeral n a >>= fun o => guardb o
      let (a', pa) ← eval_fin a
      let (a', pa) ← reduce_fin' ff n a (a', pa) <|> pure (a', pa)
      let (nm + 1, _) ← eval_fin_m.eval_n n |
        failure
      let m' ← eval_fin_m.lift_ic fun ic => ic nm
      let n' ← eval_fin_m.lift_ic fun ic => ic (nm + 1)
      let (b, pb) ← mk_fin_numeral n' m' a'
      pure (b, q(@NormalizeFin.eq).mk_app [n, a, b, a', pa, pb])
#align tactic.norm_fin.eval_fin_num tactic.norm_fin.eval_fin_num

end NormFin

namespace Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/-- Rewrites occurrences of fin expressions to normal form anywhere in the goal.
The `norm_num` extension will only rewrite fin expressions if they appear in equalities and
inequalities. For example if the goal is `P (2 + 2 : fin 3)` then `norm_num` will not do anything
but `norm_fin` will reduce the goal to `P 1`.

(The reason this is not part of `norm_num` is because evaluation of fin numerals uses a top down
evaluation strategy while `norm_num` works bottom up; also determining whether a normalization
will work is expensive, meaning that unrelated uses of `norm_num` would be slowed down with this
as a plugin.) -/
unsafe def norm_fin (hs : parse simp_arg_list) : tactic Unit :=
  try (simp_top_down tactic.norm_fin.eval_fin_num) >> try (norm_num hs (Loc.ns [none]))
#align tactic.interactive.norm_fin tactic.interactive.norm_fin

/-- Rewrites occurrences of fin expressions to normal form anywhere in the goal.
The `norm_num` extension will only rewrite fin expressions if they appear in equalities and
inequalities. For example if the goal is `P (2 + 2 : fin 3)` then `norm_num` will not do anything
but `norm_fin` will reduce the goal to `P 1`.

```lean
example : (5 : fin 7) = fin.succ (fin.succ 3) := by norm_num
example (P : fin 7 → Prop) (h : P 5) : P (fin.succ (fin.succ 3)) := by norm_fin; exact h
```
-/
add_tactic_doc
  { Name := "norm_fin"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.norm_fin]
    tags := ["arithmetic", "decision procedure"] }

end Interactive

end Tactic

