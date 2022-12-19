/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module tactic.omega.nat.preterm
! leanprover-community/mathlib commit bbeb185db4ccee8ed07dc48449414ebfa39cb821
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Omega.Term

/-
Linear natural number arithmetic terms in pre-normalized form.
-/
open Tactic

namespace Omega

namespace Nat

/-- The shadow syntax for arithmetic terms. All constants are reified to `cst`
(e.g., `5` is reified to `cst 5`) and all other atomic terms are reified to
`exp` (e.g., `5 * (list.length l)` is reified to `exp 5 \`(list.length l)`).
`exp` accepts a coefficient of type `nat` as its first argument because
multiplication by constant is allowed by the omega test. -/
unsafe inductive exprterm : Type
  | cst : Nat → exprterm
  | exp : Nat → expr → exprterm
  | add : exprterm → exprterm → exprterm
  | sub : exprterm → exprterm → exprterm
#align omega.nat.exprterm omega.nat.exprterm

/-- Similar to `exprterm`, except that all exprs are now replaced with
de Brujin indices of type `nat`. This is akin to generalizing over
the terms represented by the said exprs. -/
inductive Preterm : Type
  | cst : Nat → preterm
  | var : Nat → Nat → preterm
  | add : preterm → preterm → preterm
  | sub : preterm → preterm → preterm
  deriving has_reflect, DecidableEq, Inhabited
#align omega.nat.preterm Omega.Nat.Preterm

-- mathport name: preterm.cst
scoped notation "&" k => Omega.Nat.Preterm.cst k

-- mathport name: preterm.var
scoped infixl:300 " ** " => Omega.Nat.Preterm.var

-- mathport name: preterm.add
scoped notation t " +* " s => Omega.Nat.Preterm.add t s

-- mathport name: preterm.sub
scoped notation t " -* " s => Omega.Nat.Preterm.sub t s

namespace Preterm

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- Helper tactic for proof by induction over preterms -/
unsafe def induce (tac : tactic Unit := tactic.skip) : tactic Unit :=
  sorry
#align omega.nat.preterm.induce omega.nat.preterm.induce

/-- Preterm evaluation -/
def val (v : Nat → Nat) : Preterm → Nat
  | &i => i
  | i ** n => if i = 1 then v n else v n * i
  | t1 +* t2 => t1.val + t2.val
  | t1 -* t2 => t1.val - t2.val
#align omega.nat.preterm.val Omega.Nat.Preterm.val

@[simp]
theorem val_const {v : Nat → Nat} {m : Nat} : (&m).val v = m :=
  rfl
#align omega.nat.preterm.val_const Omega.Nat.Preterm.val_const

@[simp]
theorem val_var {v : Nat → Nat} {m n : Nat} : (m ** n).val v = m * v n := by
  simp only [val]; by_cases h1 : m = 1
  rw [if_pos h1, h1, one_mul]
  rw [if_neg h1, mul_comm]
#align omega.nat.preterm.val_var Omega.Nat.Preterm.val_var

@[simp]
theorem val_add {v : Nat → Nat} {t s : Preterm} : (t +* s).val v = t.val v + s.val v :=
  rfl
#align omega.nat.preterm.val_add Omega.Nat.Preterm.val_add

@[simp]
theorem val_sub {v : Nat → Nat} {t s : Preterm} : (t -* s).val v = t.val v - s.val v :=
  rfl
#align omega.nat.preterm.val_sub Omega.Nat.Preterm.val_sub

/-- Fresh de Brujin index not used by any variable in argument -/
def freshIndex : Preterm → Nat
  | &_ => 0
  | i ** n => n + 1
  | t1 +* t2 => max t1.freshIndex t2.freshIndex
  | t1 -* t2 => max t1.freshIndex t2.freshIndex
#align omega.nat.preterm.fresh_index Omega.Nat.Preterm.freshIndex

/-- If variable assignments `v` and `w` agree on all variables that occur
in term `t`, the value of `t` under `v` and `w` are identical. -/
theorem val_constant (v w : Nat → Nat) :
    ∀ t : Preterm, (∀ x < t.freshIndex, v x = w x) → t.val v = t.val w
  | &n, h1 => rfl
  | m ** n, h1 => by 
    simp only [val_var]
    apply congr_arg fun y => m * y
    apply h1 _ (lt_add_one _)
  | t +* s, h1 => by 
    simp only [val_add]
    have ht := val_constant t fun x hx => h1 _ (lt_of_lt_of_le hx (le_max_left _ _))
    have hs := val_constant s fun x hx => h1 _ (lt_of_lt_of_le hx (le_max_right _ _))
    rw [ht, hs]
  | t -* s, h1 => by 
    simp only [val_sub]
    have ht := val_constant t fun x hx => h1 _ (lt_of_lt_of_le hx (le_max_left _ _))
    have hs := val_constant s fun x hx => h1 _ (lt_of_lt_of_le hx (le_max_right _ _))
    rw [ht, hs]
#align omega.nat.preterm.val_constant Omega.Nat.Preterm.val_constant

def repr : Preterm → String
  | &i => i.repr
  | i ** n => i.repr ++ "*x" ++ n.repr
  | t1 +* t2 => "(" ++ t1.repr ++ " + " ++ t2.repr ++ ")"
  | t1 -* t2 => "(" ++ t1.repr ++ " - " ++ t2.repr ++ ")"
#align omega.nat.preterm.repr Omega.Nat.Preterm.repr

@[simp]
def addOne (t : Preterm) : Preterm :=
  t +* &1
#align omega.nat.preterm.add_one Omega.Nat.Preterm.addOne

/-- Preterm is free of subtractions -/
def SubFree : Preterm → Prop
  | &m => True
  | m ** n => True
  | t +* s => t.SubFree ∧ s.SubFree
  | _ -* _ => False
#align omega.nat.preterm.sub_free Omega.Nat.Preterm.SubFree

end Preterm

open List.Func

-- get notation for list.func.set
/-- Return a term (which is in canonical form by definition)
    that is equivalent to the input preterm -/
@[simp]
def canonize : Preterm → Term
  | &m => ⟨↑m, []⟩
  | m ** n => ⟨0, [] {n ↦ ↑m}⟩
  | t +* s => Term.add (canonize t) (canonize s)
  | _ -* _ => ⟨0, []⟩
#align omega.nat.canonize Omega.Nat.canonize

@[simp]
theorem val_canonize {v : Nat → Nat} :
    ∀ {t : Preterm}, t.SubFree → ((canonize t).val fun x => ↑(v x)) = t.val v
  | &i, h1 => by simp only [canonize, preterm.val_const, term.val, coeffs.val_nil, add_zero]
  | i ** n, h1 => by
    simp only [preterm.val_var, coeffs.val_set, term.val, zero_add, Int.ofNat_mul, canonize]
  | t +* s, h1 => by
    simp only [val_canonize h1.left, val_canonize h1.right, Int.ofNat_add, canonize, term.val_add,
      preterm.val_add]
#align omega.nat.val_canonize Omega.Nat.val_canonize

end Nat

end Omega

