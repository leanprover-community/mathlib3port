/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module tactic.omega.int.preterm
! leanprover-community/mathlib commit bbeb185db4ccee8ed07dc48449414ebfa39cb821
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Omega.Term

/-
Linear integer arithmetic terms in pre-normalized form.
-/
namespace Omega

namespace Int

/-- The shadow syntax for arithmetic terms. All constants are reified to `cst`
(e.g., `-5` is reified to `cst -5`) and all other atomic terms are reified to
`exp` (e.g., `-5 * (gcd 14 -7)` is reified to `exp -5 \`(gcd 14 -7)`).
`exp` accepts a coefficient of type `int` as its first argument because
multiplication by constant is allowed by the omega test. -/
unsafe inductive exprterm : Type
  | cst : Int → exprterm
  | exp : Int → expr → exprterm
  | add : exprterm → exprterm → exprterm
#align omega.int.exprterm omega.int.exprterm

/-- Similar to `exprterm`, except that all exprs are now replaced with
de Brujin indices of type `nat`. This is akin to generalizing over
the terms represented by the said exprs. -/
inductive Preterm : Type
  | cst : Int → preterm
  | var : Int → Nat → preterm
  | add : preterm → preterm → preterm
  deriving has_reflect, Inhabited
#align omega.int.preterm Omega.Int.Preterm

-- mathport name: preterm.cst
scoped notation "&" k => Omega.Int.Preterm.cst k

-- mathport name: preterm.var
scoped infixl:300 " ** " => Omega.Int.Preterm.var

-- mathport name: preterm.add
scoped notation t " +* " s => Omega.Int.Preterm.add t s

namespace Preterm

/-- Preterm evaluation -/
@[simp]
def val (v : Nat → Int) : Preterm → Int
  | &i => i
  | i ** n => if i = 1 then v n else if i = -1 then -v n else v n * i
  | t1 +* t2 => t1.val + t2.val
#align omega.int.preterm.val Omega.Int.Preterm.val

/-- Fresh de Brujin index not used by any variable in argument -/
def freshIndex : Preterm → Nat
  | &_ => 0
  | i ** n => n + 1
  | t1 +* t2 => max t1.freshIndex t2.freshIndex
#align omega.int.preterm.fresh_index Omega.Int.Preterm.freshIndex

@[simp]
def addOne (t : Preterm) : Preterm :=
  t +* &1
#align omega.int.preterm.add_one Omega.Int.Preterm.addOne

def repr : Preterm → String
  | &i => i.repr
  | i ** n => i.repr ++ "*x" ++ n.repr
  | t1 +* t2 => "(" ++ t1.repr ++ " + " ++ t2.repr ++ ")"
#align omega.int.preterm.repr Omega.Int.Preterm.repr

end Preterm

open List.Func

-- get notation for list.func.set
/-- Return a term (which is in canonical form by definition)
    that is equivalent to the input preterm -/
@[simp]
def canonize : Preterm → Term
  | &i => ⟨i, []⟩
  | i ** n => ⟨0, [] {n ↦ i}⟩
  | t1 +* t2 => Term.add (canonize t1) (canonize t2)
#align omega.int.canonize Omega.Int.canonize

@[simp]
theorem val_canonize {v : Nat → Int} : ∀ {t : Preterm}, (canonize t).val v = t.val v
  | &i => by simp only [preterm.val, add_zero, term.val, canonize, coeffs.val_nil]
  | i ** n => by 
    simp only [coeffs.val_set, canonize, preterm.val, zero_add, term.val]
    split_ifs with h1 h2
    · simp only [one_mul, h1]
    · simp only [neg_mul, one_mul, h2]
    · rw [mul_comm]
  | t +* s => by simp only [canonize, val_canonize, term.val_add, preterm.val]
#align omega.int.val_canonize Omega.Int.val_canonize

end Int

end Omega

