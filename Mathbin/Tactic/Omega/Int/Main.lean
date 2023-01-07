/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module tactic.omega.int.main
! leanprover-community/mathlib commit 134625f523e737f650a6ea7f0c82a6177e45e622
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Omega.ProveUnsats
import Mathbin.Tactic.Omega.Int.Dnf

/-
Main procedure for linear integer arithmetic.
-/
open Tactic

namespace Omega

namespace Int

open Omega.Int

run_cmd
  mk_simp_attr `sugar

attribute [sugar]
  Ne not_le not_lt Int.lt_iff_add_one_le or_false_iff false_or_iff and_true_iff true_and_iff GE.ge GT.gt mul_add add_mul one_mul mul_one mul_comm sub_eq_add_neg imp_iff_not_or iff_iff_not_or_and_or_not

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
unsafe def desugar :=
  sorry
#align omega.int.desugar omega.int.desugar

theorem univ_close_of_unsat_clausify (m : Nat) (p : Preform) :
    Clauses.Unsat (dnf (¬* p)) → UnivClose p (fun x => 0) m
  | h1 => by
    apply univ_close_of_valid
    apply valid_of_unsat_not
    apply unsat_of_clauses_unsat
    exact h1
#align omega.int.univ_close_of_unsat_clausify Omega.Int.univ_close_of_unsat_clausify

/-- Given a (p : preform), return the expr of a (t : univ_close m p) -/
unsafe def prove_univ_close (m : Nat) (p : Preform) : tactic expr := do
  let x ← prove_unsats (dnf (¬* p))
  return q(univ_close_of_unsat_clausify $(q(m)) $(q(p)) $(x))
#align omega.int.prove_univ_close omega.int.prove_univ_close

-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- Reification to imtermediate shadow syntax that retains exprs -/ unsafe
  def
    to_exprterm
    : expr → tactic exprterm
    |
        q( - $ ( x ) )
        =>
        ( do let z ← eval_expr' Int x return ( exprterm.cst ( - z : Int ) ) )
          <|>
          ( return <| exprterm.exp ( - 1 : Int ) x )
      | q( $ ( mx ) * $ ( zx ) ) => do let z ← eval_expr' Int zx return ( exprterm.exp z mx )
      |
        q( $ ( t1x ) + $ ( t2x ) )
        =>
        do let t1 ← to_exprterm t1x let t2 ← to_exprterm t2x return ( exprterm.add t1 t2 )
      |
        x
        =>
        ( do let z ← eval_expr' Int x return ( exprterm.cst z ) ) <|> ( return <| exprterm.exp 1 x )
#align omega.int.to_exprterm omega.int.to_exprterm

-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- Reification to imtermediate shadow syntax that retains exprs -/ unsafe
  def
    to_exprform
    : expr → tactic exprform
    |
        q( $ ( tx1 ) = $ ( tx2 ) )
        =>
        do let t1 ← to_exprterm tx1 let t2 ← to_exprterm tx2 return ( exprform.eq t1 t2 )
      |
        q( $ ( tx1 ) ≤ $ ( tx2 ) )
        =>
        do let t1 ← to_exprterm tx1 let t2 ← to_exprterm tx2 return ( exprform.le t1 t2 )
      | q( ¬ $ ( px ) ) => do let p ← to_exprform px return ( exprform.not p )
      |
        q( $ ( px ) ∨ $ ( qx ) )
        =>
        do let p ← to_exprform px let q ← to_exprform qx return ( exprform.or p q )
      |
        q( $ ( px ) ∧ $ ( qx ) )
        =>
        do let p ← to_exprform px let q ← to_exprform qx return ( exprform.and p q )
      | q( _ → $ ( px ) ) => to_exprform px
      | x => ( trace "Cannot reify expr : " >> trace x ) >> failed
#align omega.int.to_exprform omega.int.to_exprform

/-- List of all unreified exprs -/
unsafe def exprterm.exprs : exprterm → List expr
  | exprterm.cst _ => []
  | exprterm.exp _ x => [x]
  | exprterm.add t s => List.union t.exprs s.exprs
#align omega.int.exprterm.exprs omega.int.exprterm.exprs

/-- List of all unreified exprs -/
unsafe def exprform.exprs : exprform → List expr
  | exprform.eq t s => List.union t.exprs s.exprs
  | exprform.le t s => List.union t.exprs s.exprs
  | exprform.not p => p.exprs
  | exprform.or p q => List.union p.exprs q.exprs
  | exprform.and p q => List.union p.exprs q.exprs
#align omega.int.exprform.exprs omega.int.exprform.exprs

/-- Reification to an intermediate shadow syntax which eliminates exprs,
    but still includes non-canonical terms -/
unsafe def exprterm.to_preterm (xs : List expr) : exprterm → tactic Preterm
  | exprterm.cst k => return (&k)
  | exprterm.exp k x =>
    let m := xs.indexOf x
    if m < xs.length then return (k ** m) else failed
  | exprterm.add xa xb => do
    let a ← xa.to_preterm
    let b ← xb.to_preterm
    return (a +* b)
#align omega.int.exprterm.to_preterm omega.int.exprterm.to_preterm

/-- Reification to an intermediate shadow syntax which eliminates exprs,
    but still includes non-canonical terms -/
unsafe def exprform.to_preform (xs : List expr) : exprform → tactic Preform
  | exprform.eq xa xb => do
    let a ← xa.to_preterm xs
    let b ← xb.to_preterm xs
    return (a =* b)
  | exprform.le xa xb => do
    let a ← xa.to_preterm xs
    let b ← xb.to_preterm xs
    return (a ≤* b)
  | exprform.not xp => do
    let p ← xp.to_preform
    return (¬* p)
  | exprform.or xp xq => do
    let p ← xp.to_preform
    let q ← xq.to_preform
    return (p ∨* q)
  | exprform.and xp xq => do
    let p ← xp.to_preform
    let q ← xq.to_preform
    return (p ∧* q)
#align omega.int.exprform.to_preform omega.int.exprform.to_preform

/-- Reification to an intermediate shadow syntax which eliminates exprs,
    but still includes non-canonical terms. -/
unsafe def to_preform (x : expr) : tactic (preform × Nat) := do
  let xf ← to_exprform x
  let xs := xf.exprs
  let f ← xf.to_preform xs
  return (f, xs)
#align omega.int.to_preform omega.int.to_preform

/-- Return expr of proof of current LIA goal -/
unsafe def prove : tactic expr := do
  let (p, m) ← target >>= to_preform
  trace_if_enabled `omega p
  prove_univ_close m p
#align omega.int.prove omega.int.prove

/-- Succeed iff argument is the expr of ℤ -/
unsafe def eq_int (x : expr) : tactic Unit :=
  if x = q(Int) then skip else failed
#align omega.int.eq_int omega.int.eq_int

-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- Check whether argument is expr of a well-formed formula of LIA-/ unsafe
  def
    wff
    : expr → tactic Unit
    | q( ¬ $ ( px ) ) => wff px
      | q( $ ( px ) ∨ $ ( qx ) ) => wff px >> wff qx
      | q( $ ( px ) ∧ $ ( qx ) ) => wff px >> wff qx
      | q( $ ( px ) ↔ $ ( qx ) ) => wff px >> wff qx
      |
        q( $ ( expr.pi _ _ px qx ) )
        =>
        Monad.cond
          ( if expr.has_var px then return true else is_prop px )
            ( wff px >> wff qx )
            ( eq_int px >> wff qx )
      | q( @ LT.lt $ ( dx ) $ ( h ) _ _ ) => eq_int dx
      | q( @ LE.le $ ( dx ) $ ( h ) _ _ ) => eq_int dx
      | q( @ Eq $ ( dx ) _ _ ) => eq_int dx
      | q( @ GE.ge $ ( dx ) $ ( h ) _ _ ) => eq_int dx
      | q( @ GT.gt $ ( dx ) $ ( h ) _ _ ) => eq_int dx
      | q( @ Ne $ ( dx ) _ _ ) => eq_int dx
      | q( True ) => skip
      | q( False ) => skip
      | _ => failed
#align omega.int.wff omega.int.wff

/-- Succeed iff argument is expr of term whose type is wff -/
unsafe def wfx (x : expr) : tactic Unit :=
  infer_type x >>= wff
#align omega.int.wfx omega.int.wfx

/-- Intro all universal quantifiers over ℤ -/
unsafe def intro_ints_core : tactic Unit := do
  let x ← target
  match x with
    | expr.pi _ _ q(Int) _ => intro_fresh >> intro_ints_core
    | _ => skip
#align omega.int.intro_ints_core omega.int.intro_ints_core

unsafe def intro_ints : tactic Unit := do
  let expr.pi _ _ q(Int) _ ← target
  intro_ints_core
#align omega.int.intro_ints omega.int.intro_ints

/-- If the goal has universal quantifiers over integers, introduce all of them.
Otherwise, revert all hypotheses that are formulas of linear integer arithmetic. -/
unsafe def preprocess : tactic Unit :=
  intro_ints <|> revert_cond_all wfx >> desugar
#align omega.int.preprocess omega.int.preprocess

end Int

end Omega

open Omega.Int

/-- The core omega tactic for integers. -/
unsafe def omega_int (is_manual : Bool) : tactic Unit :=
  andthen (andthen desugar (if is_manual then skip else preprocess)) ((prove >>= apply) >> skip)
#align omega_int omega_int

