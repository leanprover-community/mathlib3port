/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek

! This file was ported from Lean 3 source module tactic.omega.nat.main
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Omega.ProveUnsats
import Mathbin.Tactic.Omega.Nat.Dnf
import Mathbin.Tactic.Omega.Nat.NegElim
import Mathbin.Tactic.Omega.Nat.SubElim

/-
Main procedure for linear natural number arithmetic.
-/
open Tactic

namespace Omega

namespace Nat

open Omega.Nat

run_cmd
  mk_simp_attr `sugar_nat

attribute [sugar_nat]
  Ne not_le not_lt Nat.lt_iff_add_one_le Nat.succ_eq_add_one or_false_iff false_or_iff and_true_iff true_and_iff GE.ge GT.gt mul_add add_mul mul_comm one_mul mul_one imp_iff_not_or iff_iff_not_or_and_or_not

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
unsafe def desugar :=
  sorry
#align omega.nat.desugar omega.nat.desugar

theorem univ_close_of_unsat_neg_elim_not (m) (p : Preform) :
    (negElim (¬* p)).Unsat → UnivClose p (fun _ => 0) m := by
  intro h1; apply univ_close_of_valid
  apply valid_of_unsat_not; intro h2; apply h1
  apply preform.sat_of_implies_of_sat implies_neg_elim h2
#align omega.nat.univ_close_of_unsat_neg_elim_not Omega.Nat.univ_close_of_unsat_neg_elim_not

/-- Return expr of proof that argument is free of subtractions -/
unsafe def preterm.prove_sub_free : Preterm → tactic expr
  | &m => return q(trivial)
  | m ** n => return q(trivial)
  | t +* s => do
    let x ← preterm.prove_sub_free t
    let y ← preterm.prove_sub_free s
    return q(@And.intro (Preterm.SubFree $(q(t))) (Preterm.SubFree $(q(s))) $(x) $(y))
  | _ -* _ => failed
#align omega.nat.preterm.prove_sub_free omega.nat.preterm.prove_sub_free

/-- Return expr of proof that argument is free of negations -/
unsafe def prove_neg_free : Preform → tactic expr
  | t =* s => return q(trivial)
  | t ≤* s => return q(trivial)
  | p ∨* q => do
    let x ← prove_neg_free p
    let y ← prove_neg_free q
    return q(@And.intro (Preform.NegFree $(q(p))) (Preform.NegFree $(q(q))) $(x) $(y))
  | p ∧* q => do
    let x ← prove_neg_free p
    let y ← prove_neg_free q
    return q(@And.intro (Preform.NegFree $(q(p))) (Preform.NegFree $(q(q))) $(x) $(y))
  | _ => failed
#align omega.nat.prove_neg_free omega.nat.prove_neg_free

/-- Return expr of proof that argument is free of subtractions -/
unsafe def prove_sub_free : Preform → tactic expr
  | t =* s => do
    let x ← preterm.prove_sub_free t
    let y ← preterm.prove_sub_free s
    return q(@And.intro (Preterm.SubFree $(q(t))) (Preterm.SubFree $(q(s))) $(x) $(y))
  | t ≤* s => do
    let x ← preterm.prove_sub_free t
    let y ← preterm.prove_sub_free s
    return q(@And.intro (Preterm.SubFree $(q(t))) (Preterm.SubFree $(q(s))) $(x) $(y))
  | ¬* p => prove_sub_free p
  | p ∨* q => do
    let x ← prove_sub_free p
    let y ← prove_sub_free q
    return q(@And.intro (Preform.SubFree $(q(p))) (Preform.SubFree $(q(q))) $(x) $(y))
  | p ∧* q => do
    let x ← prove_sub_free p
    let y ← prove_sub_free q
    return q(@And.intro (Preform.SubFree $(q(p))) (Preform.SubFree $(q(q))) $(x) $(y))
#align omega.nat.prove_sub_free omega.nat.prove_sub_free

/-- Given a p : preform, return the expr of a term t : p.unsat, where p is subtraction- and
negation-free. -/
unsafe def prove_unsat_sub_free (p : Preform) : tactic expr := do
  let x ← prove_neg_free p
  let y ← prove_sub_free p
  let z ← prove_unsats (dnf p)
  return q(unsat_of_unsat_dnf $(q(p)) $(x) $(y) $(z))
#align omega.nat.prove_unsat_sub_free omega.nat.prove_unsat_sub_free

/-- Given a p : preform, return the expr of a term t : p.unsat, where p is negation-free. -/
unsafe def prove_unsat_neg_free : Preform → tactic expr
  | p =>
    match p.subTerms with
    | none => prove_unsat_sub_free p
    | some (t, s) => do
      let x ← prove_unsat_neg_free (subElim t s p)
      return q(unsat_of_unsat_sub_elim $(q(t)) $(q(s)) $(q(p)) $(x))
#align omega.nat.prove_unsat_neg_free omega.nat.prove_unsat_neg_free

/-- Given a (m : nat) and (p : preform), return the expr of (t : univ_close m p). -/
unsafe def prove_univ_close (m : Nat) (p : Preform) : tactic expr := do
  let x ← prove_unsat_neg_free (negElim (¬* p))
  to_expr ``(univ_close_of_unsat_neg_elim_not $(q(m)) $(q(p)) $(x))
#align omega.nat.prove_univ_close omega.nat.prove_univ_close

-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- Reification to imtermediate shadow syntax that retains exprs -/ unsafe
  def
    to_exprterm
    : expr → tactic exprterm
    | q( $ ( x ) * $ ( y ) ) => do let m ← eval_expr' Nat y return ( exprterm.exp m x )
      |
        q( $ ( t1x ) + $ ( t2x ) )
        =>
        do let t1 ← to_exprterm t1x let t2 ← to_exprterm t2x return ( exprterm.add t1 t2 )
      |
        q( $ ( t1x ) - $ ( t2x ) )
        =>
        do let t1 ← to_exprterm t1x let t2 ← to_exprterm t2x return ( exprterm.sub t1 t2 )
      |
        x
        =>
        ( do let m ← eval_expr' Nat x return ( exprterm.cst m ) ) <|> ( return <| exprterm.exp 1 x )
#align omega.nat.to_exprterm omega.nat.to_exprterm

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
#align omega.nat.to_exprform omega.nat.to_exprform

/-- List of all unreified exprs -/
unsafe def exprterm.exprs : exprterm → List expr
  | exprterm.cst _ => []
  | exprterm.exp _ x => [x]
  | exprterm.add t s => List.union t.exprs s.exprs
  | exprterm.sub t s => List.union t.exprs s.exprs
#align omega.nat.exprterm.exprs omega.nat.exprterm.exprs

/-- List of all unreified exprs -/
unsafe def exprform.exprs : exprform → List expr
  | exprform.eq t s => List.union t.exprs s.exprs
  | exprform.le t s => List.union t.exprs s.exprs
  | exprform.not p => p.exprs
  | exprform.or p q => List.union p.exprs q.exprs
  | exprform.and p q => List.union p.exprs q.exprs
#align omega.nat.exprform.exprs omega.nat.exprform.exprs

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
  | exprterm.sub xa xb => do
    let a ← xa.to_preterm
    let b ← xb.to_preterm
    return (a -* b)
#align omega.nat.exprterm.to_preterm omega.nat.exprterm.to_preterm

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
#align omega.nat.exprform.to_preform omega.nat.exprform.to_preform

/-- Reification to an intermediate shadow syntax which eliminates exprs,
    but still includes non-canonical terms. -/
unsafe def to_preform (x : expr) : tactic (preform × Nat) := do
  let xf ← to_exprform x
  let xs := xf.exprs
  let f ← xf.to_preform xs
  return (f, xs)
#align omega.nat.to_preform omega.nat.to_preform

/-- Return expr of proof of current LNA goal -/
unsafe def prove : tactic expr := do
  let (p, m) ← target >>= to_preform
  trace_if_enabled `omega p
  prove_univ_close m p
#align omega.nat.prove omega.nat.prove

/-- Succeed iff argument is expr of ℕ -/
unsafe def eq_nat (x : expr) : tactic Unit :=
  if x = q(Nat) then skip else failed
#align omega.nat.eq_nat omega.nat.eq_nat

-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- Check whether argument is expr of a well-formed formula of LNA-/ unsafe
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
            ( eq_nat px >> wff qx )
      | q( @ LT.lt $ ( dx ) $ ( h ) _ _ ) => eq_nat dx
      | q( @ LE.le $ ( dx ) $ ( h ) _ _ ) => eq_nat dx
      | q( @ Eq $ ( dx ) _ _ ) => eq_nat dx
      | q( @ GE.ge $ ( dx ) $ ( h ) _ _ ) => eq_nat dx
      | q( @ GT.gt $ ( dx ) $ ( h ) _ _ ) => eq_nat dx
      | q( @ Ne $ ( dx ) _ _ ) => eq_nat dx
      | q( True ) => skip
      | q( False ) => skip
      | _ => failed
#align omega.nat.wff omega.nat.wff

/-- Succeed iff argument is expr of term whose type is wff -/
unsafe def wfx (x : expr) : tactic Unit :=
  infer_type x >>= wff
#align omega.nat.wfx omega.nat.wfx

/-- Intro all universal quantifiers over nat -/
unsafe def intro_nats_core : tactic Unit := do
  let x ← target
  match x with
    | expr.pi _ _ q(Nat) _ => intro_fresh >> intro_nats_core
    | _ => skip
#align omega.nat.intro_nats_core omega.nat.intro_nats_core

unsafe def intro_nats : tactic Unit := do
  let expr.pi _ _ q(Nat) _ ← target
  intro_nats_core
#align omega.nat.intro_nats omega.nat.intro_nats

/-- If the goal has universal quantifiers over natural, introduce all of them.
Otherwise, revert all hypotheses that are formulas of linear natural number arithmetic. -/
unsafe def preprocess : tactic Unit :=
  intro_nats <|> revert_cond_all wfx >> desugar
#align omega.nat.preprocess omega.nat.preprocess

end Nat

end Omega

open Omega.Nat

/-- The core omega tactic for natural numbers. -/
unsafe def omega_nat (is_manual : Bool) : tactic Unit :=
  andthen (andthen desugar (if is_manual then skip else preprocess)) ((prove >>= apply) >> skip)
#align omega_nat omega_nat

