/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
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

/- ./././Mathport/Syntax/Translate/Expr.lean:332:4: warning: unsupported (TODO): `[tacs] -/
unsafe def desugar :=
  sorry
#align omega.nat.desugar omega.nat.desugar

theorem univ_close_of_unsat_neg_elim_not (m) (p : Preform) : (negElim (¬* p)).Unsat → UnivClose p (fun _ => 0) m := by
  intro h1
  apply univ_close_of_valid
  apply valid_of_unsat_not
  intro h2
  apply h1
  apply preform.sat_of_implies_of_sat implies_neg_elim h2
#align omega.nat.univ_close_of_unsat_neg_elim_not Omega.Nat.univ_close_of_unsat_neg_elim_not

/-- Return expr of proof that argument is free of subtractions -/
unsafe def preterm.prove_sub_free : Preterm → tactic expr
  | &m => return (quote.1 trivial)
  | m ** n => return (quote.1 trivial)
  | t +* s => do
    let x ← preterm.prove_sub_free t
    let y ← preterm.prove_sub_free s
    return (quote.1 (@And.intro (Preterm.SubFree (%%ₓquote.1 t)) (Preterm.SubFree (%%ₓquote.1 s)) (%%ₓx) (%%ₓy)))
  | _ -* _ => failed
#align omega.nat.preterm.prove_sub_free omega.nat.preterm.prove_sub_free

/-- Return expr of proof that argument is free of negations -/
unsafe def prove_neg_free : Preform → tactic expr
  | t =* s => return (quote.1 trivial)
  | t ≤* s => return (quote.1 trivial)
  | p ∨* q => do
    let x ← prove_neg_free p
    let y ← prove_neg_free q
    return (quote.1 (@And.intro (Preform.NegFree (%%ₓquote.1 p)) (Preform.NegFree (%%ₓquote.1 q)) (%%ₓx) (%%ₓy)))
  | p ∧* q => do
    let x ← prove_neg_free p
    let y ← prove_neg_free q
    return (quote.1 (@And.intro (Preform.NegFree (%%ₓquote.1 p)) (Preform.NegFree (%%ₓquote.1 q)) (%%ₓx) (%%ₓy)))
  | _ => failed
#align omega.nat.prove_neg_free omega.nat.prove_neg_free

/-- Return expr of proof that argument is free of subtractions -/
unsafe def prove_sub_free : Preform → tactic expr
  | t =* s => do
    let x ← preterm.prove_sub_free t
    let y ← preterm.prove_sub_free s
    return (quote.1 (@And.intro (Preterm.SubFree (%%ₓquote.1 t)) (Preterm.SubFree (%%ₓquote.1 s)) (%%ₓx) (%%ₓy)))
  | t ≤* s => do
    let x ← preterm.prove_sub_free t
    let y ← preterm.prove_sub_free s
    return (quote.1 (@And.intro (Preterm.SubFree (%%ₓquote.1 t)) (Preterm.SubFree (%%ₓquote.1 s)) (%%ₓx) (%%ₓy)))
  | ¬* p => prove_sub_free p
  | p ∨* q => do
    let x ← prove_sub_free p
    let y ← prove_sub_free q
    return (quote.1 (@And.intro (Preform.SubFree (%%ₓquote.1 p)) (Preform.SubFree (%%ₓquote.1 q)) (%%ₓx) (%%ₓy)))
  | p ∧* q => do
    let x ← prove_sub_free p
    let y ← prove_sub_free q
    return (quote.1 (@And.intro (Preform.SubFree (%%ₓquote.1 p)) (Preform.SubFree (%%ₓquote.1 q)) (%%ₓx) (%%ₓy)))
#align omega.nat.prove_sub_free omega.nat.prove_sub_free

/-- Given a p : preform, return the expr of a term t : p.unsat, where p is subtraction- and
negation-free. -/
unsafe def prove_unsat_sub_free (p : Preform) : tactic expr := do
  let x ← prove_neg_free p
  let y ← prove_sub_free p
  let z ← prove_unsats (dnf p)
  return (quote.1 (unsat_of_unsat_dnf (%%ₓquote.1 p) (%%ₓx) (%%ₓy) (%%ₓz)))
#align omega.nat.prove_unsat_sub_free omega.nat.prove_unsat_sub_free

/-- Given a p : preform, return the expr of a term t : p.unsat, where p is negation-free. -/
unsafe def prove_unsat_neg_free : Preform → tactic expr
  | p =>
    match p.subTerms with
    | none => prove_unsat_sub_free p
    | some (t, s) => do
      let x ← prove_unsat_neg_free (subElim t s p)
      return (quote.1 (unsat_of_unsat_sub_elim (%%ₓquote.1 t) (%%ₓquote.1 s) (%%ₓquote.1 p) (%%ₓx)))
#align omega.nat.prove_unsat_neg_free omega.nat.prove_unsat_neg_free

/-- Given a (m : nat) and (p : preform), return the expr of (t : univ_close m p). -/
unsafe def prove_univ_close (m : Nat) (p : Preform) : tactic expr := do
  let x ← prove_unsat_neg_free (negElim (¬* p))
  to_expr (pquote.1 (univ_close_of_unsat_neg_elim_not (%%ₓquote.1 m) (%%ₓquote.1 p) (%%ₓx)))
#align omega.nat.prove_univ_close omega.nat.prove_univ_close

/-- Reification to imtermediate shadow syntax that retains exprs -/
unsafe def to_exprterm : expr → tactic exprterm
  | quote.1 ((%%ₓx) * %%ₓy) => do
    let m ← eval_expr' Nat y
    return (exprterm.exp m x)
  | quote.1 ((%%ₓt1x) + %%ₓt2x) => do
    let t1 ← to_exprterm t1x
    let t2 ← to_exprterm t2x
    return (exprterm.add t1 t2)
  | quote.1 ((%%ₓt1x) - %%ₓt2x) => do
    let t1 ← to_exprterm t1x
    let t2 ← to_exprterm t2x
    return (exprterm.sub t1 t2)
  | x =>
    (do
        let m ← eval_expr' Nat x
        return (exprterm.cst m)) <|>
      (return <| exprterm.exp 1 x)
#align omega.nat.to_exprterm omega.nat.to_exprterm

/-- Reification to imtermediate shadow syntax that retains exprs -/
unsafe def to_exprform : expr → tactic exprform
  | quote.1 ((%%ₓtx1) = %%ₓtx2) => do
    let t1 ← to_exprterm tx1
    let t2 ← to_exprterm tx2
    return (exprform.eq t1 t2)
  | quote.1 ((%%ₓtx1) ≤ %%ₓtx2) => do
    let t1 ← to_exprterm tx1
    let t2 ← to_exprterm tx2
    return (exprform.le t1 t2)
  | quote.1 ¬%%ₓpx => do
    let p ← to_exprform px
    return (exprform.not p)
  | quote.1 ((%%ₓpx) ∨ %%ₓqx) => do
    let p ← to_exprform px
    let q ← to_exprform qx
    return (exprform.or p q)
  | quote.1 ((%%ₓpx) ∧ %%ₓqx) => do
    let p ← to_exprform px
    let q ← to_exprform qx
    return (exprform.and p q)
  | quote.1 (_ → %%ₓpx) => to_exprform px
  | x => (trace "Cannot reify expr : " >> trace x) >> failed
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
  if x = quote.1 Nat then skip else failed
#align omega.nat.eq_nat omega.nat.eq_nat

/-- Check whether argument is expr of a well-formed formula of LNA-/
unsafe def wff : expr → tactic Unit
  | quote.1 ¬%%ₓpx => wff px
  | quote.1 ((%%ₓpx) ∨ %%ₓqx) => wff px >> wff qx
  | quote.1 ((%%ₓpx) ∧ %%ₓqx) => wff px >> wff qx
  | quote.1 ((%%ₓpx) ↔ %%ₓqx) => wff px >> wff qx
  | quote.1 (%%ₓexpr.pi _ _ px qx) =>
    Monad.cond (if expr.has_var px then return true else is_prop px) (wff px >> wff qx) (eq_nat px >> wff qx)
  | quote.1 (@LT.lt (%%ₓdx) (%%ₓh) _ _) => eq_nat dx
  | quote.1 (@LE.le (%%ₓdx) (%%ₓh) _ _) => eq_nat dx
  | quote.1 (@Eq (%%ₓdx) _ _) => eq_nat dx
  | quote.1 (@GE.ge (%%ₓdx) (%%ₓh) _ _) => eq_nat dx
  | quote.1 (@GT.gt (%%ₓdx) (%%ₓh) _ _) => eq_nat dx
  | quote.1 (@Ne (%%ₓdx) _ _) => eq_nat dx
  | quote.1 True => skip
  | quote.1 False => skip
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
    | expr.pi _ _ (quote.1 Nat) _ => intro_fresh >> intro_nats_core
    | _ => skip
#align omega.nat.intro_nats_core omega.nat.intro_nats_core

unsafe def intro_nats : tactic Unit := do
  let expr.pi _ _ (quote.1 Nat) _ ← target
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

