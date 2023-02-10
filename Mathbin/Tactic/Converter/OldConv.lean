/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Converter monad for building simplifiers.

! This file was ported from Lean 3 source module tactic.converter.old_conv
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Basic

open Tactic

unsafe structure old_conv_result (α : Type) where
  val : α
  rhs : expr
  proof : Option expr
#align old_conv_result old_conv_result

unsafe def old_conv (α : Type) : Type :=
  Name → expr → tactic (old_conv_result α)
#align old_conv old_conv

namespace OldConv

unsafe def lhs : old_conv expr := fun r e => return ⟨e, e, none⟩
#align old_conv.lhs old_conv.lhs

unsafe def change (new_p : pexpr) : old_conv Unit := fun r e => do
  let e_type ← infer_type e
  let new_e ← to_expr ``(($(new_p) : $(e_type)))
  unify e new_e
  return ⟨(), new_e, none⟩
#align old_conv.change old_conv.change

protected unsafe def pure {α : Type} : α → old_conv α := fun a r e => return ⟨a, e, none⟩
#align old_conv.pure old_conv.pure

private unsafe def join_proofs (r : Name) (o₁ o₂ : Option expr) : tactic (Option expr) :=
  match o₁, o₂ with
  | none, _ => return o₂
  | _, none => return o₁
  | some p₁, some p₂ => do
    let env ← get_env
    match env r with
      | some trans => do
        let pr ← mk_app trans [p₁, p₂]
        return <| some pr
      | none => fail f! "converter failed, relation '{r}' is not transitive"
#align old_conv.join_proofs old_conv.join_proofs

protected unsafe def seq {α β : Type} (c₁ : old_conv (α → β)) (c₂ : old_conv α) : old_conv β :=
  fun r e => do
  let ⟨fn, e₁, pr₁⟩ ← c₁ r e
  let ⟨a, e₂, pr₂⟩ ← c₂ r e₁
  let pr ← join_proofs r pr₁ pr₂
  return ⟨fn a, e₂, pr⟩
#align old_conv.seq old_conv.seq

protected unsafe def fail {α β : Type} [has_to_format β] (msg : β) : old_conv α := fun r e =>
  tactic.fail msg
#align old_conv.fail old_conv.fail

protected unsafe def failed {α : Type} : old_conv α := fun r e => tactic.failed
#align old_conv.failed old_conv.failed

protected unsafe def orelse {α : Type} (c₁ : old_conv α) (c₂ : old_conv α) : old_conv α :=
  fun r e => c₁ r e <|> c₂ r e
#align old_conv.orelse old_conv.orelse

protected unsafe def map {α β : Type} (f : α → β) (c : old_conv α) : old_conv β := fun r e => do
  let ⟨a, e₁, pr⟩ ← c r e
  return ⟨f a, e₁, pr⟩
#align old_conv.map old_conv.map

protected unsafe def bind {α β : Type} (c₁ : old_conv α) (c₂ : α → old_conv β) : old_conv β :=
  fun r e =>
  Bind.bind (c₁ r e) fun ⟨a, e₁, pr₁⟩ =>
    Bind.bind (c₂ a r e₁) fun ⟨b, e₂, pr₂⟩ =>
      Bind.bind (join_proofs r pr₁ pr₂) fun pr => return ⟨b, e₂, pr⟩
#align old_conv.bind old_conv.bind

/- do -- wrong bind instance something with `name`?
  ⟨a, e₁, pr₁⟩ ← c₁ r e,
  ⟨b, e₂, pr₂⟩ ← c₂ a r e₁,
  pr           ← join_proofs r pr₁ pr₂,
  return ⟨b, e₂, pr⟩
  -/
unsafe instance : Monad old_conv where
  map := @old_conv.map
  pure := @old_conv.pure
  bind := @old_conv.bind

unsafe instance : Alternative old_conv :=
  { old_conv.monad with
    failure := @old_conv.failed
    orelse := @old_conv.orelse }

unsafe def whnf (md : Transparency := reducible) : old_conv Unit := fun r e => do
  let n ← tactic.whnf e md
  return ⟨(), n, none⟩
#align old_conv.whnf old_conv.whnf

unsafe def dsimp : old_conv Unit := fun r e => do
  let s ← simp_lemmas.mk_default
  let n ← s.dsimplify [] e
  return ⟨(), n, none⟩
#align old_conv.dsimp old_conv.dsimp

unsafe def trace {α : Type} [has_to_tactic_format α] (a : α) : old_conv Unit := fun r e =>
  tactic.trace a >> return ⟨(), e, none⟩
#align old_conv.trace old_conv.trace

unsafe def trace_lhs : old_conv Unit :=
  lhs >>= trace
#align old_conv.trace_lhs old_conv.trace_lhs

unsafe def apply_lemmas_core (s : simp_lemmas) (prove : tactic Unit) : old_conv Unit := fun r e =>
  do
  let (new_e, pr) ← s.rewrite e prove r
  return ⟨(), new_e, some pr⟩
#align old_conv.apply_lemmas_core old_conv.apply_lemmas_core

unsafe def apply_lemmas (s : simp_lemmas) : old_conv Unit :=
  apply_lemmas_core s failed
#align old_conv.apply_lemmas old_conv.apply_lemmas

-- adapter for using iff-lemmas as eq-lemmas
unsafe def apply_propext_lemmas_core (s : simp_lemmas) (prove : tactic Unit) : old_conv Unit :=
  fun r e => do
  guard (r = `eq)
  let (new_e, pr) ← s.rewrite e prove `iff
  let new_pr ← mk_app `propext [pr]
  return ⟨(), new_e, some new_pr⟩
#align old_conv.apply_propext_lemmas_core old_conv.apply_propext_lemmas_core

unsafe def apply_propext_lemmas (s : simp_lemmas) : old_conv Unit :=
  apply_propext_lemmas_core s failed
#align old_conv.apply_propext_lemmas old_conv.apply_propext_lemmas

private unsafe def mk_refl_proof (r : Name) (e : expr) : tactic expr := do
  let env ← get_env
  match environment.refl_for env r with
    | some refl => do
      let pr ← mk_app refl [e]
      return pr
    | none => fail f! "converter failed, relation '{r}' is not reflexive"
#align old_conv.mk_refl_proof old_conv.mk_refl_proof

unsafe def to_tactic (c : old_conv Unit) : Name → expr → tactic (expr × expr) := fun r e => do
  let ⟨u, e₁, o⟩ ← c r e
  match o with
    | none => do
      let p ← mk_refl_proof r e
      return (e₁, p)
    | some p => return (e₁, p)
#align old_conv.to_tactic old_conv.to_tactic

unsafe def lift_tactic {α : Type} (t : tactic α) : old_conv α := fun r e => do
  let a ← t
  return ⟨a, e, none⟩
#align old_conv.lift_tactic old_conv.lift_tactic

unsafe def apply_simp_set (attr_name : Name) : old_conv Unit :=
  lift_tactic (get_user_simp_lemmas attr_name) >>= apply_lemmas
#align old_conv.apply_simp_set old_conv.apply_simp_set

unsafe def apply_propext_simp_set (attr_name : Name) : old_conv Unit :=
  lift_tactic (get_user_simp_lemmas attr_name) >>= apply_propext_lemmas
#align old_conv.apply_propext_simp_set old_conv.apply_propext_simp_set

unsafe def skip : old_conv Unit :=
  return ()
#align old_conv.skip old_conv.skip

unsafe def repeat : old_conv Unit → old_conv Unit
  | c, r, lhs =>
    (do
        let ⟨_, rhs₁, pr₁⟩ ← c r lhs
        guard ¬lhs == rhs₁
        let ⟨_, rhs₂, pr₂⟩ ← repeat c r rhs₁
        let pr ← join_proofs r pr₁ pr₂
        return ⟨(), rhs₂, pr⟩) <|>
      return ⟨(), lhs, none⟩
#align old_conv.repeat old_conv.repeat

unsafe def first {α : Type} : List (old_conv α) → old_conv α
  | [] => old_conv.failed
  | c :: cs => c <|> first cs
#align old_conv.first old_conv.first

unsafe def match_pattern (p : pattern) : old_conv Unit := fun r e =>
  tactic.match_pattern p e >> return ⟨(), e, none⟩
#align old_conv.match_pattern old_conv.match_pattern

unsafe def mk_match_expr (p : pexpr) : tactic (old_conv Unit) := do
  let new_p ← pexpr_to_pattern p
  return fun r e => tactic.match_pattern new_p e >> return ⟨(), e, none⟩
#align old_conv.mk_match_expr old_conv.mk_match_expr

unsafe def match_expr (p : pexpr) : old_conv Unit := fun r e => do
  let new_p ← pexpr_to_pattern p
  tactic.match_pattern new_p e >> return ⟨(), e, none⟩
#align old_conv.match_expr old_conv.match_expr

unsafe def funext (c : old_conv Unit) : old_conv Unit := fun r lhs => do
  guard (r = `eq)
  let expr.lam n bi d b ← return lhs
  let aux_type := expr.pi n bi d (expr.const `true [])
  let (result, _) ←
    solve_aux aux_type do
        let x ← intro1
        let c_result ← c r (b.instantiate_var x)
        let rhs := expr.lam n bi d (c_result.rhs.abstract x)
        match (motive := _ → tactic (old_conv_result Unit)) c_result with
          | some pr => do
            let aux_pr := expr.lam n bi d (pr x)
            let new_pr ← mk_app `funext [lhs, rhs, aux_pr]
            return ⟨(), rhs, some new_pr⟩
          | none => return ⟨(), rhs, none⟩
  return result
#align old_conv.funext old_conv.funext

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `f_type -/
unsafe def congr_core (c_f c_a : old_conv Unit) : old_conv Unit := fun r lhs => do
  guard (r = `eq)
  let expr.app f a ← return lhs
  let f_type ← infer_type f >>= tactic.whnf
  guard (f_type f_type.is_arrow)
  let ⟨(), new_f, of⟩ ← tryM c_f r f
  let ⟨(), new_a, oa⟩ ← tryM c_a r a
  let rhs ← return <| new_f new_a
  match of, oa with
    | none, none => return ⟨(), rhs, none⟩
    | none, some pr_a => do
      let pr ← mk_app `congr_arg [a, new_a, f, pr_a]
      return ⟨(), new_f new_a, some pr⟩
    | some pr_f, none => do
      let pr ← mk_app `congr_fun [f, new_f, pr_f, a]
      return ⟨(), rhs, some pr⟩
    | some pr_f, some pr_a => do
      let pr ← mk_app `congr [f, new_f, a, new_a, pr_f, pr_a]
      return ⟨(), rhs, some pr⟩
#align old_conv.congr_core old_conv.congr_core

unsafe def congr (c : old_conv Unit) : old_conv Unit :=
  congr_core c c
#align old_conv.congr old_conv.congr

unsafe def bottom_up (c : old_conv Unit) : old_conv Unit := fun r e => do
  let s ← simp_lemmas.mk_default
  let (a, new_e, pr) ←
    ext_simplify_core () { } s (fun u => return u) (fun a s r p e => failed)
        (fun a s r p e => do
          let ⟨u, new_e, pr⟩ ← c r e
          return ((), new_e, pr, tt))
        r e
  return ⟨(), new_e, some pr⟩
#align old_conv.bottom_up old_conv.bottom_up

unsafe def top_down (c : old_conv Unit) : old_conv Unit := fun r e => do
  let s ← simp_lemmas.mk_default
  let (a, new_e, pr) ←
    ext_simplify_core () { } s (fun u => return u)
        (fun a s r p e => do
          let ⟨u, new_e, pr⟩ ← c r e
          return ((), new_e, pr, tt))
        (fun a s r p e => failed) r e
  return ⟨(), new_e, some pr⟩
#align old_conv.top_down old_conv.top_down

unsafe def find (c : old_conv Unit) : old_conv Unit := fun r e => do
  let s ← simp_lemmas.mk_default
  let (a, new_e, pr) ←
    ext_simplify_core () { } s (fun u => return u)
        (fun a s r p e =>
          (do
              let ⟨u, new_e, pr⟩ ← c r e
              return ((), new_e, pr, ff)) <|>
            return ((), e, none, true))
        (fun a s r p e => failed) r e
  return ⟨(), new_e, some pr⟩
#align old_conv.find old_conv.find

unsafe def find_pattern (pat : pattern) (c : old_conv Unit) : old_conv Unit := fun r e => do
  let s ← simp_lemmas.mk_default
  let (a, new_e, pr) ←
    ext_simplify_core () { } s (fun u => return u)
        (fun a s r p e => do
          let matched ← tactic.match_pattern pat e >> return true <|> return false
          if matched then do
              let ⟨u, new_e, pr⟩ ← c r e
              return ((), new_e, pr, ff)
            else return ((), e, none, tt))
        (fun a s r p e => failed) r e
  return ⟨(), new_e, some pr⟩
#align old_conv.find_pattern old_conv.find_pattern

unsafe def findp : pexpr → old_conv Unit → old_conv Unit := fun p c r e => do
  let pat ← pexpr_to_pattern p
  find_pattern pat c r e
#align old_conv.findp old_conv.findp

unsafe def conversion (c : old_conv Unit) : tactic Unit := do
  let (r, lhs, rhs) ←
    target_lhs_rhs <|> fail "conversion failed, target is not of the form 'lhs R rhs'"
  let (new_lhs, pr) ← to_tactic c r lhs
  unify new_lhs rhs <|> do
      let new_lhs_fmt ← pp new_lhs
      let rhs_fmt ← pp rhs
      fail
          (to_fmt "conversion failed, expected" ++ rhs_fmt 4 ++ format.line ++ "provided" ++
            new_lhs_fmt 4)
  exact pr
#align old_conv.conversion old_conv.conversion

end OldConv

