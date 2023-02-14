/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module tactic.monotonicity.basic
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.WithBot

namespace Tactic.Interactive

open Tactic List

open Lean Lean.Parser Interactive

open Interactive.Types

structure MonoCfg where
  unify := false
  deriving Inhabited
#align tactic.interactive.mono_cfg Tactic.Interactive.MonoCfg

inductive MonoSelection : Type
  | left : mono_selection
  | right : mono_selection
  | both : mono_selection
  deriving DecidableEq, has_reflect, Inhabited
#align tactic.interactive.mono_selection Tactic.Interactive.MonoSelection

initialize
  registerTraceClass.1 `mono.relation

section Compare

parameter (opt : MonoCfg)

unsafe def compare (e₀ e₁ : expr) : tactic Unit := do
  if opt then do
      guard (¬e₀ ∧ ¬e₁)
      unify e₀ e₁
    else is_def_eq e₀ e₁
#align tactic.interactive.compare tactic.interactive.compare

unsafe def find_one_difference :
    List expr → List expr → tactic (List expr × expr × expr × List expr)
  | x :: xs, y :: ys => do
    let c ← try_core (compare x y)
    if c then Prod.map (cons x) id <$> find_one_difference xs ys
      else do
        guard (xs = ys)
        zipWithM' compare xs ys
        return ([], x, y, xs)
  | xs, ys => fail f! "find_one_difference: {xs }, {ys}"
#align tactic.interactive.find_one_difference tactic.interactive.find_one_difference

end Compare

def lastTwo {α : Type _} (l : List α) : Option (α × α) :=
  match l.reverse with
  | x₁ :: x₀ :: _ => some (x₀, x₁)
  | _ => none
#align tactic.interactive.last_two Tactic.Interactive.lastTwo

-- failed to format: unknown constant 'term.pseudo.antiquot'
unsafe
  def
    match_imp
    : expr → tactic ( expr × expr )
    | q( $ ( e₀ ) → $ ( e₁ ) ) => do guard ¬ e₁ return ( e₀ , e₁ ) | _ => failed
#align tactic.interactive.match_imp tactic.interactive.match_imp

open Expr

unsafe def same_operator : expr → expr → Bool
  | app e₀ _, app e₁ _ =>
    let fn₀ := e₀.get_app_fn
    let fn₁ := e₁.get_app_fn
    fn₀.is_constant ∧ fn₀.const_name = fn₁.const_name
  | pi _ _ _ _, pi _ _ _ _ => true
  | _, _ => false
#align tactic.interactive.same_operator tactic.interactive.same_operator

unsafe def get_operator (e : expr) : Option Name :=
  (guard ¬e.is_pi) >> pure e.get_app_fn.const_name
#align tactic.interactive.get_operator tactic.interactive.get_operator

unsafe def monotonicity.check_rel (l r : expr) : tactic (Option Name) := do
  guard (same_operator l r) <|> do
      fail f! "{l } and {r} should be the f x and f y for some f"
  if l then pure none else pure r
#align tactic.interactive.monotonicity.check_rel tactic.interactive.monotonicity.check_rel

@[reducible]
def MonoKey :=
  WithBot Name × WithBot Name
#align tactic.interactive.mono_key Tactic.Interactive.MonoKey

unsafe instance mono_key.has_lt : LT MonoKey where lt := Prod.Lex (· < ·) (· < ·)
#align tactic.interactive.mono_key.has_lt tactic.interactive.mono_key.has_lt

open Nat

unsafe def mono_head_candidates : ℕ → List expr → expr → tactic MonoKey
  | 0, _, h => throwError "Cannot find relation in {← h}"
  | succ n, xs, h =>
    (do
        let (Rel, l, r) ←
          if h.is_arrow then pure (none, h.binding_domain, h.binding_body)
            else
              guard h.get_app_fn.is_constant >>
                Prod.mk (some h.get_app_fn.const_name) <$> lastTwo h.get_app_args
        Prod.mk <$> monotonicity.check_rel l r <*> pure Rel) <|>
      match xs with
      | [] => fail f! "oh? {h}"
      | x :: xs => mono_head_candidates n xs (h.pis [x])
#align tactic.interactive.mono_head_candidates tactic.interactive.mono_head_candidates

unsafe def monotonicity.check (lm_n : Name) : tactic MonoKey := do
  let lm ← mk_const lm_n
  let lm_t ← infer_type lm >>= instantiate_mvars
  when_tracing `mono.relation
      (← do
        dbg_trace "[mono] Looking for relation in {← lm_t}")
  let s := simp_lemmas.mk
  let s ← s.add_simp `` Monotone
  let s ← s.add_simp `` StrictMono
  let lm_t ← s.dsimplify [] lm_t { failIfUnchanged := false }
  when_tracing `mono.relation
      (← do
        dbg_trace "[mono] Looking for relation in {← lm_t} (after unfolding)")
  let (xs, h) ← open_pis lm_t
  mono_head_candidates 3 xs h
#align tactic.interactive.monotonicity.check tactic.interactive.monotonicity.check

unsafe instance : has_to_format MonoSelection :=
  ⟨fun x =>
    match x with
    | mono_selection.left => "left"
    | mono_selection.right => "right"
    | mono_selection.both => "both"⟩

unsafe def side : lean.parser MonoSelection :=
  with_desc "expecting 'left', 'right' or 'both' (default)" do
    let some n ← optional ident |
      pure MonoSelection.both
    if n = `left then pure <| mono_selection.left
      else
        if n = `right then pure <| mono_selection.right
        else
          if n = `both then pure <| mono_selection.both
          else fail f! "invalid argument: {n}, expecting 'left', 'right' or 'both' (default)"
#align tactic.interactive.side tactic.interactive.side

open Function

@[user_attribute]
unsafe def monotonicity.attr :
    user_attribute (native.rb_lmap MonoKey Name) (Option MonoKey × MonoSelection)
    where
  Name := `mono
  descr := "monotonicity of function `f` wrt relations `R₀` and `R₁`: R₀ x y → R₁ (f x) (f y)"
  cache_cfg :=
    { dependencies := []
      mk_cache := fun ls => do
        let ps ← ls.mapM monotonicity.attr.get_param
        let ps := ps.filterMap Prod.fst
        pure <| (ps ls).foldl (flip <| uncurry fun k n m => m k n) (native.rb_lmap.mk mono_key _) }
  after_set :=
    some fun n prio p => do
      let (none, v) ← monotonicity.attr.get_param n |
        pure ()
      let k ← monotonicity.check n
      monotonicity.attr n (some k, v) p
  parser := Prod.mk none <$> side
#align tactic.interactive.monotonicity.attr tactic.interactive.monotonicity.attr

unsafe def filter_instances (e : MonoSelection) (ns : List Name) : tactic (List Name) :=
  ns.filterM fun n => do
    let d ← user_attribute.get_param_untyped monotonicity.attr n
    let (_, d) ← to_expr ``(id $(d)) >>= eval_expr (Option MonoKey × MonoSelection)
    return (e = d : Bool)
#align tactic.interactive.filter_instances tactic.interactive.filter_instances

unsafe def get_monotonicity_lemmas (k : expr) (e : MonoSelection) : tactic (List Name) := do
  let ns ← monotonicity.attr.get_cache
  let k' ←
    if k.is_pi then pure (get_operator k.binding_domain, none)
      else do
        let (x₀, x₁) ← lastTwo k.get_app_args
        pure (get_operator x₀, some k)
  let ns := ns.find_def [] k'
  let ns' ← filter_instances e ns
  if e ≠ mono_selection.both then (· ++ ·) ns' <$> filter_instances mono_selection.both ns
    else pure ns'
#align tactic.interactive.get_monotonicity_lemmas tactic.interactive.get_monotonicity_lemmas

end Tactic.Interactive

