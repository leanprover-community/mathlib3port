/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module tactic.monotonicity.interactive
! leanprover-community/mathlib commit 940d371319c6658e526349d2c3e1daeeabfae0fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Traversable.Derive
import Mathbin.Control.Traversable.Lemmas
import Leanbin.Data.Dlist
import Mathbin.Tactic.Monotonicity.Basic

variable {a b c p : Prop}

namespace Tactic.Interactive

open Lean Lean.Parser Interactive

open Interactive.Types

open Tactic

-- mathport name: parser.optional
local postfix:1024 "?" => optional

-- mathport name: parser.many
local postfix:1024 "*" => many

unsafe inductive mono_function (elab : Bool := true)
  | non_assoc : expr elab → List (expr elab) → List (expr elab) → mono_function
  | assoc : expr elab → Option (expr elab) → Option (expr elab) → mono_function
  | assoc_comm : expr elab → expr elab → mono_function
#align tactic.interactive.mono_function tactic.interactive.mono_function

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_dec_eq_instance -/
unsafe instance : DecidableEq mono_function := by
  run_tac
    mk_dec_eq_instance

unsafe def mono_function.to_tactic_format : mono_function → tactic format
  | mono_function.non_assoc fn xs ys => do
    let fn' ← pp fn
    let xs' ← mapM pp xs
    let ys' ← mapM pp ys
    return f! "{fn' } {xs' } _ {ys'}"
  | mono_function.assoc fn xs ys => do
    let fn' ← pp fn
    let xs' ← pp xs
    let ys' ← pp ys
    return f! "{fn' } {xs' } _ {ys'}"
  | mono_function.assoc_comm fn xs => do
    let fn' ← pp fn
    let xs' ← pp xs
    return f! "{fn' } _ {xs'}"
#align
  tactic.interactive.mono_function.to_tactic_format tactic.interactive.mono_function.to_tactic_format

unsafe instance has_to_tactic_format_mono_function : has_to_tactic_format mono_function
    where to_tactic_format := mono_function.to_tactic_format
#align
  tactic.interactive.has_to_tactic_format_mono_function tactic.interactive.has_to_tactic_format_mono_function

unsafe structure ac_mono_ctx' (rel : Type) where
  to_rel : Rel
  function : mono_function
  (left right rel_def : expr)
  deriving Traversable
#align tactic.interactive.ac_mono_ctx' tactic.interactive.ac_mono_ctx'

@[reducible]
unsafe def ac_mono_ctx :=
  ac_mono_ctx' (Option (expr → expr → expr))
#align tactic.interactive.ac_mono_ctx tactic.interactive.ac_mono_ctx

@[reducible]
unsafe def ac_mono_ctx_ne :=
  ac_mono_ctx' (expr → expr → expr)
#align tactic.interactive.ac_mono_ctx_ne tactic.interactive.ac_mono_ctx_ne

unsafe def ac_mono_ctx.to_tactic_format (ctx : ac_mono_ctx) : tactic format := do
  let fn ← pp ctx.function
  let l ← pp ctx.left
  let r ← pp ctx.right
  let rel ← pp ctx.rel_def
  return
      f! "\{ function := {fn }
        , left  := {l }
        , right := {r }
        , rel_def := {Rel} }}"
#align
  tactic.interactive.ac_mono_ctx.to_tactic_format tactic.interactive.ac_mono_ctx.to_tactic_format

unsafe instance has_to_tactic_format_mono_ctx : has_to_tactic_format ac_mono_ctx
    where to_tactic_format := ac_mono_ctx.to_tactic_format
#align
  tactic.interactive.has_to_tactic_format_mono_ctx tactic.interactive.has_to_tactic_format_mono_ctx

unsafe def as_goal (e : expr) (tac : tactic Unit) : tactic Unit := do
  let gs ← get_goals
  set_goals [e]
  tac
  set_goals gs
#align tactic.interactive.as_goal tactic.interactive.as_goal

open List hiding map

open Functor Dlist

section Config

parameter (opt : MonoCfg)

parameter (asms : List expr)

unsafe def unify_with_instance (e : expr) : tactic Unit :=
  as_goal e <|
    apply_instance <|>
      apply_opt_param <|>
        apply_auto_param <|>
          tactic.solve_by_elim { lemmas := some asms } <|>
            reflexivity <|> applyc `` id <|> return ()
#align tactic.interactive.unify_with_instance tactic.interactive.unify_with_instance

private unsafe def match_rule_head (p : expr) : List expr → expr → expr → tactic expr
  | vs, e, t =>
    (unify t p >> mapM' unify_with_instance vs.reverse) >> instantiate_mvars e <|> do
      let expr.pi _ _ d b ← return t |
        failed
      let v ← mk_meta_var d
      match_rule_head (v :: vs) (expr.app e v) (b v)
#align tactic.interactive.match_rule_head tactic.interactive.match_rule_head

unsafe def pi_head : expr → tactic expr
  | expr.pi n _ t b => do
    let v ← mk_meta_var t
    pi_head (b v)
  | e => return e
#align tactic.interactive.pi_head tactic.interactive.pi_head

unsafe def delete_expr (e : expr) : List expr → tactic (Option (List expr))
  | [] => return none
  | x :: xs => compare opt e x >> return (some xs) <|> map (cons x) <$> delete_expr xs
#align tactic.interactive.delete_expr tactic.interactive.delete_expr

unsafe def match_ac' : List expr → List expr → tactic (List expr × List expr × List expr)
  | es, x :: xs => do
    let es' ← delete_expr x es
    match es' with
      | some es' => do
        let (c, l, r) ← match_ac' es' xs
        return (x :: c, l, r)
      | none => do
        let (c, l, r) ← match_ac' es xs
        return (c, l, x :: r)
  | es, [] => do
    return ([], es, [])
#align tactic.interactive.match_ac' tactic.interactive.match_ac'

unsafe def match_ac (l : List expr) (r : List expr) : tactic (List expr × List expr × List expr) :=
  do
  let (s', l', r') ← match_ac' l r
  let s' ← mapM instantiate_mvars s'
  let l' ← mapM instantiate_mvars l'
  let r' ← mapM instantiate_mvars r'
  return (s', l', r')
#align tactic.interactive.match_ac tactic.interactive.match_ac

unsafe def match_prefix : List expr → List expr → tactic (List expr × List expr × List expr)
  | x :: xs, y :: ys =>
    (do
        compare opt x y
        Prod.map ((· :: ·) x) id <$> match_prefix xs ys) <|>
      return ([], x :: xs, y :: ys)
  | xs, ys => return ([], xs, ys)
#align tactic.interactive.match_prefix tactic.interactive.match_prefix

/-- `(prefix,left,right,suffix) ← match_assoc unif l r` finds the
longest prefix and suffix common to `l` and `r` and
returns them along with the differences  -/
unsafe def match_assoc (l : List expr) (r : List expr) :
    tactic (List expr × List expr × List expr × List expr) := do
  let (pre, l₁, r₁) ← match_prefix l r
  let (suf, l₂, r₂) ← match_prefix (reverse l₁) (reverse r₁)
  return (pre, reverse l₂, reverse r₂, reverse suf)
#align tactic.interactive.match_assoc tactic.interactive.match_assoc

unsafe def check_ac : expr → tactic (Bool × Bool × Option (expr × expr × expr) × expr)
  | expr.app (expr.app f x) y => do
    let t ← infer_type x
    let a ← try_core <| to_expr ``(IsAssociative $(t) $(f)) >>= mk_instance
    let c ← try_core <| to_expr ``(IsCommutative $(t) $(f)) >>= mk_instance
    let i ←
      try_core do
          let v ← mk_meta_var t
          let l_inst_p ← to_expr ``(IsLeftId $(t) $(f) $(v))
          let r_inst_p ← to_expr ``(IsRightId $(t) $(f) $(v))
          let l_v ← mk_meta_var l_inst_p
          let r_v ← mk_meta_var r_inst_p
          let l_id ← mk_mapp `is_left_id.left_id [some t, f, v, some l_v]
          mk_instance l_inst_p >>= unify l_v
          let r_id ← mk_mapp `is_right_id.right_id [none, f, v, some r_v]
          mk_instance r_inst_p >>= unify r_v
          let v' ← instantiate_mvars v
          return (l_id, r_id, v')
    return (a, c, i, f)
  | _ => return (false, false, none, expr.var 1)
#align tactic.interactive.check_ac tactic.interactive.check_ac

unsafe def parse_assoc_chain' (f : expr) : expr → tactic (Dlist expr)
  | e =>
    (do
        let expr.app (expr.app f' x) y ← return e
        is_def_eq f f'
        (· ++ ·) <$> parse_assoc_chain' x <*> parse_assoc_chain' y) <|>
      return (singleton e)
#align tactic.interactive.parse_assoc_chain' tactic.interactive.parse_assoc_chain'

unsafe def parse_assoc_chain (f : expr) : expr → tactic (List expr) :=
  map Dlist.toList ∘ parse_assoc_chain' f
#align tactic.interactive.parse_assoc_chain tactic.interactive.parse_assoc_chain

unsafe def fold_assoc (op : expr) :
    Option (expr × expr × expr) → List expr → Option (expr × List expr)
  | _, x :: xs => some (foldl (expr.app ∘ expr.app op) x xs, [])
  | none, [] => none
  | some (l_id, r_id, x₀), [] => some (x₀, [l_id, r_id])
#align tactic.interactive.fold_assoc tactic.interactive.fold_assoc

unsafe def fold_assoc1 (op : expr) : List expr → Option expr
  | x :: xs => some <| foldl (expr.app ∘ expr.app op) x xs
  | [] => none
#align tactic.interactive.fold_assoc1 tactic.interactive.fold_assoc1

unsafe def same_function_aux :
    List expr → List expr → expr → expr → tactic (expr × List expr × List expr)
  | xs₀, xs₁, expr.app f₀ a₀, expr.app f₁ a₁ => same_function_aux (a₀ :: xs₀) (a₁ :: xs₁) f₀ f₁
  | xs₀, xs₁, e₀, e₁ => is_def_eq e₀ e₁ >> return (e₀, xs₀, xs₁)
#align tactic.interactive.same_function_aux tactic.interactive.same_function_aux

unsafe def same_function : expr → expr → tactic (expr × List expr × List expr) :=
  same_function_aux [] []
#align tactic.interactive.same_function tactic.interactive.same_function

unsafe def parse_ac_mono_function (l r : expr) : tactic (expr × expr × List expr × mono_function) :=
  do
  let (full_f, ls, rs) ← same_function l r
  let (a, c, i, f) ← check_ac l
  if a then
      if c then do
        let (s, ls, rs) ← Monad.join (match_ac <$> parse_assoc_chain f l <*> parse_assoc_chain f r)
        let (l', l_id) ← fold_assoc f i ls
        let (r', r_id) ← fold_assoc f i rs
        let s' ← fold_assoc1 f s
        return (l', r', l_id ++ r_id, mono_function.assoc_comm f s')
      else do
        let-- a ∧ ¬ c
          (pre, ls, rs, suff)
          ← Monad.join (match_assoc <$> parse_assoc_chain f l <*> parse_assoc_chain f r)
        let (l', l_id) ← fold_assoc f i ls
        let (r', r_id) ← fold_assoc f i rs
        let pre' := fold_assoc1 f pre
        let suff' := fold_assoc1 f suff
        return (l', r', l_id ++ r_id, mono_function.assoc f pre' suff')
    else do
      let-- ¬ a
        (xs₀, x₀, x₁, xs₁)
        ← find_one_difference opt ls rs
      return (x₀, x₁, [], mono_function.non_assoc full_f xs₀ xs₁)
#align tactic.interactive.parse_ac_mono_function tactic.interactive.parse_ac_mono_function

unsafe def parse_ac_mono_function' (l r : pexpr) := do
  let l' ← to_expr l
  let r' ← to_expr r
  parse_ac_mono_function l' r'
#align tactic.interactive.parse_ac_mono_function' tactic.interactive.parse_ac_mono_function'

-- failed to format: unknown constant 'term.pseudo.antiquot'
unsafe
  def
    ac_monotonicity_goal
    : expr → tactic ( expr × expr × List expr × ac_mono_ctx )
    |
        q( $ ( e₀ ) → $ ( e₁ ) )
        =>
        do
          let ( l , r , id_rs , f ) ← parse_ac_mono_function e₀ e₁
            let t₀ ← infer_type e₀
            let t₁ ← infer_type e₁
            let rel_def ← to_expr ` `( fun x₀ x₁ => ( x₀ : $ ( t₀ ) ) → ( x₁ : $ ( t₁ ) ) )
            return
              (
                e₀
                  ,
                  e₁
                    ,
                    id_rs
                    ,
                    {
                      function := f
                        left := l
                        right := r
                        to_rel := some <| expr.pi `x BinderInfo.default
                        rel_def
                      }
                )
      |
        q( $ ( e₀ ) = $ ( e₁ ) )
        =>
        do
          let ( l , r , id_rs , f ) ← parse_ac_mono_function e₀ e₁
            let t₀ ← infer_type e₀
            let t₁ ← infer_type e₁
            let rel_def ← to_expr ` `( fun x₀ x₁ => ( x₀ : $ ( t₀ ) ) = ( x₁ : $ ( t₁ ) ) )
            return
              ( e₀ , e₁ , id_rs , { function := f left := l right := r to_rel := none rel_def } )
      |
        expr.app ( expr.app Rel e₀ ) e₁
        =>
        do
          let ( l , r , id_rs , f ) ← parse_ac_mono_function e₀ e₁
            return
              (
                e₀
                  ,
                  e₁
                    ,
                    id_rs
                    ,
                    {
                      function := f
                        left := l
                        right := r
                        to_rel := expr.app ∘ expr.app Rel
                        rel_def := Rel
                      }
                )
      | _ => fail "invalid monotonicity goal"
#align tactic.interactive.ac_monotonicity_goal tactic.interactive.ac_monotonicity_goal

unsafe def bin_op_left (f : expr) : Option expr → expr → expr
  | none, e => e
  | some e₀, e₁ => f.mk_app [e₀, e₁]
#align tactic.interactive.bin_op_left tactic.interactive.bin_op_left

unsafe def bin_op (f a b : expr) : expr :=
  f.mk_app [a, b]
#align tactic.interactive.bin_op tactic.interactive.bin_op

unsafe def bin_op_right (f : expr) : expr → Option expr → expr
  | e, none => e
  | e₀, some e₁ => f.mk_app [e₀, e₁]
#align tactic.interactive.bin_op_right tactic.interactive.bin_op_right

unsafe def mk_fun_app : mono_function → expr → expr
  | mono_function.non_assoc f x y, z => f.mk_app (x ++ z :: y)
  | mono_function.assoc f x y, z => bin_op_left f x (bin_op_right f z y)
  | mono_function.assoc_comm f x, z => f.mk_app [z, x]
#align tactic.interactive.mk_fun_app tactic.interactive.mk_fun_app

unsafe inductive mono_law/- `assoc (l₀,r₀) (r₁,l₁)` gives first how to find rules to prove
      x+(y₀+z) R x+(y₁+z);
      if that fails, helps prove (x+y₀)+z R (x+y₁)+z -/

  |
  assoc :
    expr × expr → expr × expr → mono_law-- `congr r` gives the rule to prove `x = y → f x = f y`

  | congr : expr → mono_law
  | other : expr → mono_law
#align tactic.interactive.mono_law tactic.interactive.mono_law

unsafe def mono_law.to_tactic_format : mono_law → tactic format
  | mono_law.other e => do
    let e ← pp e
    return f! "other {e}"
  | mono_law.congr r => do
    let e ← pp r
    return f! "congr {e}"
  | mono_law.assoc (x₀, x₁) (y₀, y₁) => do
    let x₀ ← pp x₀
    let x₁ ← pp x₁
    let y₀ ← pp y₀
    let y₁ ← pp y₁
    return f! "assoc {x₀ }; {x₁ } | {y₀ }; {y₁}"
#align tactic.interactive.mono_law.to_tactic_format tactic.interactive.mono_law.to_tactic_format

unsafe instance has_to_tactic_format_mono_law : has_to_tactic_format mono_law
    where to_tactic_format := mono_law.to_tactic_format
#align
  tactic.interactive.has_to_tactic_format_mono_law tactic.interactive.has_to_tactic_format_mono_law

unsafe def mk_rel (ctx : ac_mono_ctx_ne) (f : expr → expr) : expr :=
  ctx.to_rel (f ctx.left) (f ctx.right)
#align tactic.interactive.mk_rel tactic.interactive.mk_rel

/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `xs₁ -/
unsafe def mk_congr_args (fn : expr) (xs₀ xs₁ : List expr) (l r : expr) : tactic expr := do
  let p ← mk_app `eq [fn.mk_app <| xs₀ ++ l :: xs₁, fn.mk_app <| xs₀ ++ r :: xs₁]
  Prod.snd <$>
      solve_aux p do
        iterate_exactly (xs₁ xs₁.length) (applyc `congr_fun)
        applyc `congr_arg
#align tactic.interactive.mk_congr_args tactic.interactive.mk_congr_args

unsafe def mk_congr_law (ctx : ac_mono_ctx) : tactic expr :=
  match ctx.function with
  | mono_function.assoc f x₀ x₁ =>
    if (x₀ <|> x₁).isSome then mk_congr_args f x₀.toMonad x₁.toMonad ctx.left ctx.right else failed
  | mono_function.assoc_comm f x₀ => mk_congr_args f [x₀] [] ctx.left ctx.right
  | mono_function.non_assoc f x₀ x₁ => mk_congr_args f x₀ x₁ ctx.left ctx.right
#align tactic.interactive.mk_congr_law tactic.interactive.mk_congr_law

unsafe def mk_pattern (ctx : ac_mono_ctx) : tactic mono_law :=
  match (sequence ctx : Option (ac_mono_ctx' _)) with
  | some ctx =>
    match ctx.function with
    | mono_function.assoc f (some x) (some y) =>
      return <|
        mono_law.assoc
          (mk_rel ctx fun i => bin_op f x (bin_op f i y), mk_rel ctx fun i => bin_op f i y)
          (mk_rel ctx fun i => bin_op f (bin_op f x i) y, mk_rel ctx fun i => bin_op f x i)
    | mono_function.assoc f (some x) none =>
      return <| mono_law.other <| mk_rel ctx fun e => mk_fun_app ctx.function e
    | mono_function.assoc f none (some y) =>
      return <| mono_law.other <| mk_rel ctx fun e => mk_fun_app ctx.function e
    | mono_function.assoc f none none => none
    | _ => return <| mono_law.other <| mk_rel ctx fun e => mk_fun_app ctx.function e
  | none => mono_law.congr <$> mk_congr_law ctx
#align tactic.interactive.mk_pattern tactic.interactive.mk_pattern

unsafe def match_rule (pat : expr) (r : Name) : tactic expr := do
  let r' ← mk_const r
  let t ← infer_type r'
  let t ←
    expr.dsimp t { failIfUnchanged := false } true []
        [simp_arg_type.expr ``(Monotone), simp_arg_type.expr ``(StrictMono)]
  match_rule_head pat [] r' t
#align tactic.interactive.match_rule tactic.interactive.match_rule

unsafe def find_lemma (pat : expr) : List Name → tactic (List expr)
  | [] => return []
  | r :: rs => do
    (cons <$> match_rule pat r <|> pure id) <*> find_lemma rs
#align tactic.interactive.find_lemma tactic.interactive.find_lemma

-- failed to format: unknown constant 'term.pseudo.antiquot'
unsafe
  def
    match_chaining_rules
    ( ls : List Name ) ( x₀ x₁ : expr ) : tactic ( List expr )
    :=
      do
        let x' ← to_expr ` `( $ ( x₁ ) → $ ( x₀ ) )
          let r₀ ← find_lemma x' ls
          let r₁ ← find_lemma x₁ ls
          return ( expr.app <$> r₀ <*> r₁ )
#align tactic.interactive.match_chaining_rules tactic.interactive.match_chaining_rules

unsafe def find_rule (ls : List Name) : mono_law → tactic (List expr)
  | mono_law.assoc (x₀, x₁) (y₀, y₁) =>
    match_chaining_rules ls x₀ x₁ <|> match_chaining_rules ls y₀ y₁
  | mono_law.congr r => return [r]
  | mono_law.other p => find_lemma p ls
#align tactic.interactive.find_rule tactic.interactive.find_rule

universe u v

def applyRel {α : Sort u} (R : α → α → Sort v) {x y : α} (x' y' : α) (h : R x y) (hx : x = x')
    (hy : y = y') : R x' y' := by
  rw [← hx, ← hy]
  apply h
#align tactic.interactive.apply_rel Tactic.Interactive.applyRel

unsafe def ac_refine (e : expr) : tactic Unit :=
  andthen (refine ``(Eq.mp _ $(e))) ac_refl
#align tactic.interactive.ac_refine tactic.interactive.ac_refine

unsafe def one_line (e : expr) : tactic format := do
  let lbl ← pp e
  let asm ← infer_type e >>= pp
  return
      f! "	{asm}
        "
#align tactic.interactive.one_line tactic.interactive.one_line

unsafe def side_conditions (e : expr) : tactic format := do
  let vs := e.list_meta_vars
  let ts ← mapM one_line vs.tail
  let r := e.get_app_fn.const_name
  return
      f! "{r }:
        {format.join ts}"
#align tactic.interactive.side_conditions tactic.interactive.side_conditions

open Monad

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      tactic-facing function, similar to `interactive.tactic.generalize` with the
      exception that meta variables -/
    private
    unsafe
  def
    monotonicity.generalize'
    ( h : Name ) ( v : expr ) ( x : Name ) : tactic ( expr × expr )
    :=
      do
        let tgt ← target
          let t ← infer_type v
          let
            tgt'
              ←
              (
                  do
                    let ⟨ tgt' , _ ⟩ ← solve_aux tgt ( tactic.generalize v x >> target )
                      to_expr ` `( fun y : $ ( t ) => ∀ x , y = x → $ ( tgt' 0 1 ) )
                  )
                <|>
                to_expr ` `( fun y : $ ( t ) => ∀ x , $ ( v ) = x → $ ( tgt ) )
          let t ← head_beta ( tgt' v ) >>= assert h
          swap
          let r ← mk_eq_refl v
          solve1 <| tactic.exact ( t v r )
          Prod.mk <$> tactic.intro x <*> tactic.intro h
#align tactic.interactive.monotonicity.generalize' tactic.interactive.monotonicity.generalize'

private unsafe def hide_meta_vars (tac : List expr → tactic Unit) : tactic Unit :=
  focus1 do
    let tgt ← target >>= instantiate_mvars
    tactic.change tgt
    let ctx ← local_context
    let vs := tgt.list_meta_vars
    let vs' ←
      mapM
          (fun v => do
            let h ← get_unused_name `h
            let x ← get_unused_name `x
            Prod.snd <$> monotonicity.generalize' h v x)
          vs
    andthen (tac ctx) (vs' (try ∘ tactic.subst))
#align tactic.interactive.hide_meta_vars tactic.interactive.hide_meta_vars

unsafe def hide_meta_vars' (tac : itactic) : itactic :=
  hide_meta_vars fun _ => tac
#align tactic.interactive.hide_meta_vars' tactic.interactive.hide_meta_vars'

end Config

unsafe def solve_mvar (v : expr) (tac : tactic Unit) : tactic Unit := do
  let gs ← get_goals
  set_goals [v]
  target >>= instantiate_mvars >>= tactic.change
  tac
  done
  set_goals <| gs
#align tactic.interactive.solve_mvar tactic.interactive.solve_mvar

def List.minimumOn {α β} [LinearOrder β] (f : α → β) : List α → List α
  | [] => []
  | x :: xs =>
    Prod.snd <|
      xs.foldl
        (fun ⟨k, a⟩ b =>
          let k' := f b
          if k < k' then (k, a) else if k' < k then (k', [b]) else (k, b :: a))
        (f x, [x])
#align tactic.interactive.list.minimum_on Tactic.Interactive.List.minimumOn

open Format MonoSelection

unsafe def best_match {β} (xs : List expr) (tac : expr → tactic β) : tactic Unit := do
  let t ← target
  let xs ← xs.mmap fun x => try_core <| Prod.mk x <$> solve_aux t (tac x >> get_goals)
  let xs := xs.filterMap id
  let r := List.minimumOn (List.length ∘ Prod.fst ∘ Prod.snd) xs
  match r with
    | [(_, gs, pr)] => tactic.exact pr >> set_goals gs
    | [] => fail "no good match found"
    | _ => do
      let lmms ←
        r fun ⟨l, gs, _⟩ => do
            let ts ← gs infer_type
            let msg ← ts pp
            pure <| foldl compose "\n\n" <| List.intersperse "\n" <| to_fmt l :: msg
      let msg := foldl compose "" lmms
      fail
          f! "ambiguous match: {msg}
            
            Tip: try asserting a side condition to distinguish between the lemmas"
#align tactic.interactive.best_match tactic.interactive.best_match

unsafe def mono_aux (dir : parse side) : tactic Unit := do
  let t ← target >>= instantiate_mvars
  let ns ← get_monotonicity_lemmas t dir
  let asms ← local_context
  let rs ← find_lemma asms t ns
  focus1 <| () <$ best_match rs fun law => tactic.refine <| to_pexpr law
#align tactic.interactive.mono_aux tactic.interactive.mono_aux

/-- - `mono` applies a monotonicity rule.
- `mono*` applies monotonicity rules repetitively.
- `mono with x ≤ y` or `mono with [0 ≤ x,0 ≤ y]` creates an assertion for the listed
  propositions. Those help to select the right monotonicity rule.
- `mono left` or `mono right` is useful when proving strict orderings:
   for `x + y < w + z` could be broken down into either
    - left:  `x ≤ w` and `y < z` or
    - right: `x < w` and `y ≤ z`
- `mono using [rule1,rule2]` calls `simp [rule1,rule2]` before applying mono.
- The general syntax is
  `mono '*'? ('with' hyp | 'with' [hyp1,hyp2])? ('using' [hyp1,hyp2])? mono_cfg?`

To use it, first import `tactic.monotonicity`.

Here is an example of mono:

```lean
example (x y z k : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y) :
  (k + 3 + x) - y ≤ (k + 4 + x) - z :=
begin
  mono, -- unfold `(-)`, apply add_le_add
  { -- ⊢ k + 3 + x ≤ k + 4 + x
    mono, -- apply add_le_add, refl
    -- ⊢ k + 3 ≤ k + 4
    mono },
  { -- ⊢ -y ≤ -z
    mono /- apply neg_le_neg -/ }
end
```

More succinctly, we can prove the same goal as:

```lean
example (x y z k : ℤ)
  (h : 3 ≤ (4 : ℤ))
  (h' : z ≤ y) :
  (k + 3 + x) - y ≤ (k + 4 + x) - z :=
by mono*
```

-/
unsafe def mono (many : parse (tk "*")?) (dir : parse side)
    (hyps : parse <| tk "with" *> pexpr_list_or_texpr <|> pure [])
    (simp_rules : parse <| tk "using" *> simp_arg_list <|> pure []) : tactic Unit := do
  let hyps ← hyps.mmap fun p => to_expr p >>= mk_meta_var
  hyps fun pr => do
      let h ← get_unused_name `h
      note h none pr
  when (¬simp_rules) (simp_core { } failed tt simp_rules [] (loc.ns [none]) >> skip)
  if many then repeat <| mono_aux dir else mono_aux dir
  let gs ← get_goals
  set_goals <| hyps ++ gs
#align tactic.interactive.mono tactic.interactive.mono

add_tactic_doc
  { Name := "mono"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.mono]
    tags := ["monotonicity"] }

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `g -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
/-- transforms a goal of the form `f x ≼ f y` into `x ≤ y` using lemmas
marked as `monotonic`.

Special care is taken when `f` is the repeated application of an
associative operator and if the operator is commutative
-/
unsafe def ac_mono_aux (cfg : MonoCfg := { }) : tactic Unit :=
  hide_meta_vars fun asms => do
    try sorry
    let tgt ← target >>= instantiate_mvars
    let (l, r, id_rs, g) ← ac_monotonicity_goal cfg tgt <|> fail "monotonic context not found"
    let ns ← get_monotonicity_lemmas tgt both
    let p ← mk_pattern g
    let rules ← find_rule asms ns p <|> fail "no applicable rules found"
    when (rules = []) (fail "no applicable rules found")
    let err ← format.join <$> mapM side_conditions rules
    focus1 <|
        best_match rules fun rule => do
          let t₀ ← mk_meta_var q(Prop)
          let v₀ ← mk_meta_var t₀
          let t₁ ← mk_meta_var q(Prop)
          let v₁ ← mk_meta_var t₁
          tactic.refine <| ``(applyRel (g $(g.rel_def)) $(l) $(r) $(rule) $(v₀) $(v₁))
          solve_mvar v₀ (try (any_of id_rs rewrite_target) >> (done <|> refl <|> ac_refl <|> sorry))
          solve_mvar v₁ (try (any_of id_rs rewrite_target) >> (done <|> refl <|> ac_refl <|> sorry))
          let n ← num_goals
          iterate_exactly (n - 1)
              (try <| solve1 <| apply_instance <|> tactic.solve_by_elim { lemmas := some asms })
#align tactic.interactive.ac_mono_aux tactic.interactive.ac_mono_aux

open Sum Nat

/-- (repeat_until_or_at_most n t u): repeat tactic `t` at most n times or until u succeeds -/
unsafe def repeat_until_or_at_most : Nat → tactic Unit → tactic Unit → tactic Unit
  | 0, t, _ => fail "too many applications"
  | succ n, t, u => u <|> t >> repeat_until_or_at_most n t u
#align tactic.interactive.repeat_until_or_at_most tactic.interactive.repeat_until_or_at_most

unsafe def repeat_until : tactic Unit → tactic Unit → tactic Unit :=
  repeat_until_or_at_most 100000
#align tactic.interactive.repeat_until tactic.interactive.repeat_until

inductive RepArity : Type
  | one
  | exactly (n : ℕ)
  | many
  deriving _root_.has_reflect, Inhabited
#align tactic.interactive.rep_arity Tactic.Interactive.RepArity

unsafe def repeat_or_not : RepArity → tactic Unit → Option (tactic Unit) → tactic Unit
  | rep_arity.one, tac, none => tac
  | rep_arity.many, tac, none => repeat tac
  | rep_arity.exactly n, tac, none => iterate_exactly' n tac
  | rep_arity.one, tac, some until => tac >> until
  | rep_arity.many, tac, some until => repeat_until tac until
  | rep_arity.exactly n, tac, some until => iterate_exactly n tac >> until
#align tactic.interactive.repeat_or_not tactic.interactive.repeat_or_not

unsafe def assert_or_rule : lean.parser (Sum pexpr pexpr) :=
  tk ":=" *> inl <$> texpr <|> tk ":" *> inr <$> texpr
#align tactic.interactive.assert_or_rule tactic.interactive.assert_or_rule

unsafe def arity : lean.parser RepArity :=
  tk "*" *> pure RepArity.many <|> rep_arity.exactly <$> (tk "^" *> small_nat) <|> pure RepArity.one
#align tactic.interactive.arity tactic.interactive.arity

/-- `ac_mono` reduces the `f x ⊑ f y`, for some relation `⊑` and a
monotonic function `f` to `x ≺ y`.

`ac_mono*` unwraps monotonic functions until it can't.

`ac_mono^k`, for some literal number `k` applies monotonicity `k`
times.

`ac_mono := h`, with `h` a hypothesis, unwraps monotonic functions and
uses `h` to solve the remaining goal. Can be combined with `*` or `^k`:
`ac_mono* := h`

`ac_mono : p` asserts `p` and uses it to discharge the goal result
unwrapping a series of monotonic functions. Can be combined with * or
^k: `ac_mono* : p`

In the case where `f` is an associative or commutative operator,
`ac_mono` will consider any possible permutation of its arguments and
use the one the minimizes the difference between the left-hand side
and the right-hand side.

To use it, first import `tactic.monotonicity`.

`ac_mono` can be used as follows:

```lean
example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y) :
  (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
  ac_mono,
  -- ⊢ (m + x + n) * z ≤ z * (y + n + m)
  ac_mono,
  -- ⊢ m + x + n ≤ y + n + m
  ac_mono,
end
```

As with `mono*`, `ac_mono*` solves the goal in one go and so does
`ac_mono* := h₁`. The latter syntax becomes especially interesting in the
following example:

```lean
example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : m + x + n ≤ y + n + m) :
  (m + x + n) * z + k ≤ z * (y + n + m) + k :=
by ac_mono* := h₁.
```

By giving `ac_mono` the assumption `h₁`, we are asking `ac_refl` to
stop earlier than it would normally would.
-/
unsafe def ac_mono (rep : parse arity) : parse assert_or_rule ? → optParam MonoCfg { } → tactic Unit
  | none, opt => focus1 <| repeat_or_not rep (ac_mono_aux opt) none
  | some (inl h), opt => do
    focus1 <| repeat_or_not rep (ac_mono_aux opt) (some <| done <|> to_expr h >>= ac_refine)
  | some (inr t), opt => do
    let h ← i_to_expr t >>= assert `h
    tactic.swap
    focus1 <| repeat_or_not rep (ac_mono_aux opt) (some <| done <|> ac_refine h)
#align tactic.interactive.ac_mono tactic.interactive.ac_mono

/-
TODO(Simon): with `ac_mono := h` and `ac_mono : p` split the remaining
  gaol if the provided rule does not solve it completely.
-/
add_tactic_doc
  { Name := "ac_mono"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.ac_mono]
    tags := ["monotonicity"] }

attribute [mono] And.imp Or.imp

end Tactic.Interactive

