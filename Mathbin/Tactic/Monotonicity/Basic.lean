import Mathbin.Order.BoundedOrder

namespace Tactic.Interactive

open Tactic List

open Lean Lean.Parser Interactive

open Interactive.Types

-- error in Tactic.Monotonicity.Basic: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler inhabited
@[derive #[expr inhabited]] structure mono_cfg := (unify := ff)

-- error in Tactic.Monotonicity.Basic: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler decidable_eq
@[derive #["[", expr decidable_eq, ",", expr has_reflect, ",", expr inhabited, "]"]] inductive mono_selection : Type
| left : mono_selection
| right : mono_selection
| both : mono_selection

initialize 
  registerTraceClass.1 `mono.relation

section Compare

parameter (opt : mono_cfg)

unsafe def compare (e₀ e₁ : expr) : tactic Unit :=
  do 
    if opt.unify then
        do 
          guardₓ (¬e₀.is_mvar ∧ ¬e₁.is_mvar)
          unify e₀ e₁
      else is_def_eq e₀ e₁

unsafe def find_one_difference : List expr → List expr → tactic (List expr × expr × expr × List expr)
| x :: xs, y :: ys =>
  do 
    let c ← try_core (compare x y)
    if c.is_some then Prod.mapₓ (cons x) id <$> find_one_difference xs ys else
        do 
          guardₓ (xs.length = ys.length)
          mzipWith' compare xs ys 
          return ([], x, y, xs)
| xs, ys => fail f! "find_one_difference: {xs }, {ys}"

end Compare

def last_two {α : Type _} (l : List α) : Option (α × α) :=
  match l.reverse with 
  | x₁ :: x₀ :: _ => some (x₀, x₁)
  | _ => none

unsafe def match_imp : expr → tactic (expr × expr)
| quote.1 ((%%ₓe₀) → %%ₓe₁) =>
  do 
    guardₓ ¬e₁.has_var 
    return (e₀, e₁)
| _ => failed

open Expr

unsafe def same_operator : expr → expr → Bool
| app e₀ _, app e₁ _ =>
  let fn₀ := e₀.get_app_fn 
  let fn₁ := e₁.get_app_fn 
  fn₀.is_constant ∧ fn₀.const_name = fn₁.const_name
| pi _ _ _ _, pi _ _ _ _ => tt
| _, _ => ff

unsafe def get_operator (e : expr) : Option Name :=
  (guardₓ ¬e.is_pi) >> pure e.get_app_fn.const_name

unsafe def monotonicity.check_rel (l r : expr) : tactic (Option Name) :=
  do 
    guardₓ (same_operator l r) <|>
        do 
          fail f! "{l } and {r } should be the f x and f y for some f"
    if l.is_pi then pure none else pure r.get_app_fn.const_name

@[reducible]
def mono_key :=
  WithBot Name × WithBot Name

unsafe instance mono_key.has_lt : LT mono_key :=
  { lt := Prod.Lex (· < ·) (· < ·) }

open Nat

unsafe def mono_head_candidates : ℕ → List expr → expr → tactic mono_key
| 0, _, h => throwError "Cannot find relation in { ← h}"
| succ n, xs, h =>
  (do 
      let (rel, l, r) ←
        if h.is_arrow then pure (none, h.binding_domain, h.binding_body) else
            guardₓ h.get_app_fn.is_constant >> Prod.mk (some h.get_app_fn.const_name) <$> last_two h.get_app_args 
      Prod.mk <$> monotonicity.check_rel l r <*> pure rel) <|>
    match xs with 
    | [] => fail f! "oh? {h}"
    | x :: xs => mono_head_candidates n xs (h.pis [x])

unsafe def monotonicity.check (lm_n : Name) : tactic mono_key :=
  do 
    let lm ← mk_const lm_n 
    let lm_t ← infer_type lm >>= instantiate_mvars 
    when_tracing `mono.relation
        ( ←
          do 
            dbg_trace "[mono] Looking for relation in { ← lm_t}")
    let s := simp_lemmas.mk 
    let s ← s.add_simp `` Monotone 
    let s ← s.add_simp `` StrictMono 
    let lm_t ← s.dsimplify [] lm_t { failIfUnchanged := ff }
    when_tracing `mono.relation
        ( ←
          do 
            dbg_trace "[mono] Looking for relation in { ← lm_t} (after unfolding)")
    let (xs, h) ← open_pis lm_t 
    mono_head_candidates 3 xs.reverse h

unsafe instance  : has_to_format mono_selection :=
  ⟨fun x =>
      match x with 
      | mono_selection.left => "left"
      | mono_selection.right => "right"
      | mono_selection.both => "both"⟩

unsafe def side : lean.parser mono_selection :=
  with_desc "expecting 'left', 'right' or 'both' (default)"$
    do 
      let some n ← optionalₓ ident | pure mono_selection.both 
      if n = `left then pure$ mono_selection.left else
          if n = `right then pure$ mono_selection.right else
            if n = `both then pure$ mono_selection.both else
              fail f! "invalid argument: {n}, expecting 'left', 'right' or 'both' (default)"

open Function

@[user_attribute]
unsafe def monotonicity.attr : user_attribute (native.rb_lmap mono_key Name) (Option mono_key × mono_selection) :=
  { Name := `mono, descr := "monotonicity of function `f` wrt relations `R₀` and `R₁`: R₀ x y → R₁ (f x) (f y)",
    cache_cfg :=
      { dependencies := [],
        mk_cache :=
          fun ls =>
            do 
              let ps ← ls.mmap monotonicity.attr.get_param 
              let ps := ps.filter_map Prod.fst 
              pure$ (ps.zip ls).foldl (flip$ uncurry fun k n m => m.insert k n) (native.rb_lmap.mk mono_key _) },
    after_set :=
      some$
        fun n prio p =>
          do 
            let (none, v) ← monotonicity.attr.get_param n | pure ()
            let k ← monotonicity.check n 
            monotonicity.attr.set n (some k, v) p,
    Parser := Prod.mk none <$> side }

unsafe def filter_instances (e : mono_selection) (ns : List Name) : tactic (List Name) :=
  ns.mfilter$
    fun n =>
      do 
        let d ← user_attribute.get_param_untyped monotonicity.attr n 
        let (_, d) ← to_expr (pquote.1 (id (%%ₓd))) >>= eval_expr (Option mono_key × mono_selection)
        return (e = d : Bool)

unsafe def get_monotonicity_lemmas (k : expr) (e : mono_selection) : tactic (List Name) :=
  do 
    let ns ← monotonicity.attr.get_cache 
    let k' ←
      if k.is_pi then pure (get_operator k.binding_domain, none) else
          do 
            let (x₀, x₁) ← last_two k.get_app_args 
            pure (get_operator x₀, some k.get_app_fn.const_name)
    let ns := ns.find_def [] k' 
    let ns' ← filter_instances e ns 
    if e ≠ mono_selection.both then (· ++ ·) ns' <$> filter_instances mono_selection.both ns else pure ns'

end Tactic.Interactive

