import Mathbin.Tactic.SimpResult 
import Mathbin.Tactic.Clear 
import Mathbin.Control.EquivFunctor.Instances

/-!
# The `equiv_rw` tactic transports goals or hypotheses along equivalences.

The basic syntax is `equiv_rw e`, where `e : α ≃ β` is an equivalence.
This will try to replace occurrences of `α` in the goal with `β`, for example
transforming
* `⊢ α` to `⊢ β`,
* `⊢ option α` to `⊢ option β`
* `⊢ {a // P}` to `{b // P (⇑(equiv.symm e) b)}`

The tactic can also be used to rewrite hypotheses, using the syntax `equiv_rw e at h`.

## Implementation details

The main internal function is `equiv_rw_type e t`,
which attempts to turn an expression `e : α ≃ β` into a new equivalence with left hand side `t`.
As an example, with `t = option α`, it will generate `functor.map_equiv option e`.

This is achieved by generating a new synthetic goal `%%t ≃ _`,
and calling `solve_by_elim` with an appropriate set of congruence lemmas.
To avoid having to specify the relevant congruence lemmas by hand,
we mostly rely on `equiv_functor.map_equiv` and `bifunctor.map_equiv`
along with some structural congruence lemmas such as
* `equiv.arrow_congr'`,
* `equiv.subtype_equiv_of_subtype'`,
* `equiv.sigma_congr_left'`, and
* `equiv.Pi_congr_left'`.

The main `equiv_rw` function, when operating on the goal, simply generates a new equivalence `e'`
with left hand side matching the target, and calls `apply e'.inv_fun`.

When operating on a hypothesis `x : α`, we introduce a new fact `h : x = e.symm (e x)`, revert this,
and then attempt to `generalize`, replacing all occurrences of `e x` with a new constant `y`, before
`intro`ing and `subst`ing `h`, and renaming `y` back to `x`.

## Future improvements
In a future PR I anticipate that `derive equiv_functor` should work on many examples,
(internally using `transport`, which is in turn based on `equiv_rw`)
and we can incrementally bootstrap the strength of `equiv_rw`.

An ambitious project might be to add `equiv_rw!`,
a tactic which, when failing to find appropriate `equiv_functor` instances,
attempts to `derive` them on the spot.

For now `equiv_rw` is entirely based on `equiv`,
but the framework can readily be generalised to also work with other types of equivalences,
for example specific notations such as ring equivalence (`≃+*`),
or general categorical isomorphisms (`≅`).

This will allow us to transport across more general types of equivalences,
but this will wait for another subsequent PR.
-/


namespace Tactic

/-- A list of lemmas used for constructing congruence equivalences. -/
unsafe def equiv_congr_lemmas : List (tactic expr) :=
  [`equiv.of_iff, `equiv.equiv_congr, `equiv.arrow_congr', `equiv.subtype_equiv_of_subtype', `equiv.sigma_congr_left',
        `equiv.forall₃_congr', `equiv.forall₂_congr', `equiv.forall_congr', `equiv.Pi_congr_left', `bifunctor.map_equiv,
        `equiv_functor.map_equiv, `equiv.refl, `iff.refl].map
    fun n => mk_const n

initialize 
  registerTraceClass.1 `equiv_rw_type

/--
Configuration structure for `equiv_rw`.

* `max_depth` bounds the search depth for equivalences to rewrite along.
  The default value is 10.
  (e.g., if you're rewriting along `e : α ≃ β`, and `max_depth := 2`,
  you can rewrite `option (option α))` but not `option (option (option α))`.
-/
unsafe structure equiv_rw_cfg where 
  max_depth : ℕ := 10

/--
Implementation of `equiv_rw_type`, using `solve_by_elim`.
Expects a goal of the form `t ≃ _`,
and tries to solve it using `eq : α ≃ β` and congruence lemmas.
-/
unsafe def equiv_rw_type_core (eq : expr) (cfg : equiv_rw_cfg) : tactic Unit :=
  do 
    solve_by_elim
        { use_symmetry := False, use_exfalso := False, lemma_thunks := some (pure Eq :: equiv_congr_lemmas),
          ctx_thunk := pure [], max_depth := cfg.max_depth, pre_apply := tactic.intros >> skip,
          backtrack_all_goals := tt,
          discharger :=
            sorry >> sorry >> (sorry <|> sorry) <|>
              trace_if_enabled `equiv_rw_type "Failed, no congruence lemma applied!" >> failed,
          accept :=
            fun goals =>
              lock_tactic_state
                do 
                  when_tracing `equiv_rw_type
                      do 
                        goals.mmap pp >>= fun goals => trace f! "So far, we've built: {goals }"
                  done <|>
                      when_tracing `equiv_rw_type
                        do 
                          let gs ← get_goals 
                          let gs ← gs.mmap fun g => infer_type g >>= pp 
                          trace f! "Attempting to adapt to {gs}" }

/--
`equiv_rw_type e t` rewrites the type `t` using the equivalence `e : α ≃ β`,
returning a new equivalence `t ≃ t'`.
-/
unsafe def equiv_rw_type (eqv : expr) (ty : expr) (cfg : equiv_rw_cfg) : tactic expr :=
  do 
    when_tracing `equiv_rw_type
        do 
          let ty_pp ← pp ty 
          let eqv_pp ← pp eqv 
          let eqv_ty_pp ← infer_type eqv >>= pp 
          trace f! "Attempting to rewrite the type `{ty_pp }` using `{eqv_pp } : {eqv_ty_pp }`."
    let quote _ ≃ _ ← infer_type eqv | fail f! "{eqv } must be an `equiv`"
    let equiv_ty ← to_expr (pquote (%%ty) ≃ _)
    let new_eqv ← Prod.snd <$> (solve_aux equiv_ty$ equiv_rw_type_core eqv cfg)
    let new_eqv ← instantiate_mvars new_eqv 
    kdepends_on new_eqv eqv >>= guardb <|>
        do 
          let eqv_pp ← pp eqv 
          let ty_pp ← pp ty 
          fail f! "Could not construct an equivalence from {eqv_pp } of the form: {ty_pp } ≃ _"
    Prod.fst <$> new_eqv.simp { failIfUnchanged := ff }

mk_simp_attribute equiv_rw_simp :=
  "The simpset `equiv_rw_simp` is used by the tactic `equiv_rw` to\nsimplify applications of equivalences and their inverses."

attribute [equiv_rw_simp] Equiv.symm_symm Equiv.apply_symm_apply Equiv.symm_apply_apply

/--
Attempt to replace the hypothesis with name `x`
by transporting it along the equivalence in `e : α ≃ β`.
-/
unsafe def equiv_rw_hyp (x : Name) (e : expr) (cfg : equiv_rw_cfg := {  }) : tactic Unit :=
  dsimp_result
    (do 
      let x' ← get_local x 
      let x_ty ← infer_type x' 
      let e ← equiv_rw_type e x_ty cfg 
      let eq ← to_expr (pquote (%%x') = Equiv.symm (%%e) (Equiv.toFun (%%e) (%%x')))
      let prf ← to_expr (pquote (Equiv.symm_apply_apply (%%e) (%%x')).symm)
      let h ← note_anon Eq prf 
      revert h 
      let ex ← to_expr (pquote Equiv.toFun (%%e) (%%x'))
      generalize ex
          (by 
            inferOptParam)
          transparency.none 
      intro x 
      let h ← intro1 
      let b ← target >>= is_prop 
      if b then
          do 
            subst h 
            sorry
        else
          unfreezing_hyp x' (clear' tt [x']) <|>
            fail f! "equiv_rw expected to be able to clear the original hypothesis {x }, but couldn't."
      skip)
    { failIfUnchanged := ff } tt

/-- Rewrite the goal using an equiv `e`. -/
unsafe def equiv_rw_target (e : expr) (cfg : equiv_rw_cfg := {  }) : tactic Unit :=
  do 
    let t ← target 
    let e ← equiv_rw_type e t cfg 
    let s ← to_expr (pquote Equiv.invFun (%%e))
    tactic.eapply s 
    skip

end Tactic

namespace Tactic.Interactive

open Lean.Parser

open Interactive Interactive.Types

open Tactic

local postfix:9001 "?" => optionalₓ

/--
`equiv_rw e at h`, where `h : α` is a hypothesis, and `e : α ≃ β`,
will attempt to transport `h` along `e`, producing a new hypothesis `h : β`,
with all occurrences of `h` in other hypotheses and the goal replaced with `e.symm h`.

`equiv_rw e` will attempt to transport the goal along an equivalence `e : α ≃ β`.
In its minimal form it replaces the goal `⊢ α` with `⊢ β` by calling `apply e.inv_fun`.

`equiv_rw` will also try rewriting under (equiv_)functors, so can turn
a hypothesis `h : list α` into `h : list β` or
a goal `⊢ unique α` into `⊢ unique β`.

The maximum search depth for rewriting in subexpressions is controlled by
`equiv_rw e {max_depth := n}`.
-/
unsafe def equiv_rw (e : parse texpr) (loc : parse$ (tk "at" *> ident)?) (cfg : equiv_rw_cfg := {  }) : itactic :=
  do 
    let e ← to_expr e 
    match loc with 
      | some hyp => equiv_rw_hyp hyp e cfg
      | none => equiv_rw_target e cfg

add_tactic_doc
  { Name := "equiv_rw", category := DocCategory.tactic, declNames := [`tactic.interactive.equiv_rw],
    tags := ["rewriting", "equiv", "transport"] }

/--
Solve a goal of the form `t ≃ _`,
by constructing an equivalence from `e : α ≃ β`.
This is the same equivalence that `equiv_rw` would use to rewrite a term of type `t`.

A typical usage might be:
```
have e' : option α ≃ option β := by equiv_rw_type e
```
-/
unsafe def equiv_rw_type (e : parse texpr) (cfg : equiv_rw_cfg := {  }) : itactic :=
  do 
    let quote (%%t) ≃ _ ← target | fail "`equiv_rw_type` solves goals of the form `t ≃ _`."
    let e ← to_expr e 
    tactic.equiv_rw_type e t cfg >>= tactic.exact

add_tactic_doc
  { Name := "equiv_rw_type", category := DocCategory.tactic, declNames := [`tactic.interactive.equiv_rw_type],
    tags := ["rewriting", "equiv", "transport"] }

end Tactic.Interactive

