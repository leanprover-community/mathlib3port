import Mathbin.Tactic.Chain 
import Mathbin.Data.Quot

namespace Tactic

/-- Auxiliary tactic for `trunc_cases`. -/
private unsafe def trunc_cases_subsingleton (e : expr) (ids : List Name) : tactic expr :=
  do 
    let [(_, [e], _)] ← tactic.induction e ids `trunc.rec_on_subsingleton 
    return e

/-- Auxiliary tactic for `trunc_cases`. -/
private unsafe def trunc_cases_nondependent (e : expr) (ids : List Name) : tactic expr :=
  do 
    to_expr (pquote.1 (Trunc.liftOn (%%ₓe))) >>= tactic.fapply 
    tactic.clear e 
    let e ← tactic.intro e.local_pp_name 
    tactic.swap 
    match ids.nth 1 with 
      | some n => tactic.intro n
      | none => tactic.intro1 
    match ids.nth 2 with 
      | some n => tactic.intro n
      | none => tactic.intro1 
    tactic.swap 
    return e

-- ././Mathport/Syntax/Translate/Basic.lean:686:4: warning: unsupported (TODO): `[tacs]
/-- Auxiliary tactic for `trunc_cases`. -/
private unsafe def trunc_cases_dependent (e : expr) (ids : List Name) : tactic expr :=
  do 
    let [(_, [e], _), (_, [e_a, e_b, e_p], _)] ← tactic.induction e ids 
    swap 
    tactic.cases e_p >> sorry 
    swap 
    return e

namespace Interactive

setup_tactic_parser

/--
`trunc_cases e` performs case analysis on a `trunc` expression `e`,
attempting the following strategies:
1. when the goal is a subsingleton, calling `induction e using trunc.rec_on_subsingleton`,
2. when the goal does not depend on `e`, calling `fapply trunc.lift_on e`,
   and using `intro` and `clear` afterwards to make the goals look like we used `induction`,
3. otherwise, falling through to `trunc.rec_on`, and in the new invariance goal
   calling `cases h_p` on the useless `h_p : true` hypothesis,
   and then attempting to simplify the `eq.rec`.

`trunc_cases e with h` names the new hypothesis `h`.
If `e` is a local hypothesis already,
`trunc_cases` defaults to reusing the same name.

`trunc_cases e with h h_a h_b` will use the names `h_a` and `h_b` for the new hypothesis
in the invariance goal if `trunc_cases` uses `trunc.lift_on` or `trunc.rec_on`.

Finally, if the new hypothesis from inside the `trunc` is a type class,
`trunc_cases` resets the instance cache so that it is immediately available.
-/
unsafe def trunc_cases (e : parse texpr) (ids : parse with_ident_list) : tactic Unit :=
  do 
    let e ← to_expr e 
    let ids := if ids = [] ∧ e.is_local_constant then [e.local_pp_name] else ids 
    let e ←
      if e.is_local_constant then return e else
          do 
            let n ←
              match ids.nth 0 with 
                | some n => pure n
                | none => mk_fresh_name 
            note n none e 
    let tgt ← target 
    let ss ← succeeds (mk_app `subsingleton [tgt] >>= mk_instance)
    let e ←
      if ss then trunc_cases_subsingleton e ids else
          if e.occurs tgt then trunc_cases_dependent e ids else trunc_cases_nondependent e ids 
    let c ← infer_type e >>= is_class 
    when c reset_instance_cache

end Interactive

end Tactic

add_tactic_doc
  { Name := "trunc_cases", category := DocCategory.tactic, declNames := [`tactic.interactive.trunc_cases],
    tags := ["case bashing"] }

