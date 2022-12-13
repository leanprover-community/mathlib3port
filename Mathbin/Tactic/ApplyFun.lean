/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek, Patrick Massot
-/
import Mathbin.Tactic.Monotonicity.Default

namespace Tactic

/- ./././Mathport/Syntax/Translate/Expr.lean:333:4: warning: unsupported (TODO): `[tacs] -/
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Apply the function `f` given by `e : pexpr` to the local hypothesis `hyp`, which must either be
      of the form `a = b` or `a ≤ b`, replacing the type of `hyp` with `f a = f b` or `f a ≤ f b`. If
      `hyp` names an inequality then a new goal `monotone f` is created, unless the name of a proof of
      this fact is passed as the optional argument `mono_lem`, or the `mono` tactic can prove it.
      -/
    unsafe
  def
    apply_fun_to_hyp
    ( e : pexpr ) ( mono_lem : Option pexpr ) ( hyp : expr ) : tactic Unit
    :=
      do
        let t ← infer_type hyp >>= instantiate_mvars
          let
            prf
              ←
              match
                t
                with
                |
                    q( $ ( l ) = $ ( r ) )
                    =>
                    do
                      let ltp ← infer_type l
                        let mv ← mk_mvar
                        to_expr ` `( congr_arg ( $ ( e ) : $ ( ltp ) → $ ( mv ) ) $ ( hyp ) )
                  |
                    q( $ ( l ) ≤ $ ( r ) )
                    =>
                    do
                      let
                          Hmono
                            ←
                            match
                              mono_lem
                              with
                              | some mono_lem => tactic.i_to_expr mono_lem
                                |
                                  none
                                  =>
                                  do
                                    let n ← get_unused_name `mono
                                      to_expr ` `( Monotone $ ( e ) ) >>= assert n
                                      swap
                                      let n ← get_local n
                                      to_expr ` `( $ ( n ) $ ( hyp ) )
                                      swap
                                      ( do intro_lst [ `x , `y , `h ] sorry ) <|> swap
                                      return n
                        to_expr ` `( $ ( Hmono ) $ ( hyp ) )
                  | _ => throwError "failed to apply { ( ← e ) } at { ← hyp }"
          clear hyp
          let hyp ← note hyp . local_pp_name none prf
          try <| tactic.dsimp_hyp hyp simp_lemmas.mk [ ] { eta := False beta := True }
#align tactic.apply_fun_to_hyp tactic.apply_fun_to_hyp

-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Attempt to "apply" a function `f` represented by the argument `e : pexpr` to the goal.
      
      If the goal is of the form `a ≠ b`, we obtain the new goal `f a ≠ f b`.
      If the goal is of the form `a = b`, we obtain a new goal `f a = f b`, and a subsidiary goal
      `injective f`.
      (We attempt to discharge this subsidiary goal automatically, or using the optional argument.)
      If the goal is of the form `a ≤ b` (or similarly for `a < b`), and `f` is an `order_iso`,
      we obtain a new goal `f a ≤ f b`.
      -/
    unsafe
  def
    apply_fun_to_goal
    ( e : pexpr ) ( lem : Option pexpr ) : tactic Unit
    :=
      do
        let t ← target
          match
            t
            with
            | q( $ ( l ) ≠ $ ( r ) ) => ( to_expr ` `( ne_of_apply_ne $ ( e ) ) >>= apply ) >> skip
              |
                q( ¬ $ ( l ) = $ ( r ) )
                =>
                ( to_expr ` `( ne_of_apply_ne $ ( e ) ) >>= apply ) >> skip
              |
                q( $ ( l ) ≤ $ ( r ) )
                =>
                ( to_expr ` `( ( OrderIso.le_iff_le $ ( e ) ) . mp ) >>= apply ) >> skip
              |
                q( $ ( l ) < $ ( r ) )
                =>
                ( to_expr ` `( ( OrderIso.lt_iff_lt $ ( e ) ) . mp ) >>= apply ) >> skip
              |
                q( $ ( l ) = $ ( r ) )
                =>
                focus1
                  do
                    to_expr ` `( $ ( e ) $ ( l ) )
                      let n ← get_unused_name `inj
                      to_expr ` `( Function.Injective $ ( e ) ) >>= assert n
                      (
                          focus1
                            <|
                            assumption
                              <|>
                              ( to_expr ` `( Equiv.injective ) >>= apply ) >> done
                                <|>
                                ( lem fun l => to_expr l >>= apply ) >> done
                          )
                        <|>
                        swap
                      let n ← get_local n
                      apply n
                      clear n
              | _ => throwError "failed to apply { ← e } to the goal"
#align tactic.apply_fun_to_goal tactic.apply_fun_to_goal

namespace Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/-- Apply a function to an equality or inequality in either a local hypothesis or the goal.

* If we have `h : a = b`, then `apply_fun f at h` will replace this with `h : f a = f b`.
* If we have `h : a ≤ b`, then `apply_fun f at h` will replace this with `h : f a ≤ f b`,
  and create a subsidiary goal `monotone f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using `mono`,
  or an explicit solution can be provided with `apply_fun f at h using P`, where `P : monotone f`.
* If the goal is `a ≠ b`, `apply_fun f` will replace this with `f a ≠ f b`.
* If the goal is `a = b`, `apply_fun f` will replace this with `f a = f b`,
  and create a subsidiary goal `injective f`.
  `apply_fun` will automatically attempt to discharge this subsidiary goal using local hypotheses,
  or if `f` is actually an `equiv`,
  or an explicit solution can be provided with `apply_fun f using P`, where `P : injective f`.
* If the goal is `a ≤ b` (or similarly for `a < b`), and `f` is actually an `order_iso`,
  `apply_fun f` will replace the goal with `f a ≤ f b`.
  If `f` is anything else (e.g. just a function, or an `equiv`), `apply_fun` will fail.


Typical usage is:
```lean
open function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : injective $ g ∘ f) :
  injective f :=
begin
  intros x x' h,
  apply_fun g at h,
  exact H h
end
```
 -/
unsafe def apply_fun (q : parse texpr) (locs : parse location)
    (lem : parse (tk "using" *> texpr)?) : tactic Unit :=
  locs.apply (apply_fun_to_hyp q lem) (apply_fun_to_goal q lem)
#align tactic.interactive.apply_fun tactic.interactive.apply_fun

add_tactic_doc
  { Name := "apply_fun"
    category := DocCategory.tactic
    declNames := [`tactic.interactive.apply_fun]
    tags := ["context management"] }

end Interactive

end Tactic

