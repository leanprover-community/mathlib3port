import Mathbin.Tactic.Core

/-!
## #simp
A user command to run the simplifier.
-/


namespace Tactic

/-- Strip all annotations of non local constants in the passed `expr`. (This is required in an
incantation later on in order to make the C++ simplifier happy.) -/
private unsafe def strip_annotations_from_all_non_local_consts {elab : Bool} (e : expr elab) : expr elab :=
  expr.unsafe_cast <|
    e.unsafe_cast.replace fun e n =>
      match e.is_annotation with
      | some (_, expr.local_const _ _ _ _) => none
      | some (_, _) => e.erase_annotations
      | _ => none

/-- `simp_arg_type.to_pexpr` retrieves the `pexpr` underlying the given `simp_arg_type`, if there is
one. -/
unsafe def simp_arg_type.to_pexpr : simp_arg_type → Option pexpr
  | sat@(simp_arg_type.expr e) => e
  | sat@(simp_arg_type.symm_expr e) => e
  | sat => none

/-- Incantation which prepares a `pexpr` in a `simp_arg_type` for use by the simplifier after
`expr.replace_subexprs` as been called to replace some of its local variables. -/
private unsafe def replace_subexprs_for_simp_arg (e : pexpr) (rules : List (expr × expr)) : pexpr :=
  strip_annotations_from_all_non_local_consts <| pexpr.of_expr <| e.unsafe_cast.replace_subexprs rules

/-- `simp_arg_type.replace_subexprs` calls `expr.replace_subexprs` on the underlying `pexpr`, if
there is one, and then prepares the result for use by the simplifier. -/
unsafe def simp_arg_type.replace_subexprs : simp_arg_type → List (expr × expr) → simp_arg_type
  | simp_arg_type.expr e, rules => simp_arg_type.expr <| replace_subexprs_for_simp_arg e rules
  | simp_arg_type.symm_expr e, rules => simp_arg_type.symm_expr <| replace_subexprs_for_simp_arg e rules
  | sat, rules => sat

setup_tactic_parser

initialize
  registerTraceClass.1 `silence_simp_if_true

/-- The basic usage is `#simp e`, where `e` is an expression,
which will print the simplified form of `e`.

You can specify additional simp lemmas as usual for example using
`#simp [f, g] : e`, or `#simp with attr : e`.
(The colon is optional, but helpful for the parser.)

`#simp` understands local variables, so you can use them to
introduce parameters.
-/
@[user_command]
unsafe def simp_cmd (_ : parse <| tk "#simp") : lean.parser Unit := do
  let no_dflt ← only_flag
  let hs ← simp_arg_list
  let attr_names ← with_ident_list
  let o ← optionalₓ (tk ":")
  let e ← types.texpr
  let hs_es := List.join <| hs.map <| Option.toList ∘ simp_arg_type.to_pexpr
  let (ts, mappings) ← synthesize_tactic_state_with_variables_as_hyps (e :: hs_es)
  let simp_result ←
    lean.parser.of_tactic fun _ =>
        (do
            let e ← to_expr e
            let hs := hs.map fun sat => sat.replace_subexprs mappings
            Prod.fst <$> e {  } failed no_dflt attr_names hs)
          ts
  when (¬is_trace_enabled_for `silence_simp_if_true ∨ simp_result ≠ expr.const `true []) (trace simp_result)

add_tactic_doc
  { Name := "#simp", category := DocCategory.cmd, declNames := [`tactic.simp_cmd], tags := ["simplification"] }

end Tactic

