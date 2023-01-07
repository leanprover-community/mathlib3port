/-
Copyright (c) 2019 Rob Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Lewis

! This file was ported from Lean 3 source module tactic.delta_instance
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.SimpResult

namespace Tactic

-- We call `dsimp_result` here because otherwise
-- `delta_target` will insert an `id` in the result.
-- See the note [locally reducible category instances]
-- https://github.com/leanprover-community/mathlib/blob/c9fca15420e2ad443707ace831679fd1762580fe/src/algebra/category/Mon/basic.lean#L27
-- for an example where this used to cause a problem.
/-- `delta_instance ids` tries to solve the goal by calling `apply_instance`,
first unfolding the definitions in `ids`.
-/
unsafe def delta_instance (ids : List Name) : tactic Unit :=
  dsimp_result ((((intros >> reset_instance_cache) >> delta_target ids) >> apply_instance) >> done)
#align tactic.delta_instance tactic.delta_instance

namespace Interactive

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/- ./././Mathport/Syntax/Translate/Expr.lean:207:4: warning: unsupported notation `parser.many -/
/-- `delta_instance id₁ id₂ ...` tries to solve the goal by calling `apply_instance`,
first unfolding the definitions in `idᵢ`.
-/
unsafe def delta_instance (ids : parse (parser.many ident)) : itactic :=
  tactic.delta_instance ids
#align tactic.interactive.delta_instance tactic.interactive.delta_instance

end Interactive

/-- Guess a name for an instance from its expression.

This is a poor-man's version of the C++ `heuristic_inst_name`, and tries much less hard to pick a
good name. -/
unsafe def delta_instance_name : pexpr → String
  | expr.app f _ => delta_instance_name f
  | expr.pi _ _ _ body => delta_instance_name body
  | expr.lam _ _ _ body => delta_instance_name body
  | expr.const nm _ => nm.last
  | _ => "inst"
#align tactic.delta_instance_name tactic.delta_instance_name

/--
Tries to derive instances by unfolding the newly introduced type and applying type class resolution.

For example,
```lean
@[derive ring] def new_int : Type := ℤ
```
adds an instance `ring new_int`, defined to be the instance of `ring ℤ` found by `apply_instance`.

Multiple instances can be added with `@[derive [ring, module ℝ]]`.

This derive handler applies only to declarations made using `def`, and will fail on such a
declaration if it is unable to derive an instance. It is run with higher priority than the built-in
handlers, which will fail on `def`s.
-/
@[derive_handler]
unsafe def delta_instance_handler : derive_handler := fun cls new_decl_name => do
  let env ← get_env
  if env new_decl_name then return ff
    else do
      let new_decl ← get_decl new_decl_name
      let new_decl_pexpr ← resolve_name new_decl_name
      let arity ← get_pexpr_arg_arity_with_tgt cls new_decl
      let tgt ← to_expr <| apply_under_n_pis cls new_decl_pexpr new_decl (new_decl - arity)
      let (vs, tgt') ← open_pis tgt
      let tgt ← whnf tgt' transparency.none >>= pis vs
      let (_, inst) ← solve_aux tgt <| tactic.delta_instance [new_decl_name]
      let inst ← instantiate_mvars inst
      let inst ← replace_univ_metas_with_univ_params inst
      let tgt ← instantiate_mvars tgt
      let nm ← get_unused_decl_name <| .str new_decl_name (delta_instance_name cls)
      add_protected_decl <| declaration.defn nm inst tgt inst new_decl new_decl
      set_basic_attribute `instance nm tt
      return tt
#align tactic.delta_instance_handler tactic.delta_instance_handler

end Tactic

