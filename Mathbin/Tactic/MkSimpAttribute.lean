/-
Copyright (c) 2019 Rob Lewis All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rob Lewis
-/
import Mathbin.Tactic.DocCommands

#align_import tactic.mk_simp_attribute from "leanprover-community/mathlib"@"48fb5b5280e7c81672afc9524185ae994553ebf4"

/-!
# User command to register `simp` attributes

In this file we define a command `mk_simp_attribute` that can be used to register `simp` sets.  We
also define all `simp` attributes that are used in the library and tag lemmas from Lean core with
these attributes.
-/


/-!
### User command
-/


section Cmd

open Interactive Lean Lean.Parser

namespace Tactic

/--
The command `mk_simp_attribute simp_name "description"` creates a simp set with name `simp_name`.
Lemmas tagged with `@[simp_name]` will be included when `simp with simp_name` is called.
`mk_simp_attribute simp_name none` will use a default description.

Appending the command with `with attr1 attr2 ...` will include all declarations tagged with
`attr1`, `attr2`, ... in the new simp set.

This command is preferred to using ``run_cmd mk_simp_attr `simp_name`` since it adds a doc string
to the attribute that is defined. If you need to create a simp set in a file where this command is
not available, you should use
```lean
run_cmd mk_simp_attr `simp_name
run_cmd add_doc_string `simp_attr.simp_name "Description of the simp set here"
```
-/
@[user_command]
unsafe def mk_simp_attribute_cmd (_ : parse <| tk "mk_simp_attribute") : lean.parser Unit := do
  let n ← ident
  let d ← parser.pexpr
  let d ← to_expr ``(($(d) : Option String))
  let descr ← eval_expr (Option String) d
  let with_list ← tk "with" *> many ident <|> return []
  mk_simp_attr n with_list
  add_doc_string (name.append `simp_attr n) <| descr <| "simp set for " ++ toString n
#align tactic.mk_simp_attribute_cmd tactic.mk_simp_attribute_cmd

add_tactic_doc
  { Name := "mk_simp_attribute"
    category := DocCategory.cmd
    declNames := [`tactic.mk_simp_attribute_cmd]
    tags := ["simplification"] }

end Tactic

end Cmd

/-!
### Attributes
-/


-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/--
    The simpset `equiv_rw_simp` is used by the tactic `equiv_rw` to
    simplify applications of equivalences and their inverses. -/
  register_simp_attr
  equiv_rw_simp

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/--
    The simpset `field_simps` is used by the tactic `field_simp` to
    reduce an expression in a field to an expression of the form `n / d` where `n` and `d` are
    division-free. -/
  register_simp_attr
  field_simps

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- Simp set for functor_norm -/ register_simp_attr functor_norm

attribute [functor_norm] bind_assoc pure_bind bind_pure

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- Simplification rules for ghost equations -/ register_simp_attr ghost_simps

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- Simp set for integral rules. -/ register_simp_attr integral_simps

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- Simp attribute for lemmas about `is_R_or_C` -/ register_simp_attr is_R_or_C_simps

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/--
    The simpset `mfld_simps` records several simp lemmas that are
    especially useful in manifolds. It is a subset of the whole set of simp lemmas, but it makes it
    possible to have quicker proofs (when used with `squeeze_simp` or `simp only`) while retaining
    readability.
    
    The typical use case is the following, in a file on manifolds:
    If `simp [foo, bar]` is slow, replace it with `squeeze_simp [foo, bar] with mfld_simps` and paste
    its output. The list of lemmas should be reasonable (contrary to the output of
    `squeeze_simp [foo, bar]` which might contain tens of lemmas), and the outcome should be quick
    enough.
     -/
  register_simp_attr
  mfld_simps

attribute [mfld_simps] id.def Function.comp.left_id Set.mem_setOf_eq and_true_iff true_and_iff
  Function.comp_apply and_self_iff eq_self_iff_true Function.comp.right_id not_false_iff true_or_iff
  or_true_iff

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:61:9: unsupported: weird string -/
-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:61:9: unsupported: weird string -/
  register_simp_attr
  monad_norm

/- [mathport] port note: move this to another file, it won't work here -/
attribute [monad_norm] functor_norm

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- Simp lemmas for `nontriviality` tactic -/ register_simp_attr nontriviality

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- Simp attribute for lemmas about `even` -/ register_simp_attr parity_simps

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/--
    The `push_cast` simp attribute uses `norm_cast` lemmas
    to move casts toward the leaf nodes of the expression. -/
  register_simp_attr
  push_cast

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- Simp set for if-then-else statements, used in the `split_ifs` tactic -/
  register_simp_attr
  split_if_reduction

attribute [split_if_reduction] if_pos if_neg dif_pos dif_neg if_congr

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/--
    The simpset `transport_simps` is used by the tactic `transport`
    to simplify certain expressions involving application of equivalences,
    and trivial `eq.rec` or `ep.mpr` conversions.
    It's probably best not to adjust it without understanding the algorithm used by `transport`. -/
  register_simp_attr
  transport_simps

attribute [transport_simps] cast_eq

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
/-- simp set for the manipulation of typevec and arrow expressions -/ register_simp_attr typevec

