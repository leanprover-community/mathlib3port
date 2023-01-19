/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

! This file was ported from Lean 3 source module tactic.with_local_reducibility
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Core

/-!
# `with_local_reducibility`

Run a tactic in an environment with a temporarily modified reducibility attribute
for a specified declaration.
-/


namespace Tactic

/-- Possible reducibility attributes for a declaration:
reducible, semireducible (the default), irreducible. -/
inductive DeclReducibility
  | reducible
  | semireducible
  | Irreducible
  deriving DecidableEq
#align tactic.decl_reducibility Tactic.DeclReducibility

/-- Satisfy the inhabited linter -/
instance : Inhabited DeclReducibility :=
  ⟨DeclReducibility.semireducible⟩

/-- Get the reducibility attribute of a declaration.
Fails if the name does not refer to an existing declaration. -/
unsafe def get_decl_reducibility (n : Name) : tactic DeclReducibility := do
  let is_irred ← has_attribute' `irreducible n
  if is_irred then pure decl_reducibility.irreducible
    else do
      let is_red ← has_attribute' `reducible n
      if is_red then pure decl_reducibility.reducible
        else do
          let e ← get_env
          if e n then pure decl_reducibility.semireducible
            else fail f! "get_decl_reducibility: no declaration {n}"
#align tactic.get_decl_reducibility tactic.get_decl_reducibility

/-- Return the attribute (as a `name`) corresponding to a reducibility level. -/
def DeclReducibility.toAttribute : DeclReducibility → Name
  | decl_reducibility.reducible => `reducible
  | decl_reducibility.semireducible => `semireducible
  | decl_reducibility.irreducible => `irreducible
#align tactic.decl_reducibility.to_attribute Tactic.DeclReducibility.toAttribute

-- Note: even though semireducible definitions don't have the `semireducible` attribute
-- (according to `has_attribute`), setting `semireducible` still has the intended effect
-- of clearing `reducible`/`irreducible`.
/-- Set the reducibility attribute of a declaration.
If `persistent := ff`, this is scoped to the enclosing `section`, like `local attribute`. -/
unsafe def set_decl_reducibility (n : Name) (r : DeclReducibility) (persistent := false) :
    tactic Unit :=
  set_basic_attribute r.toAttribute n persistent
#align tactic.set_decl_reducibility tactic.set_decl_reducibility

/-- Execute a tactic with a temporarily modified reducibility attribute for a declaration. -/
unsafe def with_local_reducibility {α : Type _} (n : Name) (r : DeclReducibility)
    (body : tactic α) : tactic α := do
  let r' ← get_decl_reducibility n
  bracket (set_decl_reducibility n r) body (set_decl_reducibility n r')
#align tactic.with_local_reducibility tactic.with_local_reducibility

end Tactic

