import Mathbin.Tactic.Core

/-!
# `with_local_reducibility`

Run a tactic in an environment with a temporarily modified reducibility attribute
for a specified declaration.
-/


namespace Tactic

-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler decidable_eq
/--  Possible reducibility attributes for a declaration:
reducible, semireducible (the default), irreducible. -/
inductive decl_reducibility
  | reducible
  | semireducible
  | irreducible
  deriving [anonymous]

/--  Satisfy the inhabited linter -/
instance : Inhabited decl_reducibility :=
  ⟨decl_reducibility.semireducible⟩

/--  Get the reducibility attribute of a declaration.
Fails if the name does not refer to an existing declaration. -/
unsafe def get_decl_reducibility (n : Name) : tactic decl_reducibility := do
  let is_irred ← has_attribute' `irreducible n
  if is_irred then pure decl_reducibility.irreducible
    else do
      let is_red ← has_attribute' `reducible n
      if is_red then pure decl_reducibility.reducible
        else do
          let e ← get_env
          if e.contains n then pure decl_reducibility.semireducible
            else fail f! "get_decl_reducibility: no declaration {n}"

/--  Return the attribute (as a `name`) corresponding to a reducibility level. -/
def decl_reducibility.to_attribute : decl_reducibility → Name
  | decl_reducibility.reducible => `reducible
  | decl_reducibility.semireducible => `semireducible
  | decl_reducibility.irreducible => `irreducible

/--  Set the reducibility attribute of a declaration.
If `persistent := ff`, this is scoped to the enclosing `section`, like `local attribute`. -/
unsafe def set_decl_reducibility (n : Name) (r : decl_reducibility) (persistent := ff) : tactic Unit :=
  set_basic_attribute r.to_attribute n persistent

/--  Execute a tactic with a temporarily modified reducibility attribute for a declaration. -/
unsafe def with_local_reducibility {α : Type _} (n : Name) (r : decl_reducibility) (body : tactic α) : tactic α := do
  let r' ← get_decl_reducibility n
  bracket (set_decl_reducibility n r) body (set_decl_reducibility n r')

end Tactic

