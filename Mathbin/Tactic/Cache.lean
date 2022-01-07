import Mathbin.Tactic.DocCommands

/-!
# Instance cache tactics

For performance reasons, Lean does not automatically update its database
of class instances during a proof. The group of tactics in this file
helps to force such updates.

-/


open Lean.Parser

open Interactive Interactive.Types

local postfix:9001 "?" => optionalₓ

local postfix:9001 "*" => many

namespace Tactic

/-- Reset the instance cache for the main goal. -/
unsafe def reset_instance_cache : tactic Unit := do
  unfreeze_local_instances
  freeze_local_instances

/-- Unfreeze the local instances while executing `tac` on the main goal. -/
unsafe def unfreezing {α} (tac : tactic α) : tactic α :=
  focus1 $ unfreeze_local_instances *> tac <* all_goals freeze_local_instances

/-- Unfreeze local instances while executing `tac`,
if the passed expression is amongst the frozen instances.
-/
unsafe def unfreezing_hyp (h : expr) (tac : tactic Unit) : tactic Unit := do
  let frozen ← frozen_local_instances
  if h ∈ frozen.get_or_else [] then unfreezing tac else tac

namespace Interactive

/-- `unfreezingI { tac }` executes tac while temporarily unfreezing the instance cache.
-/
unsafe def unfreezingI (tac : itactic) :=
  unfreezing tac

/-- Reset the instance cache. This allows any new instances
added to the context to be used in typeclass inference. -/
unsafe def resetI :=
  reset_instance_cache

/-- Like `subst`, but can also substitute in instance arguments. -/
unsafe def substI (q : parse texpr) : tactic Unit :=
  unfreezingI (subst q)

/-- Like `cases`, but can also be used with instance arguments. -/
unsafe def casesI (p : parse cases_arg_p) (q : parse with_ident_list) : tactic Unit :=
  unfreezingI (cases p q)

/-- Like `intro`, but uses the introduced variable
in typeclass inference. -/
unsafe def introI (p : parse (ident_)?) : tactic Unit :=
  intro p >> reset_instance_cache

/-- Like `intros`, but uses the introduced variable(s)
in typeclass inference. -/
unsafe def introsI (p : parse (ident_)*) : tactic Unit :=
  intros p >> reset_instance_cache

/-- Used to add typeclasses to the context so that they can
be used in typeclass inference. The syntax is the same as `have`. -/
unsafe def haveI (h : parse (ident)?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse (tk ":=" *> texpr)?) : tactic Unit :=
  do
  let h ←
    match h with
      | none => get_unused_name "_inst"
      | some a => return a
  have (some h) q₁ q₂
  match q₂ with
    | none => swap >> reset_instance_cache >> swap
    | some p₂ => reset_instance_cache

/-- Used to add typeclasses to the context so that they can
be used in typeclass inference. The syntax is the same as `let`. -/
unsafe def letI (h : parse (ident)?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : tactic Unit :=
  do
  let h ←
    match h with
      | none => get_unused_name "_inst"
      | some a => return a
  let (some h) q₁ q₂
  match q₂ with
    | none => swap >> reset_instance_cache >> swap
    | some p₂ => reset_instance_cache

/-- Like `exact`, but uses all variables in the context
for typeclass inference. -/
unsafe def exactI (q : parse texpr) : tactic Unit :=
  reset_instance_cache >> exact q

/-- For performance reasons, Lean does not automatically update its database
of class instances during a proof. The group of tactics described below
helps to force such updates. For a simple (but very artificial) example,
consider the function `default` from the core library. It has type
`Π (α : Sort u) [inhabited α], α`, so one can use `default α` only if Lean
can find a registered instance of `inhabited α`. Because the database of
such instance is not automatically updated during a proof, the following
attempt won't work (Lean will not pick up the instance from the local
context):
```lean
def my_id (α : Type) : α → α :=
begin
  intro x,
  have : inhabited α := ⟨x⟩,
  exact default α, -- Won't work!
end
```
However, it will work, producing the identity function, if one replaces `have`
by its variant `haveI` described below.

* `resetI`: Reset the instance cache. This allows any instances
  currently in the context to be used in typeclass inference.

* `unfreezingI { tac }`: Unfreeze local instances while executing the tactic `tac`.

* `introI`/`introsI`: `intro`/`intros` followed by `resetI`. Like
  `intro`/`intros`, but uses the introduced variable in typeclass inference.

* `casesI`: like `cases`, but can also be used with instance arguments.

* `substI`: like `subst`, but can also substitute in type-class arguments

* `haveI`/`letI`: `have`/`let` followed by `resetI`. Used to add typeclasses
  to the context so that they can be used in typeclass inference.

* `exactI`: `resetI` followed by `exact`. Like `exact`, but uses all
  variables in the context for typeclass inference.
-/
add_tactic_doc
  { Name := "Instance cache tactics", category := DocCategory.tactic,
    declNames := [`` resetI, `` unfreezingI, `` casesI, `` substI, `` introI, `` introsI, `` haveI, `` letI, `` exactI],
    tags := ["type class", "context management"] }

end Interactive

end Tactic

