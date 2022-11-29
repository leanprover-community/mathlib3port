/-
Copyright (c) 2022 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Eric Wieser
-/

/-!
# Reflection of universe variables

The `reflect` and `has_reflect` machinery (sometimes via the `` `(expr) `` syntax) allows
terms to be converted to the expression that constructs them. However, this construction does not
support universe variables.

This file provides a typeclass `reflected_univ.{u}` to match a universe variable `u` with a level
`l`, which allows `reflect` to be used universe-polymorphically.

## Main definitions

* `reflected_univ.{u}`: A typeclass for reflecting the universe `u` to a `level`.
* `reflect_univ.{u} : level`: Obtain the level of a universe by typeclass search.
* `tactic.interactive.reflect_name`: solve goals of the form `reflected (@foo.{u v})` by searching
  for `reflected_univ.{u}` instances.

-/


/-- A typeclass to translate a universe argument into a `level`. Note that `level.mvar` and
`level.param` are not supported.

Note that the `instance_priority` linter will complain if instance of this class have the default
priority, as it takes no arguments! Since it doesn't make any difference, we do what the linter
asks. -/
unsafe class reflected_univ.{u} where
  lvl : level
#align reflected_univ reflected_univ

universe u v w x y

/-- Reflect a universe variable `u` into a `level` via typeclass search. -/
unsafe def reflect_univ [reflected_univ.{u}] : level :=
  reflected_univ.lvl
#align reflect_univ reflect_univ

unsafe instance (priority := 100) reflect_univ.zero : reflected_univ.{0} :=
  ⟨level.zero⟩
#align reflect_univ.zero reflect_univ.zero

unsafe instance (priority := 100) reflect_univ.succ [reflected_univ.{u}] : reflected_univ.{u + 1} :=
  ⟨level.succ reflect_univ.{u}⟩
#align reflect_univ.succ reflect_univ.succ

unsafe instance (priority := 100) reflect_univ.max [reflected_univ.{u}] [reflected_univ.{v}] :
    reflected_univ.{max u v} :=
  ⟨level.max reflect_univ.{u} reflect_univ.{v}⟩
#align reflect_univ.max reflect_univ.max

unsafe instance (priority := 100) reflect_univ.imax [reflected_univ.{u}] [reflected_univ.{v}] :
    reflected_univ.{imax u v} :=
  ⟨level.imax reflect_univ.{u} reflect_univ.{v}⟩
#align reflect_univ.imax reflect_univ.imax

section

attribute [local semireducible] reflected

/-- This definition circumvents the protection that `reflected` tried to enforce; so is private
such that it is only used by `tactic.interactive.reflect_name` where we have enforced the protection
manually. -/
private unsafe def reflected.of {α : Sort _} {a : α} (e : expr) : reflected _ a :=
  e
#align reflected.of reflected.of

end

/-- Reflect a universe-polymorphic name, by searching for `reflected_univ` instances. -/
unsafe def tactic.interactive.reflect_name : tactic Unit := do
  let tgt ← tactic.target
  let q(reflected _ $(x)) ← pure tgt
  let expr.const Name levels ← pure x
  let levels ←
    levels.mmap fun l => do
        let inst ← tactic.mk_instance (expr.const `reflected_univ [l])
        pure <| expr.app (expr.const `reflect_univ [l]) inst
  let levels := List.foldr (fun a l => q(@List.cons level $(a) $(l))) q(@List.nil level) levels
  let e := q(@expr.const true $(q(Name)) $(levels))
  let e2 := ``((reflected.of $(e) : $(tgt)))
  let e2 ← tactic.to_expr e2
  tactic.exact e2
#align tactic.interactive.reflect_name tactic.interactive.reflect_name

/-- Convenience helper for two consecutive `reflected.subst` applications -/
unsafe def reflected.subst₂ {α : Sort u} {β : α → Sort v} {γ : ∀ a, β a → Sort w} {f : ∀ a b, γ a b}
    {a : α} {b : β a} : reflected _ f → reflected _ a → reflected _ b → reflected _ (f a b) :=
  (· ∘ ·) reflected.subst ∘ reflected.subst
#align reflected.subst₂ reflected.subst₂

/-- Convenience helper for three consecutive `reflected.subst` applications -/
unsafe def reflected.subst₃ {α : Sort u} {β : α → Sort v} {γ : ∀ a, β a → Sort w}
    {δ : ∀ a b, γ a b → Sort x} {f : ∀ a b c, δ a b c} {a : α} {b : β a} {c : γ a b} :
    reflected _ f → reflected _ a → reflected _ b → reflected _ c → reflected _ (f a b c) :=
  (· ∘ ·) reflected.subst₂ ∘ reflected.subst
#align reflected.subst₃ reflected.subst₃

/-- Convenience helper for four consecutive `reflected.subst` applications -/
unsafe def reflected.subst₄ {α : Sort u} {β : α → Sort v} {γ : ∀ a, β a → Sort w}
    {δ : ∀ a b, γ a b → Sort x} {ε : ∀ a b c, δ a b c → Sort y} {f : ∀ a b c d, ε a b c d} {a : α}
    {b : β a} {c : γ a b} {d : δ a b c} :
    reflected _ f →
      reflected _ a → reflected _ b → reflected _ c → reflected _ d → reflected _ (f a b c d) :=
  (· ∘ ·) reflected.subst₃ ∘ reflected.subst
#align reflected.subst₄ reflected.subst₄

/-! ### Universe-polymorphic `has_reflect` instances -/


/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:14: unsupported tactic `reflect_name #[] -/
/-- Universe polymorphic version of the builtin `punit.reflect`. -/
unsafe instance punit.reflect' [reflected_univ.{u}] : has_reflect PUnit.{u}
  | PUnit.unit => by
    trace
      "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:14: unsupported tactic `reflect_name #[]"
#align punit.reflect' punit.reflect'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:14: unsupported tactic `reflect_name #[] -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:14: unsupported tactic `reflect_name #[] -/
/-- Universe polymorphic version of the builtin `list.reflect`. -/
unsafe instance list.reflect' [reflected_univ.{u}] {α : Type u} [has_reflect α] [reflected _ α] :
    has_reflect (List α)
  | [] =>
    (by
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:14: unsupported tactic `reflect_name #[]" :
          reflected _ @List.nil.{u}).subst
      q(α)
  | h :: t =>
    (by
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:14: unsupported tactic `reflect_name #[]" :
          reflected _ @List.cons.{u}).subst₃
      q(α) q(h) (list.reflect' t)
#align list.reflect' list.reflect'

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:14: unsupported tactic `reflect_name #[] -/
unsafe instance ulift.reflect' [reflected_univ.{u}] [reflected_univ.{v}] {α : Type v}
    [reflected _ α] [has_reflect α] : has_reflect (ULift.{u, v} α)
  | ULift.up x =>
    (by
          trace
            "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:65:14: unsupported tactic `reflect_name #[]" :
          reflected _ @ULift.up.{u, v}).subst₂
      q(α) q(x)
#align ulift.reflect' ulift.reflect'

