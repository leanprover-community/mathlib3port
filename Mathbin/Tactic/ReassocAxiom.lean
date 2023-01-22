/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module tactic.reassoc_axiom
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Basic

/-!
# Tools to reformulate category-theoretic axioms in a more associativity-friendly way

## The `reassoc` attribute

The `reassoc` attribute can be applied to a lemma

```lean
@[reassoc]
lemma some_lemma : foo ≫ bar = baz := ...
```

and produce

```lean
lemma some_lemma_assoc {Y : C} (f : X ⟶ Y) : foo ≫ bar ≫ f = baz ≫ f := ...
```

The name of the produced lemma can be specified with `@[reassoc other_lemma_name]`. If
`simp` is added first, the generated lemma will also have the `simp` attribute.

## The `reassoc_axiom` command

When declaring a class of categories, the axioms can be reformulated to be more amenable
to manipulation in right associated expressions:

```lean
class some_class (C : Type) [category C] :=
(foo : Π X : C, X ⟶ X)
(bar : ∀ {X Y : C} (f : X ⟶ Y), foo X ≫ f = f ≫ foo Y)

reassoc_axiom some_class.bar
```

Here too, the `reassoc` attribute can be used instead. It works well when combined with
`simp`:

```lean
attribute [simp, reassoc] some_class.bar
```
-/


namespace Tactic

open CategoryTheory

/-- From an expression `f ≫ g`, extract the expression representing the category instance. -/
unsafe def get_cat_inst : expr → tactic expr
  | q(@CategoryStruct.comp _ $(struct_inst) _ _ _ _ _) => pure struct_inst
  | _ => failed
#align tactic.get_cat_inst tactic.get_cat_inst

/-- (internals for `@[reassoc]`)
Given a lemma of the form `∀ ..., f ≫ g = h`, proves a new lemma of the form
`h : ∀ ... {W} (k), f ≫ (g ≫ k) = h ≫ k`, and returns the type and proof of this lemma.
-/
unsafe def prove_reassoc (h : expr) : tactic (expr × expr) := do
  let (vs, t) ← infer_type h >>= open_pis
  let (lhs, rhs) ← match_eq t
  let struct_inst ←
    get_cat_inst lhs <|> get_cat_inst rhs <|> fail "no composition found in statement"
  let q(@Quiver.Hom _ $(hom_inst) $(X) $(Y)) ← infer_type lhs
  let C ← infer_type X
  let X' ← mk_local' `X' BinderInfo.implicit C
  let ft ← to_expr ``(@Quiver.Hom _ $(hom_inst) $(Y) $(X'))
  let f' ← mk_local_def `f' ft
  let t' ←
    to_expr
        ``(@CategoryStruct.comp _ $(struct_inst) _ _ _ $(lhs) $(f') =
            @CategoryStruct.comp _ $(struct_inst) _ _ _ $(rhs) $(f'))
  let c' := h.mk_app vs
  let (_, pr) ← solve_aux t' (andthen (rewrite_target c') reflexivity)
  let pr ← instantiate_mvars pr
  let s := simp_lemmas.mk
  let s ← s.add_simp `` category.assoc
  let s ← s.add_simp `` category.id_comp
  let s ← s.add_simp `` category.comp_id
  let (t'', pr', _) ← simplify s [] t'
  let pr' ← mk_eq_mp pr' pr
  let t'' ← pis (vs ++ [X', f']) t''
  let pr' ← lambdas (vs ++ [X', f']) pr'
  pure (t'', pr')
#align tactic.prove_reassoc tactic.prove_reassoc

/-- (implementation for `@[reassoc]`)
Given a declaration named `n` of the form `∀ ..., f ≫ g = h`, proves a new lemma named `n'`
of the form `∀ ... {W} (k), f ≫ (g ≫ k) = h ≫ k`.
-/
unsafe def reassoc_axiom (n : Name) (n' : Name := n.appendSuffix "_assoc") : tactic Unit := do
  let d ← get_decl n
  let ls := d.univ_params.map level.param
  let c := @expr.const true n ls
  let (t'', pr') ← prove_reassoc c
  add_decl <| declaration.thm n' d t'' (pure pr')
  copy_attribute `simp n n'
#align tactic.reassoc_axiom tactic.reassoc_axiom

/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Core.lean:38:34: unsupported: setup_tactic_parser -/
/-- The `reassoc` attribute can be applied to a lemma

```lean
@[reassoc]
lemma some_lemma : foo ≫ bar = baz := ...
```

to produce

```lean
lemma some_lemma_assoc {Y : C} (f : X ⟶ Y) : foo ≫ bar ≫ f = baz ≫ f := ...
```

The name of the produced lemma can be specified with `@[reassoc other_lemma_name]`. If
`simp` is added first, the generated lemma will also have the `simp` attribute.
-/
@[user_attribute]
unsafe def reassoc_attr : user_attribute Unit (Option Name)
    where
  Name := `reassoc
  descr := "create a companion lemma for associativity-aware rewriting"
  parser := optional ident
  after_set :=
    some fun n _ _ => do
      let some n' ← reassoc_attr.get_param n |
        reassoc_axiom n (n.appendSuffix "_assoc")
      reassoc_axiom n <| n ++ n'
#align tactic.reassoc_attr tactic.reassoc_attr

add_tactic_doc
  { Name := "reassoc"
    category := DocCategory.attr
    declNames := [`tactic.reassoc_attr]
    tags := ["category theory"] }

/-- When declaring a class of categories, the axioms can be reformulated to be more amenable
to manipulation in right associated expressions:

```lean
class some_class (C : Type) [category C] :=
(foo : Π X : C, X ⟶ X)
(bar : ∀ {X Y : C} (f : X ⟶ Y), foo X ≫ f = f ≫ foo Y)

reassoc_axiom some_class.bar
```

The above will produce:

```lean
lemma some_class.bar_assoc {Z : C} (g : Y ⟶ Z) :
  foo X ≫ f ≫ g = f ≫ foo Y ≫ g := ...
```

Here too, the `reassoc` attribute can be used instead. It works well when combined with
`simp`:

```lean
attribute [simp, reassoc] some_class.bar
```
-/
@[user_command]
unsafe def reassoc_cmd (_ : parse <| tk "reassoc_axiom") : lean.parser Unit := do
  let n ← ident
  of_tactic do
      let n ← resolve_constant n
      reassoc_axiom n
#align tactic.reassoc_cmd tactic.reassoc_cmd

add_tactic_doc
  { Name := "reassoc_axiom"
    category := DocCategory.cmd
    declNames := [`tactic.reassoc_cmd]
    tags := ["category theory"] }

namespace Interactive

/-- `reassoc h`, for assumption `h : x ≫ y = z`, creates a new assumption
`h : ∀ {W} (f : Z ⟶ W), x ≫ y ≫ f = z ≫ f`.
`reassoc! h`, does the same but deletes the initial `h` assumption.
(You can also add the attribute `@[reassoc]` to lemmas to generate new declarations generalized
in this way.)
-/
unsafe def reassoc (del : parse (tk "!")?) (ns : parse ident*) : tactic Unit := do
  ns fun n => do
      let h ← get_local n
      let (t, pr) ← prove_reassoc h
      assertv n t pr
      when del (tactic.clear h)
#align tactic.interactive.reassoc tactic.interactive.reassoc

end Interactive

def CalculatedProp {α} (β : Prop) (hh : α) :=
  β
#align tactic.calculated_Prop Tactic.CalculatedProp

unsafe def derive_reassoc_proof : tactic Unit := do
  let q(CalculatedProp $(v) $(h)) ← target
  let (t, pr) ← prove_reassoc h
  unify v t
  exact pr
#align tactic.derive_reassoc_proof tactic.derive_reassoc_proof

end Tactic

/-- With `h : x ≫ y ≫ z = x` (with universal quantifiers tolerated),
`reassoc_of h : ∀ {X'} (f : W ⟶ X'), x ≫ y ≫ z ≫ f = x ≫ f`.

The type and proof of `reassoc_of h` is generated by `tactic.derive_reassoc_proof`
which make `reassoc_of` meta-programming adjacent. It is not called as a tactic but as
an expression. The goal is to avoid creating assumptions that are dismissed after one use:

```lean
example (X Y Z W : C) (x : X ⟶ Y) (y : Y ⟶ Z) (z z' : Z ⟶ W) (w : X ⟶ Z)
  (h : x ≫ y = w)
  (h' : y ≫ z = y ≫ z') :
  x ≫ y ≫ z = w ≫ z' :=
begin
  rw [h',reassoc_of h],
end
```
-/
theorem CategoryTheory.reassoc_of {α} (hh : α) {β}
    (x : Tactic.CalculatedProp β hh := by derive_reassoc_proof) : β :=
  x
#align category_theory.reassoc_of CategoryTheory.reassoc_of

/-- `reassoc_of h` takes local assumption `h` and add a ` ≫ f` term on the right of
both sides of the equality. Instead of creating a new assumption from the result, `reassoc_of h`
stands for the proof of that reassociated statement. This keeps complicated assumptions that are
used only once or twice from polluting the local context.

In the following, assumption `h` is needed in a reassociated form. Instead of proving it as a new
goal and adding it as an assumption, we use `reassoc_of h` as a rewrite rule which works just as
well.

```lean
example (X Y Z W : C) (x : X ⟶ Y) (y : Y ⟶ Z) (z z' : Z ⟶ W) (w : X ⟶ Z)
  (h : x ≫ y = w)
  (h' : y ≫ z = y ≫ z') :
  x ≫ y ≫ z = w ≫ z' :=
begin
  -- reassoc_of h : ∀ {X' : C} (f : W ⟶ X'), x ≫ y ≫ f = w ≫ f
  rw [h',reassoc_of h],
end
```

Although `reassoc_of` is not a tactic or a meta program, its type is generated
through meta-programming to make it usable inside normal expressions.
-/
add_tactic_doc
  { Name := "category_theory.reassoc_of"
    category := DocCategory.tactic
    declNames := [`category_theory.reassoc_of]
    tags := ["category theory"] }

