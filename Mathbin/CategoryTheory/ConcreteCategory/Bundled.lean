/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather

! This file was ported from Lean 3 source module category_theory.concrete_category.bundled
! leanprover-community/mathlib commit d101e93197bb5f6ea89bd7ba386b7f7dff1f3903
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Lint.Default

/-!
# Bundled types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`bundled c` provides a uniform structure for bundling a type equipped with a type class.

We provide `category` instances for these in `category_theory/unbundled_hom.lean`
(for categories with unbundled homs, e.g. topological spaces)
and in `category_theory/bundled_hom.lean` (for categories with bundled homs, e.g. monoids).
-/


universe u v

namespace CategoryTheory

variable {c d : Type u → Type v} {α : Type u}

#print CategoryTheory.Bundled /-
/-- `bundled` is a type bundled with a type class instance for that type. Only
the type class is exposed as a parameter. -/
@[nolint has_nonempty_instance]
structure Bundled (c : Type u → Type v) : Type max (u + 1) v where
  α : Type u
  str : c α := by infer_instance
#align category_theory.bundled CategoryTheory.Bundled
-/

namespace Bundled

#print CategoryTheory.Bundled.of /-
-- Usually explicit instances will provide their own version of this, e.g. `Mon.of` and `Top.of`.
/-- A generic function for lifting a type equipped with an instance to a bundled object. -/
def of {c : Type u → Type v} (α : Type u) [str : c α] : Bundled c :=
  ⟨α, str⟩
#align category_theory.bundled.of CategoryTheory.Bundled.of
-/

instance : CoeSort (Bundled c) (Type u) :=
  ⟨Bundled.α⟩

#print CategoryTheory.Bundled.coe_mk /-
@[simp]
theorem coe_mk (α) (str) : (@Bundled.mk c α str : Type u) = α :=
  rfl
#align category_theory.bundled.coe_mk CategoryTheory.Bundled.coe_mk
-/

#print CategoryTheory.Bundled.map /-
/-
`bundled.map` is reducible so that, if we define a category

  def Ring : Type (u+1) := induced_category SemiRing (bundled.map @ring.to_semiring)

instance search is able to "see" that a morphism R ⟶ S in Ring is really
a (semi)ring homomorphism from R.α to S.α, and not merely from
`(bundled.map @ring.to_semiring R).α` to `(bundled.map @ring.to_semiring S).α`.
-/
/-- Map over the bundled structure -/
@[reducible]
def map (f : ∀ {α}, c α → d α) (b : Bundled c) : Bundled d :=
  ⟨b, f b.str⟩
#align category_theory.bundled.map CategoryTheory.Bundled.map
-/

end Bundled

end CategoryTheory

