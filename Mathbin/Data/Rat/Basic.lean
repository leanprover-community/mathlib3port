/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.rat.basic
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Field.Defs
import Mathbin.Data.Rat.Defs

/-!
# Field Structure on the Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We put the (discrete) field structure on the type `ℚ` of rational numbers that
was defined in `data.rat.defs`.

## Main Definitions

- `rat.field` is the field structure on `ℚ`.

## Implementation notes

We have to define the field structure in a separate file to avoid cyclic imports:
the `field` class contains a map from `ℚ` (see `field`'s docstring for the rationale),
so we have a dependency `rat.field → field → rat` that is reflected in the import
hierarchy `data.rat.basic → algebra.field.basic → data.rat.defs`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/


namespace Rat

instance : Field ℚ :=
  { Rat.commRing, Rat.commGroupWithZero with
    zero := 0
    add := (· + ·)
    neg := Neg.neg
    one := 1
    mul := (· * ·)
    inv := Inv.inv
    ratCast := id
    ratCast_mk := fun a b h1 h2 => (num_div_den _).symm
    qsmul := (· * ·) }

-- Extra instances to short-circuit type class resolution
instance : DivisionRing ℚ := by infer_instance

end Rat

