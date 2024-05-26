/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Algebra.Field.Defs
import Data.Rat.Defs

#align_import data.rat.basic from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

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
    ratCast_def := fun a b h1 h2 => (num_div_den _).symm
    qsmul := (· * ·) }

-- Extra instances to short-circuit type class resolution
instance : DivisionRing ℚ := by infer_instance

end Rat

