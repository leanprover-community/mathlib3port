/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin

! This file was ported from Lean 3 source module algebra.abs
! leanprover-community/mathlib commit 940d371319c6658e526349d2c3e1daeeabfae0fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

/-!
# Absolute value

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a notational class `has_abs` which adds the unary operator `abs` and the notation
`|.|`. The concept of an absolute value occurs in lattice ordered groups and in GL and GM spaces.

Mathematical structures possessing an absolute value often also possess a unique decomposition of
elements into "positive" and "negative" parts which are in some sense "disjoint" (e.g. the Jordan
decomposition of a measure). This file also defines `has_pos_part` and `has_neg_part` classes
which add unary operators `pos` and `neg`, representing the maps taking an element to its positive
and negative part respectively along with the notation ⁺ and ⁻.

## Notations

The following notation is introduced:

* `|.|` for the absolute value;
* `.⁺` for the positive part;
* `.⁻` for the negative part.

## Tags

absolute
-/


#print Abs /-
/--
Absolute value is a unary operator with properties similar to the absolute value of a real number.
-/
class Abs (α : Type _) where
  abs : α → α
#align has_abs Abs
-/

export Abs (abs)

#print PosPart /-
/-- The positive part of an element admiting a decomposition into positive and negative parts.
-/
class PosPart (α : Type _) where
  Pos : α → α
#align has_pos_part PosPart
-/

#print NegPart /-
/-- The negative part of an element admiting a decomposition into positive and negative parts.
-/
class NegPart (α : Type _) where
  neg : α → α
#align has_neg_part NegPart
-/

-- mathport name: «expr ⁺»
postfix:1000 "⁺" => PosPart.pos

-- mathport name: «expr ⁻»
postfix:1000 "⁻" => NegPart.neg

