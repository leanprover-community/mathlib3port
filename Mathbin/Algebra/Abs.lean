/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

/-!
# Absolute value

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


/-- Absolute value is a unary operator with properties similar to the absolute value of a real number.
-/
class HasAbs (α : Type _) where
  abs : α → α

export HasAbs (abs)

/-- The positive part of an element admiting a decomposition into positive and negative parts.
-/
class HasPosPart (α : Type _) where
  Pos : α → α

/-- The negative part of an element admiting a decomposition into positive and negative parts.
-/
class HasNegPart (α : Type _) where
  neg : α → α

-- mathport name: «expr ⁺»
postfix:1000 "⁺" => HasPosPart.pos

-- mathport name: «expr ⁻»
postfix:1000 "⁻" => HasNegPart.neg

