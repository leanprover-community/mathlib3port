
/-!
# Absolute value

This file defines a notational class `has_abs` which adds the unary operator `abs` and the notation
`|.|`. The concept of an absolute value occurs in lattice ordered groups and in GL and GM spaces.

## Notations

The notation `|.|` is introduced for the absolute value.

## Tags

absolute
-/


/--
Absolute value is a unary operator with properties similar to the absolute value of a real number.
-/
class HasAbs(α : Type _) where 
  abs : α → α

export HasAbs(abs)

notation "|" a "|" => abs a

