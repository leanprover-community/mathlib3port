/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Keeley Hoek, Floris van Doorn
-/
import Mathbin.Data.List.Defs

/-!
# Definitions for `string`

This file defines a bunch of functions for the `string` datatype.
-/


namespace String

/- warning: string.split_on -> String.splitOn is a dubious translation:
lean 3 declaration is
  String -> Char -> (List.{0} String)
but is expected to have type
  String -> (optParam.{1} String " ") -> (List.{0} String)
Case conversion may be inaccurate. Consider using '#align string.split_on String.splitOnₓ'. -/
/-- `s.split_on c` tokenizes `s : string` on `c : char`. -/
def splitOn (s : String) (c : Char) : List String :=
  split (· = c) s

/-- `string.map_tokens c f s` tokenizes `s : string` on `c : char`, maps `f` over each token, and
then reassembles the string by intercalating the separator token `c` over the mapped tokens. -/
def mapTokens (c : Char) (f : String → String) : String → String :=
  intercalate (singleton c) ∘ List.map f ∘ split (· = c)

/-- Tests whether the first string is a prefix of the second string. -/
def isPrefixOf (x y : String) : Bool :=
  x.toList.isPrefixOf y.toList

/-- Tests whether the first string is a suffix of the second string. -/
def isSuffixOf (x y : String) : Bool :=
  x.toList.isSuffixOf y.toList

/-- `x.starts_with y` is true if `y` is a prefix of `x`, and is false otherwise. -/
abbrev startsWith (x y : String) : Bool :=
  y.isPrefixOf x

/-- `x.ends_with y` is true if `y` is a suffix of `x`, and is false otherwise. -/
abbrev endsWith (x y : String) : Bool :=
  y.isSuffixOf x

/-- `get_rest s t` returns `some r` if `s = t ++ r`.
  If `t` is not a prefix of `s`, returns `none` -/
def getRest (s t : String) : Option String :=
  List.asString <$> s.toList.getRest t.toList

/-- Removes the first `n` elements from the string `s` -/
def popn (s : String) (n : Nat) : String :=
  (s.mkIterator.nextn n).nextToString

/-- `is_nat s` is true iff `s` is a nonempty sequence of digits. -/
def isNat (s : String) : Bool :=
  ¬s.isEmpty ∧ s.toList.all fun c => decide c.IsDigit

/-- Produce the head character from the string `s`, if `s` is not empty, otherwise 'A'. -/
def head (s : String) : Char :=
  s.mkIterator.curr

end String

