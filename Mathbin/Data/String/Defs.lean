import Mathbin.Data.List.Defs

/-!
# Definitions for `string`

This file defines a bunch of functions for the `string` datatype.
-/


namespace Stringₓ

/-- `s.split_on c` tokenizes `s : string` on `c : char`. -/
def split_on (s : Stringₓ) (c : Charₓ) : List Stringₓ :=
  split (· = c) s

/-- `string.map_tokens c f s` tokenizes `s : string` on `c : char`, maps `f` over each token, and
then reassembles the string by intercalating the separator token `c` over the mapped tokens. -/
def map_tokens (c : Charₓ) (f : Stringₓ → Stringₓ) : Stringₓ → Stringₓ :=
  intercalate (singleton c) ∘ List.map f ∘ split (· = c)

/-- Tests whether the first string is a prefix of the second string. -/
def is_prefix_of (x y : Stringₓ) : Bool :=
  x.toList.isPrefixOf y.toList

/-- Tests whether the first string is a suffix of the second string. -/
def is_suffix_of (x y : Stringₓ) : Bool :=
  x.toList.isSuffixOf y.toList

/-- `x.starts_with y` is true if `y` is a prefix of `x`, and is false otherwise. -/
abbrev starts_with (x y : Stringₓ) : Bool :=
  y.isPrefixOf x

/-- `x.ends_with y` is true if `y` is a suffix of `x`, and is false otherwise. -/
abbrev ends_with (x y : Stringₓ) : Bool :=
  y.isSuffixOf x

/-- `get_rest s t` returns `some r` if `s = t ++ r`.
  If `t` is not a prefix of `s`, returns `none` -/
def get_rest (s t : Stringₓ) : Option Stringₓ :=
  List.asStringₓ <$> s.toList.getRest t.toList

/-- Removes the first `n` elements from the string `s` -/
def popn (s : Stringₓ) (n : Nat) : Stringₓ :=
  (s.mkIterator.nextn n).nextToString

/-- `is_nat s` is true iff `s` is a nonempty sequence of digits. -/
def is_nat (s : Stringₓ) : Bool :=
  ¬s.isEmpty ∧ s.toList.all fun c => toBool c.IsDigit

/-- Produce the head character from the string `s`, if `s` is not empty, otherwise 'A'. -/
def head (s : Stringₓ) : Charₓ :=
  s.mkIterator.curr

end Stringₓ

