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
  x.to_list.is_prefix_of y.to_list

/-- Tests whether the first string is a suffix of the second string. -/
def is_suffix_of (x y : Stringₓ) : Bool :=
  x.to_list.is_suffix_of y.to_list

/-- `x.starts_with y` is true if `y` is a prefix of `x`, and is false otherwise. -/
abbrev starts_with (x y : Stringₓ) : Bool :=
  y.is_prefix_of x

/-- `x.ends_with y` is true if `y` is a suffix of `x`, and is false otherwise. -/
abbrev ends_with (x y : Stringₓ) : Bool :=
  y.is_suffix_of x

/-- `get_rest s t` returns `some r` if `s = t ++ r`.
  If `t` is not a prefix of `s`, returns `none` -/
def get_rest (s t : Stringₓ) : Option Stringₓ :=
  List.asStringₓ <$> s.to_list.get_rest t.to_list

/-- Removes the first `n` elements from the string `s` -/
def popn (s : Stringₓ) (n : Nat) : Stringₓ :=
  (s.mk_iterator.nextn n).nextToString

/-- `is_nat s` is true iff `s` is a nonempty sequence of digits. -/
def is_nat (s : Stringₓ) : Bool :=
  ¬s.is_empty ∧ s.to_list.all fun c => to_bool c.is_digit

/-- Produce the head character from the string `s`, if `s` is not empty, otherwise 'A'. -/
def head (s : Stringₓ) : Charₓ :=
  s.mk_iterator.curr

end Stringₓ

