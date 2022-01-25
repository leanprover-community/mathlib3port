import Mathbin.Data.Buffer.Parser.Basic

/-!
# Numeral parsers

This file expands on the existing `nat : parser ℕ` to provide parsers into any type `α` that
can be represented by a numeral, which relies on `α` having a 0, 1, and addition operation.
There are also convenience parsers that ensure that the numeral parsed in is not larger than
the cardinality of the type `α` , if it is known that `fintype α`. Additionally, there are
convenience parsers that parse in starting from "1", which can be useful for positive ordinals;
or parser from a given character or character range.

## Main definitions

* 'numeral` : The parser which uses `nat.cast` to map the result of `parser.nat` to the desired `α`
* `numeral.of_fintype` :  The parser which `guard`s to make sure the parsed numeral is within the
  cardinality of the target `fintype` type `α`.

## Implementation details

When the `numeral` or related parsers are invoked, the desired type is provided explicitly. In many
cases, it can be inferred, so one can write, for example
```lean
def get_fin : string → fin 5 :=
sum.elim (λ _, 0) id ∘ parser.run_string (parser.numeral.of_fintype _)
```

In the definitions of the parsers (except for `numeral`), there is an explicit `nat.bin_cast`
instead an explicit or implicit `nat.cast`
-/


open Parser ParseResult

namespace Parser

variable (α : Type) [Zero α] [One α] [Add α]

/-- Parse a string of digits as a numeral while casting it to target type `α`.
-/
def numeral : Parser α :=
  Nat.binCast <$> Nat deriving mono, Bounded, prog

/-- Parse a string of digits as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint. The parser ensures that the numeral parsed in
is within the cardinality of the type `α`.
-/
def numeral.of_fintype [Fintype α] : Parser α := do
  let c ← Nat
  decorate_error (s! "<numeral less than {toString (Fintype.card α)}>") (guardₓ (c < Fintype.card α))
  pure $ Nat.binCast c deriving mono, Bounded, prog

/-- Parse a string of digits as a numeral while casting it to target type `α`. The parsing starts
at "1", so `"1"` is parsed in as `nat.cast 0`. Providing `"0"` to the parser causes a failure.
-/
def numeral.from_one : Parser α := do
  let c ← Nat
  decorate_error "<positive numeral>" (guardₓ (0 < c))
  pure $ Nat.binCast (c - 1)deriving mono, Bounded, prog

/-- Parse a string of digits as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint. The parser ensures that the numeral parsed in
is within the cardinality of the type `α`. The parsing starts
at "1", so `"1"` is parsed in as `nat.cast 0`. Providing `"0"` to the parser causes a failure.
-/
def numeral.from_one.of_fintype [Fintype α] : Parser α := do
  let c ← Nat
  decorate_error (s! "<positive numeral less than or equal to {toString (Fintype.card α)}>")
      (guardₓ (0 < c ∧ c ≤ Fintype.card α))
  pure $ Nat.binCast (c - 1)deriving mono, Bounded, prog

/-- Parse a character as a numeral while casting it to target type `α`,
The parser ensures that the character parsed in is within the bounds set by `fromc` and `toc`,
and subtracts the value of `fromc` from the parsed in character.
-/
def numeral.char (fromc toc : Charₓ) : Parser α := do
  let c ←
    decorate_error (s! "<char between '{fromc.to_string }' to '{toc.to_string}' inclusively>")
        (sat fun c => fromc ≤ c ∧ c ≤ toc)
  pure $ Nat.binCast (c.to_nat - fromc.to_nat)deriving mono, Bounded, err_static, step

/-- Parse a character as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint.
The parser ensures that the character parsed in is greater or equal to `fromc` and
and subtracts the value of `fromc` from the parsed in character. There is also a check
that the resulting value is within the cardinality of the type `α`.
-/
def numeral.char.of_fintype [Fintype α] (fromc : Charₓ) : Parser α := do
  let c ←
    decorate_error
        (s! "<char from '{fromc.to_string}' to '
              {(Charₓ.ofNat (fromc.to_nat + Fintype.card α - 1)).toString}' inclusively>")
        (sat fun c => fromc ≤ c ∧ c.to_nat - Fintype.card α < fromc.to_nat)
  pure $ Nat.binCast (c.to_nat - fromc.to_nat)deriving mono, Bounded, err_static, step

end Parser

