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

variable (α : Type) [HasZero α] [HasOne α] [Add α]

-- error in Data.Buffer.Parser.Numeral: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler mono
/--
Parse a string of digits as a numeral while casting it to target type `α`.
-/ @[derive #["[", expr mono, ",", expr bounded, ",", expr prog, "]"]] def numeral : parser α :=
«expr <$> »(nat.bin_cast, nat)

-- error in Data.Buffer.Parser.Numeral: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler mono
/--
Parse a string of digits as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint. The parser ensures that the numeral parsed in
is within the cardinality of the type `α`.
-/ @[derive #["[", expr mono, ",", expr bounded, ",", expr prog, "]"]] def numeral.of_fintype [fintype α] : parser α :=
do {
c ← nat,
  decorate_error «exprsformat! »(sformat_macro "<numeral less than {to_string (fintype.card α)}>" [[expr to_string (fintype.card α)]]) (guard «expr < »(c, fintype.card α)),
  «expr $ »(pure, nat.bin_cast c) }

-- error in Data.Buffer.Parser.Numeral: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler mono
/--
Parse a string of digits as a numeral while casting it to target type `α`. The parsing starts
at "1", so `"1"` is parsed in as `nat.cast 0`. Providing `"0"` to the parser causes a failure.
-/ @[derive #["[", expr mono, ",", expr bounded, ",", expr prog, "]"]] def numeral.from_one : parser α :=
do {
c ← nat,
  decorate_error "<positive numeral>" (guard «expr < »(0, c)),
  «expr $ »(pure, nat.bin_cast «expr - »(c, 1)) }

-- error in Data.Buffer.Parser.Numeral: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler mono
/--
Parse a string of digits as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint. The parser ensures that the numeral parsed in
is within the cardinality of the type `α`. The parsing starts
at "1", so `"1"` is parsed in as `nat.cast 0`. Providing `"0"` to the parser causes a failure.
-/
@[derive #["[", expr mono, ",", expr bounded, ",", expr prog, "]"]]
def numeral.from_one.of_fintype [fintype α] : parser α :=
do {
c ← nat,
  decorate_error «exprsformat! »(sformat_macro "<positive numeral less than or equal to {to_string (fintype.card α)}>" [[expr to_string (fintype.card α)]]) (guard «expr ∧ »(«expr < »(0, c), «expr ≤ »(c, fintype.card α))),
  «expr $ »(pure, nat.bin_cast «expr - »(c, 1)) }

-- error in Data.Buffer.Parser.Numeral: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler mono
/--
Parse a character as a numeral while casting it to target type `α`,
The parser ensures that the character parsed in is within the bounds set by `fromc` and `toc`,
and subtracts the value of `fromc` from the parsed in character.
-/
@[derive #["[", expr mono, ",", expr bounded, ",", expr err_static, ",", expr step, "]"]]
def numeral.char (fromc toc : char) : parser α :=
do {
c ← decorate_error «exprsformat! »(sformat_macro "<char between '{fromc.to_string}' to '{toc.to_string}' inclusively>" [[expr fromc.to_string], [expr toc.to_string]]) (sat (λ
    c, «expr ∧ »(«expr ≤ »(fromc, c), «expr ≤ »(c, toc)))),
  «expr $ »(pure, nat.bin_cast «expr - »(c.to_nat, fromc.to_nat)) }

-- error in Data.Buffer.Parser.Numeral: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler mono
/--
Parse a character as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint.
The parser ensures that the character parsed in is greater or equal to `fromc` and
and subtracts the value of `fromc` from the parsed in character. There is also a check
that the resulting value is within the cardinality of the type `α`.
-/
@[derive #["[", expr mono, ",", expr bounded, ",", expr err_static, ",", expr step, "]"]]
def numeral.char.of_fintype [fintype α] (fromc : char) : parser α :=
do {
c ← decorate_error «exprsformat! »(sformat_macro "<char from '{fromc.to_string}' to '\n    { (char.of_nat (fromc.to_nat + fintype.card α - 1)).to_string}' inclusively>" [[expr fromc.to_string], [expr (char.of_nat «expr - »(«expr + »(fromc.to_nat, fintype.card α), 1)).to_string]]) (sat (λ
    c, «expr ∧ »(«expr ≤ »(fromc, c), «expr < »(«expr - »(c.to_nat, fintype.card α), fromc.to_nat)))),
  «expr $ »(pure, nat.bin_cast «expr - »(c.to_nat, fromc.to_nat)) }

end Parser

