/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.rat.init
! leanprover-community/mathlib commit 509de852e1de55e1efa8eacfa11df0823f26f226
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Ext
import Mathbin.Logic.Basic

/-!
# The definition of the Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We define a rational number `q` as a structure `{ num, denom, pos, cop }`, where
- `num` is the numerator of `q`,
- `denom` is the denominator of `q`,
- `pos` is a proof that `denom > 0`, and
- `cop` is a proof `num` and `denom` are coprime.

Basic constructions and results are set up in `data.rat.defs`.
As we transition to Lean 4, these two files can probably be merged again,
as so much of the needed material will be in Std4 anyway.

For now, this split allows us to give the definitions of division rings and fields
without significant theory imports.

The definition of the field structure on `ℚ` will be done in `data.rat.basic` once the
`field` class has been defined.

## Main Definitions

- `rat` is the structure encoding `ℚ`.

## Notations

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/


#print Rat /-
/-- `rat`, or `ℚ`, is the type of rational numbers. It is defined
  as the set of pairs ⟨n, d⟩ of integers such that `d` is positive and `n` and
  `d` are coprime. This representation is preferred to the quotient
  because without periodic reduction, the numerator and denominator can grow
  exponentially (for example, adding 1/2 to itself repeatedly). -/
structure Rat where mk' ::
  num : ℤ
  denom : ℕ
  Pos : 0 < denom
  cop : Num.natAbs.Coprime denom
#align rat Rat
-/

-- mathport name: exprℚ
notation "ℚ" => Rat

namespace Rat

/-- String representation of a rational numbers, used in `has_repr`, `has_to_string`, and
`has_to_format` instances. -/
protected def repr : ℚ → String
  | ⟨n, d, _, _⟩ => if d = 1 then repr n else repr n ++ "/" ++ repr d
#align rat.repr Rat.repr

instance : Repr ℚ :=
  ⟨Rat.repr⟩

instance : ToString ℚ :=
  ⟨Rat.repr⟩

unsafe instance : has_to_format ℚ :=
  ⟨coe ∘ Rat.repr⟩

#print Rat.ext_iff /-
theorem ext_iff {p q : ℚ} : p = q ↔ p.num = q.num ∧ p.denom = q.denom :=
  by
  cases p
  cases q
  simp
#align rat.ext_iff Rat.ext_iff
-/

#print Rat.ext /-
@[ext]
theorem ext {p q : ℚ} (hn : p.num = q.num) (hd : p.denom = q.denom) : p = q :=
  Rat.ext_iff.mpr ⟨hn, hd⟩
#align rat.ext Rat.ext
-/

end Rat

