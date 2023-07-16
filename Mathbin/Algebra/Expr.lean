/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.expr
! leanprover-community/mathlib commit 6b711d2ba5d470c040677ddda0c26b0d72283886
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Core

/-! ### Helpers to invoke functions involving algebra at tactic time

It's not clear whether using `instance_cache` is a sensible choice here.
In particular, we need to use these tactics below when the algebraic instances are local variables
that aren't in the "real" instance cache (the one used by `tactic.reset_instance_cache`).
-/


namespace Expr

/-- Produce a `has_one` instance for the type cached by `t`, such that `1 : expr` is the one of that
type. -/
unsafe def has_one (t : tactic.instance_cache) : tactic (tactic.instance_cache × One expr) := do
  let (t, one) ← t.mk_app `has_one.one []
  pure (t, { one })
#align expr.has_one expr.has_one

/-- Produce a `has_zero` instance for the type cached by `t`, such that `0 : expr` is the zero of
that type. -/
unsafe def has_zero (t : tactic.instance_cache) : tactic (tactic.instance_cache × Zero expr) := do
  let (t, zero) ← t.mk_app `has_zero.zero []
  pure (t, { zero })
#align expr.has_zero expr.has_zero

/-- Produce a `has_mul` instance for the type cached by `t`, such that `(*) : expr → expr → expr` is
the multiplication of that type. -/
unsafe def has_mul (t : tactic.instance_cache) : tactic (tactic.instance_cache × Mul expr) := do
  let (t, mul) ← t.mk_app `has_mul.mul []
  pure (t, { mul := fun a b => mul a b })
#align expr.has_mul expr.has_mul

/-- Produce a `has_add` instance for the type cached by `t`, such that `(+) : expr → expr → expr` is
the addition of that type. -/
unsafe def has_add (t : tactic.instance_cache) : tactic (tactic.instance_cache × Add expr) := do
  let (t, add) ← t.mk_app `has_add.add []
  pure (t, { add := fun a b => add a b })
#align expr.has_add expr.has_add

end Expr

