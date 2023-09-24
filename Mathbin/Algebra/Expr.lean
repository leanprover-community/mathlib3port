/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Tactic.Core

#align_import algebra.expr from "leanprover-community/mathlib"@"08b081ea92d80e3a41f899eea36ef6d56e0f1db0"

/-! ### Helpers to invoke functions involving algebra at tactic time

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

It's not clear whether using `instance_cache` is a sensible choice here.
In particular, we need to use these tactics below when the algebraic instances are local variables
that aren't in the "real" instance cache (the one used by `tactic.reset_instance_cache`).
-/


namespace Expr

/-- Produce a `has_one` instance for the type cached by `t`, such that `1 : expr` is the one of that
type. -/
unsafe def instOne (t : tactic.instance_cache) : tactic (tactic.instance_cache × One expr) := do
  let (t, one) ← t.mk_app `has_one.one []
  pure (t, { one })
#align expr.has_one Expr.instOneₓ

/-- Produce a `has_zero` instance for the type cached by `t`, such that `0 : expr` is the zero of
that type. -/
unsafe def instZero (t : tactic.instance_cache) : tactic (tactic.instance_cache × Zero expr) := do
  let (t, zero) ← t.mk_app `has_zero.zero []
  pure (t, { zero })
#align expr.has_zero Expr.instZeroₓ

/-- Produce a `has_mul` instance for the type cached by `t`, such that `(*) : expr → expr → expr` is
the multiplication of that type. -/
unsafe def instMul (t : tactic.instance_cache) : tactic (tactic.instance_cache × Mul expr) := do
  let (t, mul) ← t.mk_app `has_mul.mul []
  pure (t, { mul := fun a b => mul a b })
#align expr.has_mul Expr.instMulₓ

/-- Produce a `has_add` instance for the type cached by `t`, such that `(+) : expr → expr → expr` is
the addition of that type. -/
unsafe def instAdd (t : tactic.instance_cache) : tactic (tactic.instance_cache × Add expr) := do
  let (t, add) ← t.mk_app `has_add.add []
  pure (t, { add := fun a b => add a b })
#align expr.has_add Expr.instAddₓ

end Expr

