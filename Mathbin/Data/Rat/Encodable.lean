/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Logic.Encodable.Basic
import Mathbin.Data.Nat.Gcd.Basic
import Mathbin.Data.Rat.Init

#align_import data.rat.encodable from "leanprover-community/mathlib"@"f2f413b9d4be3a02840d0663dace76e8fe3da053"

/-! # The rationals are `encodable`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

As a consequence we also get the instance `countable ℚ`.

This is kept separate from `data.rat.defs` in order to minimize imports.
-/


namespace Rat

instance : Encodable ℚ :=
  Encodable.ofEquiv (Σ n : ℤ, { d : ℕ // 0 < d ∧ n.natAbs.Coprime d })
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => rfl,
      fun ⟨a, b, c, d⟩ => rfl⟩

end Rat

