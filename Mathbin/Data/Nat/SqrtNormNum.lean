/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.nat.sqrt_norm_num
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.NormNum
import Mathbin.Data.Nat.Sqrt

/-! ### `norm_num` plugin for `sqrt`

The `norm_num` plugin evaluates `sqrt` by bounding it between consecutive integers.
-/


namespace NormNum

open Tactic Nat

theorem is_sqrt {n a a2 b : ℕ} (ha2 : a * a = a2) (hb : a2 + b = n) (hle : b ≤ bit0 a) :
    sqrt n = a := by
  rw [← hb, ← ha2, ← pow_two]
  exact sqrt_add_eq' _ hle
#align norm_num.is_sqrt NormNum.is_sqrt

/-- Given `n` provides `(a, ⊢ nat.sqrt n = a)`. -/
unsafe def prove_sqrt (ic : instance_cache) (n : expr) : tactic (instance_cache × expr × expr) := do
  let nn ← n.to_nat
  let na := nn.sqrt
  let (ic, a) ← ic.of_nat na
  let (ic, a2, ha2) ← prove_mul_nat ic a a
  let (ic, b) ← ic.of_nat (nn - na * na)
  let (ic, hb) ← prove_add_nat ic a2 b n
  let (ic, hle) ← prove_le_nat ic b (q((bit0 : ℕ → ℕ)).mk_app [a])
  pure (ic, a, q(@is_sqrt).mk_app [n, a, a2, b, ha2, hb, hle])
#align norm_num.prove_sqrt norm_num.prove_sqrt

/-- A `norm_num` plugin for `sqrt n` when `n` is a numeral. -/
@[norm_num]
unsafe def eval_sqrt : expr → tactic (expr × expr)
  | q(sqrt $(en)) => do
    let n ← en.to_nat
    match n with
      | 0 => pure (q((0 : ℕ)), q(sqrt_zero))
      | _ => do
        let c ← mk_instance_cache q(ℕ)
        prod.snd <$> prove_sqrt c en
  | _ => failed
#align norm_num.eval_sqrt norm_num.eval_sqrt

end NormNum

