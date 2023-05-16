/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler

! This file was ported from Lean 3 source module analysis.special_functions.pow.tactic
! leanprover-community/mathlib commit 0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow.Nnreal

/-!
# Tactics for power functions

This file contains extensions to the `norm_num` and `positivity` tactics to handle power operations
on `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞`.

TODO: Split up the contents of this file and merge with other files in
`analysis/special_functions/pow/`, to keep the tactics together with the corresponding definitions.

-/


open NNReal ENNReal

/-!
## Complex case
-/


namespace NormNum

theorem cpow_pos (a b : ℂ) (b' : ℕ) (c : ℂ) (hb : b = b') (h : a ^ b' = c) : a ^ b = c := by
  rw [← h, hb, Complex.cpow_nat_cast]
#align norm_num.cpow_pos NormNum.cpow_pos

theorem cpow_neg (a b : ℂ) (b' : ℕ) (c c' : ℂ) (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') :
    a ^ (-b) = c' := by rw [← hc, ← h, hb, Complex.cpow_neg, Complex.cpow_nat_cast]
#align norm_num.cpow_neg NormNum.cpow_neg

end NormNum

/-!
## Real case
-/


namespace NormNum

open Tactic

theorem rpow_pos (a b : ℝ) (b' : ℕ) (c : ℝ) (hb : (b' : ℝ) = b) (h : a ^ b' = c) : a ^ b = c := by
  rw [← h, ← hb, Real.rpow_nat_cast]
#align norm_num.rpow_pos NormNum.rpow_pos

theorem rpow_neg (a b : ℝ) (b' : ℕ) (c c' : ℝ) (a0 : 0 ≤ a) (hb : (b' : ℝ) = b) (h : a ^ b' = c)
    (hc : c⁻¹ = c') : a ^ (-b) = c' := by rw [← hc, ← h, ← hb, Real.rpow_neg a0, Real.rpow_nat_cast]
#align norm_num.rpow_neg NormNum.rpow_neg

/-- Evaluate `real.rpow a b` where `a` is a rational numeral and `b` is an integer.
(This cannot go via the generalized version `prove_rpow'` because `rpow_pos` has a side condition;
we do not attempt to evaluate `a ^ b` where `a` and `b` are both negative because it comes
out to some garbage.) -/
unsafe def prove_rpow (a b : expr) : tactic (expr × expr) := do
  let na ← a.to_rat
  let ic ← mk_instance_cache q(ℝ)
  match match_sign b with
    | Sum.inl b => do
      let (ic, a0) ← guard (na ≥ 0) >> prove_nonneg ic a
      let nc ← mk_instance_cache q(ℕ)
      let (ic, nc, b', hb) ← prove_nat_uncast ic nc b
      let (ic, c, h) ← prove_pow a na ic b'
      let cr ← c
      let (ic, c', hc) ← prove_inv ic c cr
      pure (c', (expr.const `` rpow_neg []).mk_app [a, b, b', c, c', a0, hb, h, hc])
    | Sum.inr ff => pure (q((1 : ℝ)), expr.const `` Real.rpow_zero [] a)
    | Sum.inr tt => do
      let nc ← mk_instance_cache q(ℕ)
      let (ic, nc, b', hb) ← prove_nat_uncast ic nc b
      let (ic, c, h) ← prove_pow a na ic b'
      pure (c, (expr.const `` rpow_pos []).mk_app [a, b, b', c, hb, h])
#align norm_num.prove_rpow norm_num.prove_rpow

end NormNum

namespace Tactic

namespace Positivity

/-- Auxiliary definition for the `positivity` tactic to handle real powers of reals. -/
unsafe def prove_rpow (a b : expr) : tactic strictness := do
  let strictness_a ← core a
  match strictness_a with
    | nonnegative p => nonnegative <$> mk_app `` Real.rpow_nonneg_of_nonneg [p, b]
    | positive p => positive <$> mk_app `` Real.rpow_pos_of_pos [p, b]
    | _ => failed
#align tactic.positivity.prove_rpow tactic.positivity.prove_rpow

end Positivity

end Tactic

/-!
## General-purpose tactics

The following code covers all the cases `ℂ`, `ℝ`, `ℝ≥0`, and `ℝ≥0∞` together.
-/


namespace NormNum

open Tactic

/-- Generalized version of `prove_cpow`, `prove_nnrpow`, `prove_ennrpow`. -/
unsafe def prove_rpow' (pos neg zero : Name) (α β one a b : expr) : tactic (expr × expr) := do
  let na ← a.to_rat
  let icα ← mk_instance_cache α
  let icβ ← mk_instance_cache β
  match match_sign b with
    | Sum.inl b => do
      let nc ← mk_instance_cache q(ℕ)
      let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
      let (icα, c, h) ← prove_pow a na icα b'
      let cr ← c
      let (icα, c', hc) ← prove_inv icα c cr
      pure (c', (expr.const neg []).mk_app [a, b, b', c, c', hb, h, hc])
    | Sum.inr ff => pure (one, expr.const zero [] a)
    | Sum.inr tt => do
      let nc ← mk_instance_cache q(ℕ)
      let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
      let (icα, c, h) ← prove_pow a na icα b'
      pure (c, (expr.const Pos []).mk_app [a, b, b', c, hb, h])
#align norm_num.prove_rpow' norm_num.prove_rpow'

open NNReal ENNReal

theorem nnrpow_pos (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c : ℝ≥0) (hb : b = b') (h : a ^ b' = c) :
    a ^ b = c := by rw [← h, hb, NNReal.rpow_nat_cast]
#align norm_num.nnrpow_pos NormNum.nnrpow_pos

theorem nnrpow_neg (a : ℝ≥0) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0) (hb : b = b') (h : a ^ b' = c)
    (hc : c⁻¹ = c') : a ^ (-b) = c' := by rw [← hc, ← h, hb, NNReal.rpow_neg, NNReal.rpow_nat_cast]
#align norm_num.nnrpow_neg NormNum.nnrpow_neg

theorem ennrpow_pos (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c) :
    a ^ b = c := by rw [← h, hb, ENNReal.rpow_nat_cast]
#align norm_num.ennrpow_pos NormNum.ennrpow_pos

theorem ennrpow_neg (a : ℝ≥0∞) (b : ℝ) (b' : ℕ) (c c' : ℝ≥0∞) (hb : b = b') (h : a ^ b' = c)
    (hc : c⁻¹ = c') : a ^ (-b) = c' := by
  rw [← hc, ← h, hb, ENNReal.rpow_neg, ENNReal.rpow_nat_cast]
#align norm_num.ennrpow_neg NormNum.ennrpow_neg

/-- Evaluate `complex.cpow a b` where `a` is a rational numeral and `b` is an integer. -/
unsafe def prove_cpow : expr → expr → tactic (expr × expr) :=
  prove_rpow' `` cpow_pos `` cpow_neg `` Complex.cpow_zero q(ℂ) q(ℂ) q((1 : ℂ))
#align norm_num.prove_cpow norm_num.prove_cpow

/-- Evaluate `nnreal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
unsafe def prove_nnrpow : expr → expr → tactic (expr × expr) :=
  prove_rpow' `` nnrpow_pos `` nnrpow_neg `` NNReal.rpow_zero q(ℝ≥0) q(ℝ) q((1 : ℝ≥0))
#align norm_num.prove_nnrpow norm_num.prove_nnrpow

/-- Evaluate `ennreal.rpow a b` where `a` is a rational numeral and `b` is an integer. -/
unsafe def prove_ennrpow : expr → expr → tactic (expr × expr) :=
  prove_rpow' `` ennrpow_pos `` ennrpow_neg `` ENNReal.rpow_zero q(ℝ≥0∞) q(ℝ) q((1 : ℝ≥0∞))
#align norm_num.prove_ennrpow norm_num.prove_ennrpow

/-- Evaluates expressions of the form `rpow a b`, `cpow a b` and `a ^ b` in the special case where
`b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
@[norm_num]
unsafe def eval_rpow_cpow : expr → tactic (expr × expr)
  | q(@Pow.pow _ _ Real.hasPow $(a) $(b)) => b.to_int >> prove_rpow a b
  | q(Real.rpow $(a) $(b)) => b.to_int >> prove_rpow a b
  | q(@Pow.pow _ _ Complex.hasPow $(a) $(b)) => b.to_int >> prove_cpow a b
  | q(Complex.cpow $(a) $(b)) => b.to_int >> prove_cpow a b
  | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_nnrpow a b
  | q(NNReal.rpow $(a) $(b)) => b.to_int >> prove_nnrpow a b
  | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => b.to_int >> prove_ennrpow a b
  | q(ENNReal.rpow $(a) $(b)) => b.to_int >> prove_ennrpow a b
  | _ => tactic.failed
#align norm_num.eval_rpow_cpow norm_num.eval_rpow_cpow

end NormNum

namespace Tactic

namespace Positivity

private theorem nnrpow_pos {a : ℝ≥0} (ha : 0 < a) (b : ℝ) : 0 < a ^ b :=
  NNReal.rpow_pos ha
#align tactic.positivity.nnrpow_pos tactic.positivity.nnrpow_pos

/-- Auxiliary definition for the `positivity` tactic to handle real powers of nonnegative reals. -/
unsafe def prove_nnrpow (a b : expr) : tactic strictness := do
  let strictness_a ← core a
  match strictness_a with
    | positive p => positive <$> mk_app `` nnrpow_pos [p, b]
    | _ => failed
#align tactic.positivity.prove_nnrpow tactic.positivity.prove_nnrpow

-- We already know `0 ≤ x` for all `x : ℝ≥0`
private theorem ennrpow_pos {a : ℝ≥0∞} {b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < a ^ b :=
  ENNReal.rpow_pos_of_nonneg ha hb.le
#align tactic.positivity.ennrpow_pos tactic.positivity.ennrpow_pos

/-- Auxiliary definition for the `positivity` tactic to handle real powers of extended nonnegative
reals. -/
unsafe def prove_ennrpow (a b : expr) : tactic strictness := do
  let strictness_a ← core a
  let strictness_b ← core b
  match strictness_a, strictness_b with
    | positive pa, positive pb => positive <$> mk_app `` ennrpow_pos [pa, pb]
    | positive pa, nonnegative pb => positive <$> mk_app `` ENNReal.rpow_pos_of_nonneg [pa, pb]
    | _, _ => failed
#align tactic.positivity.prove_ennrpow tactic.positivity.prove_ennrpow

-- We already know `0 ≤ x` for all `x : ℝ≥0∞`
end Positivity

open Positivity

/-- Extension for the `positivity` tactic: exponentiation by a real number is nonnegative when the
base is nonnegative and positive when the base is positive. -/
@[positivity]
unsafe def positivity_rpow : expr → tactic strictness
  | q(@Pow.pow _ _ Real.hasPow $(a) $(b)) => prove_rpow a b
  | q(Real.rpow $(a) $(b)) => prove_rpow a b
  | q(@Pow.pow _ _ NNReal.Real.hasPow $(a) $(b)) => prove_nnrpow a b
  | q(NNReal.rpow $(a) $(b)) => prove_nnrpow a b
  | q(@Pow.pow _ _ ENNReal.Real.hasPow $(a) $(b)) => prove_ennrpow a b
  | q(ENNReal.rpow $(a) $(b)) => prove_ennrpow a b
  | _ => failed
#align tactic.positivity_rpow tactic.positivity_rpow

end Tactic

