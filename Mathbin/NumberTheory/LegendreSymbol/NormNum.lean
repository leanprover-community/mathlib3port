/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathbin.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# A `norm_num` extension for Jacobi and Legendre symbols

We extend the `tactic.interactive.norm_num` tactic so that it can be used to provably compute
the value of the Jacobi symbol `J(a | b)` or the Legendre symbol `legendre_sym p a` when
the arguments are numerals.

## Implementation notes

We use the Law of Quadratic Reciprocity for the Jacobi symbol to compute the value of `J(a | b)`
efficiently, roughly comparable in effort with the euclidean algorithm for the computation
of the gcd of `a` and `b`. More precisely, the computation is done in the following steps.

* Use `J(a | 0) = 1` (an artifact of the definition) and `J(a | 1) = 1` to deal
  with corner cases.

* Use `J(a | b) = J(a % b | b)` to reduce to the case that `a` is a natural number.
  We define a version of the Jacobi symbol restricted to natural numbers for use in
  the following steps; see `norm_num.jacobi_sym_nat`. (But we'll continue to write `J(a | b)`
  in this description.)

* Remove powers of two from `b`. This is done via `J(2a | 2b) = 0` and
  `J(2a+1 | 2b) = J(2a+1 | b)` (another artifact of the definition).

* Now `0 ≤ a < b` and `b` is odd. If `b = 1`, then the value is `1`.
  If `a = 0` (and `b > 1`), then the value is `0`. Otherwise, we remove powers of two from `a`
  via `J(4a | b) = J(a | b)` and `J(2a | b) = ±J(a | b)`, where the sign is determined
  by the residue class of `b` mod 8, to reduce to `a` odd.

* Once `a` is odd, we use Quadratic Reciprocity (QR) in the form
  `J(a | b) = ±J(b % a | a)`, where the sign is determined by the residue classes
  of `a` and `b` mod 4. We are then back in the previous case.

We provide customized versions of these results for the various reduction steps,
where we encode the residue classes mod 2, mod 4, or mod 8 by using terms like
`bit1 (bit0 a)`. In this way, the only divisions we have to compute and prove
are the ones occurring in the use of QR above.
-/


section Lemmas

namespace NormNum

/-- The Jacobi symbol restricted to natural numbers in both arguments. -/
def jacobiSymNat (a b : ℕ) : ℤ :=
  jacobiSym a b

/-!
### API Lemmas

We repeat part of the API for `jacobi_sym` with `norm_num.jacobi_sym_nat` and without implicit
arguments, in a form that is suitable for constructing proofs in `norm_num`.
-/


/-- Base cases: `b = 0`, `b = 1`, `a = 0`, `a = 1`. -/
theorem jacobiSymNat.zero_right (a : ℕ) : jacobiSymNat a 0 = 1 := by rwa [jacobi_sym_nat, jacobiSym.zero_right]

theorem jacobiSymNat.one_right (a : ℕ) : jacobiSymNat a 1 = 1 := by rwa [jacobi_sym_nat, jacobiSym.one_right]

theorem jacobiSymNat.zero_left_even (b : ℕ) (hb : b ≠ 0) : jacobiSymNat 0 (bit0 b) = 0 := by
  rw [jacobi_sym_nat, Nat.cast_zeroₓ, jacobiSym.zero_left (Nat.one_lt_bit0 hb)]

theorem jacobiSymNat.zero_left_odd (b : ℕ) (hb : b ≠ 0) : jacobiSymNat 0 (bit1 b) = 0 := by
  rw [jacobi_sym_nat, Nat.cast_zeroₓ, jacobiSym.zero_left (Nat.one_lt_bit1 hb)]

theorem jacobiSymNat.one_left_even (b : ℕ) : jacobiSymNat 1 (bit0 b) = 1 := by
  rw [jacobi_sym_nat, Nat.cast_oneₓ, jacobiSym.one_left]

theorem jacobiSymNat.one_left_odd (b : ℕ) : jacobiSymNat 1 (bit1 b) = 1 := by
  rw [jacobi_sym_nat, Nat.cast_oneₓ, jacobiSym.one_left]

/-- Turn a Legendre symbol into a Jacobi symbol. -/
theorem LegendreSym.to_jacobi_sym (p : ℕ) (pp : Fact p.Prime) (a r : ℤ) (hr : jacobiSym a p = r) :
    legendreSym p a = r := by rwa [@legendreSym.to_jacobi_sym p pp a]

/-- The value depends only on the residue class of `a` mod `b`. -/
theorem JacobiSym.mod_left (a : ℤ) (b ab' : ℕ) (ab r b' : ℤ) (hb' : (b : ℤ) = b') (hab : a % b' = ab)
    (h : (ab' : ℤ) = ab) (hr : jacobiSymNat ab' b = r) : jacobiSym a b = r := by
  rw [← hr, jacobi_sym_nat, jacobiSym.mod_left, hb', hab, ← h]

theorem jacobiSymNat.mod_left (a b ab : ℕ) (r : ℤ) (hab : a % b = ab) (hr : jacobiSymNat ab b = r) :
    jacobiSymNat a b = r := by
  rw [← hr, jacobi_sym_nat, jacobi_sym_nat, _root_.jacobi_sym.mod_left a b, ← hab]
  rfl

/-- The symbol vanishes when both entries are even (and `b ≠ 0`). -/
theorem jacobiSymNat.even_even (a b : ℕ) (hb₀ : b ≠ 0) : jacobiSymNat (bit0 a) (bit0 b) = 0 := by
  refine' jacobi_sym.eq_zero_iff.mpr ⟨Nat.bit0_ne_zero hb₀, fun hf => _⟩
  have h : 2 ∣ (bit0 a).gcd (bit0 b) := Nat.dvd_gcdₓ two_dvd_bit0 two_dvd_bit0
  change 2 ∣ (bit0 a : ℤ).gcd (bit0 b) at h
  rw [← Nat.cast_bit0, ← Nat.cast_bit0, hf, ← even_iff_two_dvd] at h
  exact Nat.not_even_one h

/-- When `a` is odd and `b` is even, we can replace `b` by `b / 2`. -/
theorem jacobiSymNat.odd_even (a b : ℕ) (r : ℤ) (hr : jacobiSymNat (bit1 a) b = r) :
    jacobiSymNat (bit1 a) (bit0 b) = r := by
  have ha : legendreSym 2 (bit1 a) = 1 := by
    simp only [legendreSym, quadratic_char_apply, quadratic_char_fun_one, Int.cast_bit1, CharTwo.bit1_eq_one,
      Pi.one_apply]
  cases' eq_or_ne b 0 with hb hb
  · rw [← hr, hb, jacobi_sym_nat.zero_right]
    
  · haveI : NeZero b := ⟨hb⟩
    -- for `jacobi_sym.mul_right`
    rwa [bit0_eq_two_mul b, jacobi_sym_nat, jacobiSym.mul_right, ← _root_.legendre_sym.to_jacobi_sym, Nat.cast_bit1, ha,
      one_mulₓ]
    

/-- If `a` is divisible by `4` and `b` is odd, then we can remove the factor `4` from `a`. -/
theorem jacobiSymNat.double_even (a b : ℕ) (r : ℤ) (hr : jacobiSymNat a (bit1 b) = r) :
    jacobiSymNat (bit0 (bit0 a)) (bit1 b) = r := by
  have : ((2 : ℕ) : ℤ).gcd (bit1 b : ℕ) = 1 := by
    rw [Int.coe_nat_gcd, Nat.bit1_eq_succ_bit0, bit0_eq_two_mul b, Nat.succ_eq_add_one, Nat.gcd_mul_left_add_right,
      Nat.gcd_one_rightₓ]
  rwa [bit0_eq_two_mul a, bit0_eq_two_mul (2 * a), ← mul_assoc, ← pow_two, jacobi_sym_nat, Nat.cast_mulₓ, Nat.cast_powₓ,
    jacobiSym.mul_left, jacobiSym.sq_one' this, one_mulₓ]

/-- If `a` is even and `b` is odd, then we can remove a factor `2` from `a`,
but we may have to change the sign, depending on `b % 8`.
We give one version for each of the four odd residue classes mod `8`. -/
theorem jacobiSymNat.even_odd₁ (a b : ℕ) (r : ℤ) (hr : jacobiSymNat a (bit1 (bit0 (bit0 b))) = r) :
    jacobiSymNat (bit0 a) (bit1 (bit0 (bit0 b))) = r := by
  have hb : bit1 (bit0 (bit0 b)) % 8 = 1 := by rw [Nat.bit1_mod_bit0, Nat.bit0_mod_bit0, Nat.bit0_mod_two]
  rw [jacobi_sym_nat, bit0_eq_two_mul a, Nat.cast_mulₓ, jacobiSym.mul_left, Nat.cast_two, jacobiSym.at_two (odd_bit1 _),
    Zmod.χ₈_nat_mod_eight, hb]
  norm_num
  exact hr

theorem jacobiSymNat.even_odd₇ (a b : ℕ) (r : ℤ) (hr : jacobiSymNat a (bit1 (bit1 (bit1 b))) = r) :
    jacobiSymNat (bit0 a) (bit1 (bit1 (bit1 b))) = r := by
  have hb : bit1 (bit1 (bit1 b)) % 8 = 7 := by rw [Nat.bit1_mod_bit0, Nat.bit1_mod_bit0, Nat.bit1_mod_two]
  rw [jacobi_sym_nat, bit0_eq_two_mul a, Nat.cast_mulₓ, jacobiSym.mul_left, Nat.cast_two, jacobiSym.at_two (odd_bit1 _),
    Zmod.χ₈_nat_mod_eight, hb]
  norm_num
  exact hr

theorem jacobiSymNat.even_odd₃ (a b : ℕ) (r : ℤ) (hr : jacobiSymNat a (bit1 (bit1 (bit0 b))) = r) :
    jacobiSymNat (bit0 a) (bit1 (bit1 (bit0 b))) = -r := by
  have hb : bit1 (bit1 (bit0 b)) % 8 = 3 := by rw [Nat.bit1_mod_bit0, Nat.bit1_mod_bit0, Nat.bit0_mod_two]
  rw [jacobi_sym_nat, bit0_eq_two_mul a, Nat.cast_mulₓ, jacobiSym.mul_left, Nat.cast_two, jacobiSym.at_two (odd_bit1 _),
    Zmod.χ₈_nat_mod_eight, hb]
  norm_num
  exact hr

theorem jacobiSymNat.even_odd₅ (a b : ℕ) (r : ℤ) (hr : jacobiSymNat a (bit1 (bit0 (bit1 b))) = r) :
    jacobiSymNat (bit0 a) (bit1 (bit0 (bit1 b))) = -r := by
  have hb : bit1 (bit0 (bit1 b)) % 8 = 5 := by rw [Nat.bit1_mod_bit0, Nat.bit0_mod_bit0, Nat.bit1_mod_two]
  rw [jacobi_sym_nat, bit0_eq_two_mul a, Nat.cast_mulₓ, jacobiSym.mul_left, Nat.cast_two, jacobiSym.at_two (odd_bit1 _),
    Zmod.χ₈_nat_mod_eight, hb]
  norm_num
  exact hr

/-- Use quadratic reciproity to reduce to smaller `b`. -/
theorem jacobiSymNat.qr₁ (a b : ℕ) (r : ℤ) (hr : jacobiSymNat (bit1 b) (bit1 (bit0 a)) = r) :
    jacobiSymNat (bit1 (bit0 a)) (bit1 b) = r := by
  have ha : bit1 (bit0 a) % 4 = 1 := by rw [Nat.bit1_mod_bit0, Nat.bit0_mod_two]
  have hb := Nat.bit1_mod_two
  rwa [jacobi_sym_nat, jacobiSym.quadratic_reciprocity_one_mod_four ha (nat.odd_iff.mpr hb)]

theorem jacobiSymNat.qr₁_mod (a b ab : ℕ) (r : ℤ) (hab : bit1 b % bit1 (bit0 a) = ab)
    (hr : jacobiSymNat ab (bit1 (bit0 a)) = r) : jacobiSymNat (bit1 (bit0 a)) (bit1 b) = r :=
  jacobiSymNat.qr₁ _ _ _ <| jacobiSymNat.mod_left _ _ ab r hab hr

theorem jacobiSymNat.qr₁' (a b : ℕ) (r : ℤ) (hr : jacobiSymNat (bit1 (bit0 b)) (bit1 a) = r) :
    jacobiSymNat (bit1 a) (bit1 (bit0 b)) = r := by
  have hb : bit1 (bit0 b) % 4 = 1 := by rw [Nat.bit1_mod_bit0, Nat.bit0_mod_two]
  have ha := Nat.bit1_mod_two
  rwa [jacobi_sym_nat, ← jacobiSym.quadratic_reciprocity_one_mod_four hb (nat.odd_iff.mpr ha)]

theorem jacobiSymNat.qr₁'_mod (a b ab : ℕ) (r : ℤ) (hab : bit1 (bit0 b) % bit1 a = ab)
    (hr : jacobiSymNat ab (bit1 a) = r) : jacobiSymNat (bit1 a) (bit1 (bit0 b)) = r :=
  jacobiSymNat.qr₁' _ _ _ <| jacobiSymNat.mod_left _ _ ab r hab hr

theorem jacobiSymNat.qr₃ (a b : ℕ) (r : ℤ) (hr : jacobiSymNat (bit1 (bit1 b)) (bit1 (bit1 a)) = r) :
    jacobiSymNat (bit1 (bit1 a)) (bit1 (bit1 b)) = -r := by
  have hb : bit1 (bit1 b) % 4 = 3 := by rw [Nat.bit1_mod_bit0, Nat.bit1_mod_two]
  have ha : bit1 (bit1 a) % 4 = 3 := by rw [Nat.bit1_mod_bit0, Nat.bit1_mod_two]
  rwa [jacobi_sym_nat, jacobiSym.quadratic_reciprocity_three_mod_four ha hb, neg_inj]

theorem jacobiSymNat.qr₃_mod (a b ab : ℕ) (r : ℤ) (hab : bit1 (bit1 b) % bit1 (bit1 a) = ab)
    (hr : jacobiSymNat ab (bit1 (bit1 a)) = r) : jacobiSymNat (bit1 (bit1 a)) (bit1 (bit1 b)) = -r :=
  jacobiSymNat.qr₃ _ _ _ <| jacobiSymNat.mod_left _ _ ab r hab hr

end NormNum

end Lemmas

section Evaluation

/-!
### Certified evaluation of the Jacobi symbol

The following functions recursively evaluate a Jacobi symbol and construct the
corresponding proof term.
-/


namespace NormNum

open Tactic

/-- This evaluates `r := jacobi_sym_nat a b` recursively using quadratic reciprocity
and produces a proof term for the equality, assuming that `a < b` and `b` is odd. -/
unsafe def prove_jacobi_sym_odd :
    instance_cache → instance_cache → expr → expr → tactic (instance_cache × instance_cache × expr × expr)
  | zc, nc, ea, eb => do
    match match_numeral eb with
      |
      match_numeral_result.one =>-- `b = 1`, result is `1`
          pure
          (zc, nc, quote.1 (1 : ℤ), (quote.1 jacobiSymNat.one_right).mk_app [ea])
      | match_numeral_result.bit1 eb₁ => do
        -- `b > 1` (recall that `b` is odd)
          match match_numeral ea with
          | match_numeral_result.zero => do
            let b
              ←-- `a = 0`, result is `0`
                eb₁
            let (nc, phb₀) ← prove_ne nc eb₁ (quote.1 (0 : ℕ)) b 0
            -- proof of `b ≠ 0`
                pure
                (zc, nc, quote.1 (0 : ℤ), (quote.1 jacobiSymNat.zero_left_odd).mk_app [eb₁, phb₀])
          | match_numeral_result.one => do
            -- `a = 1`, result is `1`
                pure
                (zc, nc, quote.1 (1 : ℤ), (quote.1 jacobiSymNat.one_left_odd).mk_app [eb₁])
          | match_numeral_result.bit0 ea₁ => do
            -- `a` is even; check if divisible by `4`
              match match_numeral ea₁ with
              | match_numeral_result.bit0 ea₂ => do
                let (zc, nc, er, p) ← prove_jacobi_sym_odd zc nc ea₂ eb
                -- compute `jacobi_sym_nat (a / 4) b`
                    pure
                    (zc, nc, er, (quote.1 jacobiSymNat.double_even).mk_app [ea₂, eb₁, er, p])
              | _ => do
                let-- reduce to `a / 2`; need to consider `b % 8`
                  (zc, nc, er, p)
                  ← prove_jacobi_sym_odd zc nc ea₁ eb
                -- compute `jacobi_sym_nat (a / 2) b`
                  match match_numeral eb₁ with
                  |-- | match_numeral_result.zero := -- `b = 1`, not reached
                    match_numeral_result.one =>
                    do
                    let r
                      ←-- `b = 3`
                        er
                    let (zc, er') ← zc (-r)
                    pure (zc, nc, er', (quote.1 jacobiSymNat.even_odd₃).mk_app [ea₁, quote.1 (0 : ℕ), er, p])
                  | match_numeral_result.bit0 eb₂ => do
                    -- `b % 4 = 1`
                      match match_numeral eb₂ with
                      |-- | match_numeral_result.zero := -- not reached
                        match_numeral_result.one =>
                        do
                        let r
                          ←-- `b = 5`
                            er
                        let (zc, er') ← zc (-r)
                        pure (zc, nc, er', (quote.1 jacobiSymNat.even_odd₅).mk_app [ea₁, quote.1 (0 : ℕ), er, p])
                      | match_numeral_result.bit0 eb₃ => do
                        -- `b % 8 = 1`
                            pure
                            (zc, nc, er, (quote.1 jacobiSymNat.even_odd₁).mk_app [ea₁, eb₃, er, p])
                      | match_numeral_result.bit1 eb₃ => do
                        let r
                          ←-- `b % 8 = 5`
                            er
                        let (zc, er') ← zc (-r)
                        pure (zc, nc, er', (quote.1 jacobiSymNat.even_odd₅).mk_app [ea₁, eb₃, er, p])
                      | _ => failed
                  | match_numeral_result.bit1 eb₂ => do
                    -- `b % 4 = 3`
                      match match_numeral eb₂ with
                      |-- | match_numeral_result.zero := -- not reached
                        match_numeral_result.one =>
                        do
                        -- `b = 7`
                            pure
                            (zc, nc, er, (quote.1 jacobiSymNat.even_odd₇).mk_app [ea₁, quote.1 (0 : ℕ), er, p])
                      | match_numeral_result.bit0 eb₃ => do
                        let r
                          ←-- `b % 8 = 3`
                            er
                        let (zc, er') ← zc (-r)
                        pure (zc, nc, er', (quote.1 jacobiSymNat.even_odd₃).mk_app [ea₁, eb₃, er, p])
                      | match_numeral_result.bit1 eb₃ => do
                        -- `b % 8 = 7`
                            pure
                            (zc, nc, er, (quote.1 jacobiSymNat.even_odd₇).mk_app [ea₁, eb₃, er, p])
                      | _ => failed
                  | _ => failed
          | match_numeral_result.bit1 ea₁ => do
            let-- `a` is odd
              -- use Quadratic Reciprocity; look at `a` and `b` mod `4`
              (nc, bma, phab)
              ← prove_div_mod nc eb ea tt
            let-- compute `b % a`
              (zc, nc, er, p)
              ← prove_jacobi_sym_odd zc nc bma ea
            -- compute `jacobi_sym_nat (b % a) a`
              match match_numeral ea₁ with
              |-- | match_numeral_result.zero :=  -- `a = 1`, not reached
                match_numeral_result.one =>
                do
                -- `a = 3`; need to consider `b`
                  match match_numeral eb₁ with
                  |-- | match_numeral_result.zero := -- `b = 1`, not reached
                      -- | match_numeral_result.one := -- `b = 3`, not reached, since `a < b`
                      match_numeral_result.bit0
                      eb₂ =>
                    do
                    -- `b % 4 = 1`
                        pure
                        (zc, nc, er, (quote.1 jacobiSymNat.qr₁'_mod).mk_app [ea₁, eb₂, bma, er, phab, p])
                  | match_numeral_result.bit1 eb₂ => do
                    let r
                      ←-- `b % 4 = 3`
                        er
                    let (zc, er') ← zc (-r)
                    pure (zc, nc, er', (quote.1 jacobiSymNat.qr₃_mod).mk_app [quote.1 (0 : ℕ), eb₂, bma, er, phab, p])
                  | _ => failed
              | match_numeral_result.bit0 ea₂ => do
                -- `a % 4 = 1`
                    pure
                    (zc, nc, er, (quote.1 jacobiSymNat.qr₁_mod).mk_app [ea₂, eb₁, bma, er, phab, p])
              | match_numeral_result.bit1 ea₂ => do
                -- `a % 4 = 3`; need to consider `b`
                  match match_numeral eb₁ with
                  |-- | match_numeral_result.zero := do -- `b = 1`, not reached
                      -- | match_numeral_result.one := do -- `b = 3`, not reached, since `a < b`
                      match_numeral_result.bit0
                      eb₂ =>
                    do
                    -- `b % 4 = 1`
                        pure
                        (zc, nc, er, (quote.1 jacobiSymNat.qr₁'_mod).mk_app [ea₁, eb₂, bma, er, phab, p])
                  | match_numeral_result.bit1 eb₂ => do
                    let r
                      ←-- `b % 4 = 3`
                        er
                    let (zc, er') ← zc (-r)
                    pure (zc, nc, er', (quote.1 jacobiSymNat.qr₃_mod).mk_app [ea₂, eb₂, bma, er, phab, p])
                  | _ => failed
              | _ => failed
          | _ => failed
      | _ => failed

/-- This evaluates `r := jacobi_sym_nat a b` and produces a proof term for the equality
by removing powers of `2` from `b` and then calling `prove_jacobi_sym_odd`. -/
unsafe def prove_jacobi_sym_nat :
    instance_cache → instance_cache → expr → expr → tactic (instance_cache × instance_cache × expr × expr)
  | zc, nc, ea, eb => do
    match match_numeral eb with
      |
      match_numeral_result.zero =>-- `b = 0`, result is `1`
          pure
          (zc, nc, quote.1 (1 : ℤ), (quote.1 jacobiSymNat.zero_right).mk_app [ea])
      |
      match_numeral_result.one =>-- `b = 1`, result is `1`
          pure
          (zc, nc, quote.1 (1 : ℤ), (quote.1 jacobiSymNat.one_right).mk_app [ea])
      |
      match_numeral_result.bit0 eb₁ =>-- `b` is even and nonzero
        match match_numeral ea with
        | match_numeral_result.zero => do
          let b
            ←-- `a = 0`, result is `0`
              eb₁
          let (nc, phb₀) ← prove_ne nc eb₁ (quote.1 (0 : ℕ)) b 0
          -- proof of `b ≠ 0`
              pure
              (zc, nc, quote.1 (0 : ℤ), (quote.1 jacobiSymNat.zero_left_even).mk_app [eb₁, phb₀])
        | match_numeral_result.one => do
          -- `a = 1`, result is `1`
              pure
              (zc, nc, quote.1 (1 : ℤ), (quote.1 jacobiSymNat.one_left_even).mk_app [eb₁])
        | match_numeral_result.bit0 ea₁ => do
          let b
            ←-- `a` is even, result is `0`
              eb₁
          let (nc, phb₀) ← prove_ne nc eb₁ (quote.1 (0 : ℕ)) b 0
          let-- proof of `b ≠ 0`
          er : expr := quote.1 (0 : ℤ)
          pure (zc, nc, er, (quote.1 jacobiSymNat.even_even).mk_app [ea₁, eb₁, phb₀])
        | match_numeral_result.bit1 ea₁ => do
          let-- `a` is odd, reduce to `b / 2`
            (zc, nc, er, p)
            ← prove_jacobi_sym_nat zc nc ea eb₁
          pure (zc, nc, er, (quote.1 jacobiSymNat.odd_even).mk_app [ea₁, eb₁, er, p])
        | _ => failed
      | match_numeral_result.bit1 eb₁ => do
        let a
          ←-- `b` is odd
            ea
        let b ← eb
        if b ≤ a then do
            let-- reduce to `jacobi_sym_nat (a % b) b`
              (nc, amb, phab)
              ← prove_div_mod nc ea eb tt
            let-- compute `a % b`
              (zc, nc, er, p)
              ← prove_jacobi_sym_odd zc nc amb eb
            -- compute `jacobi_sym_nat (a % b) b`
                pure
                (zc, nc, er, (quote.1 jacobiSymNat.mod_left).mk_app [ea, eb, amb, er, phab, p])
          else prove_jacobi_sym_odd zc nc ea eb
      | _ => failed

/-- This evaluates `r := jacobi_sym a b` and produces a proof term for the equality.
This is done by reducing to `r := jacobi_sym_nat (a % b) b`. -/
unsafe def prove_jacobi_sym :
    instance_cache → instance_cache → expr → expr → tactic (instance_cache × instance_cache × expr × expr)
  | zc, nc, ea, eb => do
    match match_numeral eb with
      |-- deal with simple cases right away
        match_numeral_result.zero =>
        pure (zc, nc, quote.1 (1 : ℤ), (quote.1 jacobiSym.zero_right).mk_app [ea])
      | match_numeral_result.one => pure (zc, nc, quote.1 (1 : ℤ), (quote.1 jacobiSym.one_right).mk_app [ea])
      | _ => do
        let b
          ←-- Now `1 < b`. Compute `jacobi_sym_nat (a % b) b` instead.
            eb
        let (zc, eb') ← zc (b : ℤ)
        let-- Get the proof that `(b : ℤ) = b'` (where `eb'` is the numeral representing `b'`).
          -- This is important to avoid inefficient matching between the two.
          (zc, nc, eb₁, pb')
          ← prove_nat_uncast zc nc eb'
        let (zc, amb, phab) ← prove_div_mod zc ea eb' tt
        let-- compute `a % b`
          (zc, nc, amb', phab')
          ← prove_nat_uncast zc nc amb
        let-- `a % b` as a natural number
          (zc, nc, er, p)
          ← prove_jacobi_sym_nat zc nc amb' eb₁
        -- compute `jacobi_sym_nat (a % b) b`
            pure
            (zc, nc, er, (quote.1 JacobiSym.mod_left).mk_app [ea, eb₁, amb', amb, er, eb', pb', phab, phab', p])

end NormNum

end Evaluation

section Tactic

/-!
### The `norm_num` plug-in
-/


namespace Tactic

namespace NormNum

/-- This is the `norm_num` plug-in that evaluates Jacobi and Legendre symbols. -/
@[norm_num]
unsafe def eval_jacobi_sym : expr → tactic (expr × expr)
  | quote.1 (jacobiSym (%%ₓea) (%%ₓeb)) => do
    let zc
      ←-- Jacobi symbol
          mk_instance_cache
          (quote.1 ℤ)
    let nc ← mk_instance_cache (quote.1 ℕ)
    (Prod.snd ∘ Prod.snd) <$> norm_num.prove_jacobi_sym zc nc ea eb
  | quote.1 (NormNum.jacobiSymNat (%%ₓea) (%%ₓeb)) => do
    let zc
      ←-- Jacobi symbol on natural numbers
          mk_instance_cache
          (quote.1 ℤ)
    let nc ← mk_instance_cache (quote.1 ℕ)
    (Prod.snd ∘ Prod.snd) <$> norm_num.prove_jacobi_sym_nat zc nc ea eb
  | quote.1 (@legendreSym (%%ₓep) (%%ₓinst) (%%ₓea)) => do
    let zc
      ←-- Legendre symbol
          mk_instance_cache
          (quote.1 ℤ)
    let nc ← mk_instance_cache (quote.1 ℕ)
    let (zc, nc, er, pf) ← norm_num.prove_jacobi_sym zc nc ea ep
    pure (er, (quote.1 NormNum.LegendreSym.to_jacobi_sym).mk_app [ep, inst, ea, er, pf])
  | _ => failed

end NormNum

end Tactic

end Tactic

