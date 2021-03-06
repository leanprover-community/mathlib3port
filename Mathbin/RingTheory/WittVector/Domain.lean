/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathbin.RingTheory.WittVector.Identities

/-!

# Witt vectors over a domain

This file builds to the proof `witt_vector.is_domain`,
an instance that says if `R` is an integral domain, then so is `π R`.
It depends on the API around iterated applications
of `witt_vector.verschiebung` and `witt_vector.frobenius`
found in `identities.lean`.

The [proof sketch](https://math.stackexchange.com/questions/4117247/ring-of-witt-vectors-over-an-integral-domain/4118723#4118723)
goes as follows:
any nonzero $x$ is an iterated application of $V$
to some vector $w_x$ whose 0th component is nonzero (`witt_vector.verschiebung_nonzero`).
Known identities (`witt_vector.iterate_verschiebung_mul`) allow us to transform
the product of two such $x$ and $y$
to the form $V^{m+n}\left(F^n(w_x) \cdot F^m(w_y)\right)$,
the 0th component of which must be nonzero.

## Main declarations

* `witt_vector.iterate_verschiebung_mul_coeff` : an identity from [Haze09]
* `witt_vector.is_domain`

-/


noncomputable section

open Classical

namespace WittVector

open Function

variable {p : β} {R : Type _}

-- mathport name: Β«exprπΒ»
local notation "π" => WittVector p

/-!
## The `shift` operator
-/


/-- `witt_vector.verschiebung` translates the entries of a Witt vector upward, inserting 0s in the gaps.
`witt_vector.shift` does the opposite, removing the first entries.
This is mainly useful as an auxiliary construction for `witt_vector.verschiebung_nonzero`.
-/
-- type as `\bbW`
def shift (x : π R) (n : β) : π R :=
  mk p fun i => x.coeff (n + i)

theorem shift_coeff (x : π R) (n k : β) : (x.shift n).coeff k = x.coeff (n + k) :=
  rfl

variable [hp : Fact p.Prime] [CommRingβ R]

include hp

theorem verschiebung_shift (x : π R) (k : β) (h : β, β i < k + 1, β, x.coeff i = 0) :
    verschiebung (x.shift k.succ) = x.shift k := by
  ext β¨jβ©
  Β· rw [verschiebung_coeff_zero, shift_coeff, h]
    apply Nat.lt_succ_selfβ
    
  Β· simp only [β verschiebung_coeff_succ, β shift]
    congr 1
    rw [Nat.add_succ, add_commβ, Nat.add_succ, add_commβ]
    

theorem eq_iterate_verschiebung {x : π R} {n : β} (h : β, β i < n, β, x.coeff i = 0) :
    x = (verschiebung^[n]) (x.shift n) := by
  induction' n with k ih
  Β· cases x <;> simp [β shift]
    
  Β· dsimp'
    rw [verschiebung_shift]
    Β· exact ih fun i hi => h _ (hi.trans (Nat.lt_succ_selfβ _))
      
    Β· exact h
      
    

theorem verschiebung_nonzero {x : π R} (hx : x β  0) : β n : β, β x' : π R, x'.coeff 0 β  0 β§ x = (verschiebung^[n]) x' :=
  by
  have hex : β k : β, x.coeff k β  0 := by
    by_contra' hall
    apply hx
    ext i
    simp only [β hall, β zero_coeff]
  let n := Nat.findβ hex
  use n, x.shift n
  refine' β¨Nat.find_specβ hex, eq_iterate_verschiebung fun i hi => not_not.mp _β©
  exact Nat.find_minβ hex hi

/-!
## Witt vectors over a domain

If `R` is an integral domain, then so is `π R`.
This argument is adapted from
<https://math.stackexchange.com/questions/4117247/ring-of-witt-vectors-over-an-integral-domain/4118723#4118723>.
-/


instance [CharP R p] [NoZeroDivisors R] : NoZeroDivisors (π R) :=
  β¨fun x y => by
    contrapose!
    rintro β¨ha, hbβ©
    rcases verschiebung_nonzero ha with β¨na, wa, hwa0, rflβ©
    rcases verschiebung_nonzero hb with β¨nb, wb, hwb0, rflβ©
    refine' ne_of_apply_ne (fun x => x.coeff (na + nb)) _
    rw [iterate_verschiebung_mul_coeff, zero_coeff]
    refine' mul_ne_zero (pow_ne_zero _ hwa0) (pow_ne_zero _ hwb0)β©

instance [CharP R p] [IsDomain R] : IsDomain (π R) :=
  { WittVector.no_zero_divisors, WittVector.nontrivial with }

end WittVector

