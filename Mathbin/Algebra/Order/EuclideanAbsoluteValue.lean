import Mathbin.Algebra.Order.AbsoluteValue 
import Mathbin.Algebra.EuclideanDomain

/-!
# Euclidean absolute values

This file defines a predicate `absolute_value.is_euclidean abv` stating the
absolute value is compatible with the Euclidean domain structure on its domain.

## Main definitions

 * `absolute_value.is_euclidean abv` is a predicate on absolute values on `R` mapping to `S`
    that preserve the order on `R` arising from the Euclidean domain structure.
 * `absolute_value.abs_is_euclidean` shows the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`, is euclidean.
-/


local infixl:50 " ≺ " => EuclideanDomain.R

namespace AbsoluteValue

section OrderedSemiring

variable{R S : Type _}[EuclideanDomain R][OrderedSemiring S]

variable(abv : AbsoluteValue R S)

/-- An absolute value `abv : R → S` is Euclidean if it is compatible with the
`euclidean_domain` structure on `R`, namely `abv` is strictly monotone with respect to the well
founded relation `≺` on `R`. -/
structure is_euclidean : Prop where 
  map_lt_map_iff' : ∀ {x y}, abv x < abv y ↔ x ≺ y

namespace IsEuclidean

variable{abv}

theorem map_lt_map_iff {x y : R} (h : abv.is_euclidean) : abv x < abv y ↔ x ≺ y :=
  map_lt_map_iff' h

attribute [simp] map_lt_map_iff

theorem sub_mod_lt (h : abv.is_euclidean) (a : R) {b : R} (hb : b ≠ 0) : abv (a % b) < abv b :=
  h.map_lt_map_iff.mpr (EuclideanDomain.mod_lt a hb)

end IsEuclidean

end OrderedSemiring

section Int

open Int

/-- `abs : ℤ → ℤ` is a Euclidean absolute value -/
protected theorem abs_is_euclidean : is_euclidean (AbsoluteValue.abs : AbsoluteValue ℤ ℤ) :=
  { map_lt_map_iff' :=
      fun x y =>
        show abs x < abs y ↔ nat_abs x < nat_abs y by 
          rw [abs_eq_nat_abs, abs_eq_nat_abs, coe_nat_lt] }

end Int

end AbsoluteValue

