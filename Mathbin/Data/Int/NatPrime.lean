import Mathbin.Data.Nat.Prime
import Mathbin.Data.Int.Basic

/-!
# Lemmas about nat.prime using `int`s
-/


open Nat

namespace Int

theorem not_prime_of_int_mul {a b : ℤ} {c : ℕ} (ha : 1 < a.nat_abs) (hb : 1 < b.nat_abs) (hc : (a*b) = (c : ℤ)) :
    ¬prime c :=
  not_prime_mul' (nat_abs_mul_nat_abs_eq hc) ha hb

end Int

