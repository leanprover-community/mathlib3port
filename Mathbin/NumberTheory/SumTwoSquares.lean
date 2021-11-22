import Mathbin.NumberTheory.Zsqrtd.GaussianInt

/-!
# Sums of two squares

Proof of Fermat's theorem on the sum of two squares. Every prime congruent to 1 mod 4 is the sum
of two squares
-/


open GaussianInt PrincipalIdealRing

namespace Nat

namespace Prime

/-- **Fermat's theorem on the sum of two squares**. Every prime congruent to 1 mod 4 is the sum
of two squares. -/
theorem sq_add_sq (p : ℕ) [hp : _root_.fact p.prime] (hp1 : p % 4 = 1) : ∃ a b : ℕ, ((a^2)+b^2) = p :=
  by 
    apply sq_add_sq_of_nat_prime_of_not_irreducible p 
    rw [PrincipalIdealRing.irreducible_iff_prime, prime_iff_mod_four_eq_three_of_nat_prime p, hp1]
    normNum

end Prime

end Nat

