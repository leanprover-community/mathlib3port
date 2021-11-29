import Mathbin.Algebra.GcdMonoid.Basic 
import Mathbin.RingTheory.Coprime.Basic 
import Mathbin.RingTheory.Ideal.Basic 
import Mathbin.RingTheory.PrincipalIdealDomain

/-!
# Lemmas about Euclidean domains

Various about Euclidean domains are proved; all of them seem to be true
more generally for principal ideal domains, so these lemmas should
probably be reproved in more generality and this file perhaps removed?

## Tags

euclidean domain
-/


noncomputable theory

open_locale Classical

open EuclideanDomain Set Ideal

section GcdMonoid

variable {R : Type _} [EuclideanDomain R] [GcdMonoid R]

theorem left_div_gcd_ne_zero {p q : R} (hp : p ≠ 0) : p / GcdMonoid.gcd p q ≠ 0 :=
  by 
    obtain ⟨r, hr⟩ := GcdMonoid.gcd_dvd_left p q 
    obtain ⟨pq0, r0⟩ : GcdMonoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hp)
    rw [hr, mul_commₓ, mul_div_cancel _ pq0]
    exact r0

theorem right_div_gcd_ne_zero {p q : R} (hq : q ≠ 0) : q / GcdMonoid.gcd p q ≠ 0 :=
  by 
    obtain ⟨r, hr⟩ := GcdMonoid.gcd_dvd_right p q 
    obtain ⟨pq0, r0⟩ : GcdMonoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hq)
    rw [hr, mul_commₓ, mul_div_cancel _ pq0]
    exact r0

end GcdMonoid

namespace EuclideanDomain

/-- Create a `gcd_monoid` whose `gcd_monoid.gcd` matches `euclidean_domain.gcd`. -/
def GcdMonoid R [EuclideanDomain R] : GcdMonoid R :=
  { gcd := gcd, lcm := lcm, gcd_dvd_left := gcd_dvd_left, gcd_dvd_right := gcd_dvd_right,
    dvd_gcd := fun a b c => dvd_gcd,
    gcd_mul_lcm :=
      fun a b =>
        by 
          rw [EuclideanDomain.gcd_mul_lcm],
    lcm_zero_left := lcm_zero_left, lcm_zero_right := lcm_zero_right }

variable {α : Type _} [EuclideanDomain α] [DecidableEq α]

-- error in RingTheory.EuclideanDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem span_gcd {α} [euclidean_domain α] (x y : α) : «expr = »(span ({gcd x y} : set α), span ({x, y} : set α)) :=
begin
  letI [] [] [":=", expr euclidean_domain.gcd_monoid α],
  exact [expr span_gcd x y]
end

-- error in RingTheory.EuclideanDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gcd_is_unit_iff {α} [euclidean_domain α] {x y : α} : «expr ↔ »(is_unit (gcd x y), is_coprime x y) :=
begin
  letI [] [] [":=", expr euclidean_domain.gcd_monoid α],
  exact [expr gcd_is_unit_iff x y]
end

-- error in RingTheory.EuclideanDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_coprime_of_dvd
{α}
[euclidean_domain α]
{x y : α}
(z : «expr¬ »(«expr ∧ »(«expr = »(x, 0), «expr = »(y, 0))))
(H : ∀ z «expr ∈ » nonunits α, «expr ≠ »(z, 0) → «expr ∣ »(z, x) → «expr¬ »(«expr ∣ »(z, y))) : is_coprime x y :=
begin
  letI [] [] [":=", expr euclidean_domain.gcd_monoid α],
  exact [expr is_coprime_of_dvd x y z H]
end

-- error in RingTheory.EuclideanDomain: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem dvd_or_coprime
{α}
[euclidean_domain α]
(x y : α)
(h : irreducible x) : «expr ∨ »(«expr ∣ »(x, y), is_coprime x y) :=
begin
  letI [] [] [":=", expr euclidean_domain.gcd_monoid α],
  exact [expr dvd_or_coprime x y h]
end

end EuclideanDomain

