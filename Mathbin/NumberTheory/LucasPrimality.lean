import Mathbin.Data.Fintype.Basic 
import Mathbin.GroupTheory.OrderOfElement 
import Mathbin.Tactic.Zify 
import Mathbin.Data.Nat.Totient 
import Mathbin.Data.Zmod.Basic

/-!
# The Lucas test for primes.

This file implements the Lucas test for primes (not to be confused with the Lucas-Lehmer test for
Mersenne primes). A number `a` witnesses that `n` is prime if `a` has order `n-1` in the
multiplicative group of integers mod `n`. This is checked by verifying that `a^(n-1) = 1 (mod n)`
and `a^d ≠ 1 (mod n)` for any divisor `d | n - 1`. This test is the basis of the Pratt primality
certificate.

## TODO

- Bonus: Show the reverse implication i.e. if a number is prime then it has a Lucas witness.
  Use `units.is_cyclic` from `ring_theory/integral_domain` to show the group is cyclic.
- Write a tactic that uses this theorem to generate Pratt primality certificates
- Integrate Pratt primality certificates into the norm_num primality verifier

## Implementation notes

Note that the proof for `lucas_primality` relies on analyzing the multiplicative group
modulo `p`. Despite this, the theorem still holds vacuously for `p = 0` and `p = 1`: In these
cases, we can take `q` to be any prime and see that `hd` does not hold, since `a^((p-1)/q)` reduces
to `1`.
-/


-- error in NumberTheory.LucasPrimality: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If `a^(p-1) = 1 mod p`, but `a^((p-1)/q) ≠ 1 mod p` for all prime factors `q` of `p-1`, then `p`
is prime. This is true because `a` has order `p-1` in the multiplicative group mod `p`, so this
group must itself have order `p-1`, which only happens when `p` is prime.
-/
theorem lucas_primality
(p : exprℕ())
(a : zmod p)
(ha : «expr = »(«expr ^ »(a, «expr - »(p, 1)), 1))
(hd : ∀
 q : exprℕ(), q.prime → «expr ∣ »(q, «expr - »(p, 1)) → «expr ≠ »(«expr ^ »(a, «expr / »(«expr - »(p, 1), q)), 1)) : p.prime :=
begin
  have [ident h0] [":", expr «expr ≠ »(p, 0)] [],
  { rintro ["⟨", "⟩"],
    exact [expr hd 2 nat.prime_two (dvd_zero _) (pow_zero _)] },
  have [ident h1] [":", expr «expr ≠ »(p, 1)] [],
  { rintro ["⟨", "⟩"],
    exact [expr hd 2 nat.prime_two (dvd_zero _) (pow_zero _)] },
  have [ident hp1] [":", expr «expr < »(1, p)] [":=", expr lt_of_le_of_ne h0.bot_lt h1.symm],
  have [ident order_of_a] [":", expr «expr = »(order_of a, «expr - »(p, 1))] [],
  { apply [expr order_of_eq_of_pow_and_pow_div_prime _ ha hd],
    exact [expr tsub_pos_of_lt hp1] },
  haveI [ident fhp0] [":", expr fact «expr < »(0, p)] [":=", expr ⟨h0.bot_lt⟩],
  rw [expr nat.prime_iff_card_units] [],
  refine [expr le_antisymm (nat.card_units_zmod_lt_sub_one hp1) _],
  have [ident hp'] [":", expr «expr = »(«expr + »(«expr - »(p, 2), 1), «expr - »(p, 1))] [":=", expr tsub_add_eq_add_tsub hp1],
  let [ident a'] [":", expr units (zmod p)] [":=", expr units.mk_of_mul_eq_one a «expr ^ »(a, «expr - »(p, 2)) (by rw ["[", "<-", expr pow_succ, ",", expr hp', ",", expr ha, "]"] [])],
  calc
    «expr = »(«expr - »(p, 1), order_of a) : order_of_a.symm
    «expr = »(..., order_of a') : order_of_injective (units.coe_hom (zmod p)) units.ext a'
    «expr ≤ »(..., fintype.card (units (zmod p))) : order_of_le_card_univ
end

