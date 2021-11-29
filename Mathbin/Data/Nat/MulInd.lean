import Mathbin.NumberTheory.Padics.PadicNorm

/-!
# Multiplicative induction principles for ℕ

This file provides three (closely linked) induction principles for ℕ, commonly used for proofs
about multiplicative functions, such as the totient function and the Möbius function.

## Main definitions

* `nat.rec_on_prime_pow`: Given `P 0, P 1` and a way to extend `P a` to `P (p ^ k * a)`, you can
  define `P` for all natural numbers.
* `nat.rec_on_prime_coprime`: Given `P 0`, `P (p ^ k)` for all `p` prime, and a way to extend `P a`
  and `P b` to `P (a * b)` when `a, b` are coprime, you can define `P` for all natural numbers.
* `nat.rec_on_pos_prime_coprime`: Given `P 0`, `P 1`, and `P (p ^ k)` for positive prime powers, and
  a way to extend `P a` and `P b` to `P (a * b)` when `a, b` are coprime, you can define `P` for all
  natural numbers.
* `nat.rec_on_mul`: Given `P 0`, `P 1`, `P p` for all primes, and a proof that
  you can extend `P a` and `P b` to `P (a * b)`, you can define `P` for all natural numbers.

## Implementation notes

The proofs use `padic_val_nat`; however, we have `padic_val_nat p = nat.log p $ nat.gcd k (p ^ k)`
for any `p ∣ k`, which requires far less imports - the API isn't there though; however, this is why
it's in `data` even though we import `number_theory`; it's not a particularly deep theorem.

## TODO:

Extend these results to any `normalization_monoid` with unique factorization.

-/


namespace Nat

-- error in Data.Nat.MulInd: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given `P 0, P 1` and a way to extend `P a` to `P (p ^ k * a)`,
you can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def rec_on_prime_pow
{P : exprℕ() → Sort*}
(h0 : P 0)
(h1 : P 1)
(h : ∀
 a p n : exprℕ(), p.prime → «expr¬ »(«expr ∣ »(p, a)) → P a → P «expr * »(«expr ^ »(p, n), a)) : ∀ a : exprℕ(), P a :=
λ a, «expr $ »(nat.strong_rec_on a, λ n, match n with
 | 0 := λ _, h0
 | 1 := λ _, h1
 | «expr + »(k, 2) := λ hk, begin
   let [ident p] [] [":=", expr «expr + »(k, 2).min_fac],
   haveI [] [":", expr fact (prime p)] [":=", expr ⟨min_fac_prime (succ_succ_ne_one k)⟩],
   let [ident t] [] [":=", expr padic_val_nat p «expr + »(k, 2)],
   have [ident hpt] [":", expr «expr ∣ »(«expr ^ »(p, t), «expr + »(k, 2))] [":=", expr pow_padic_val_nat_dvd],
   have [ident ht] [":", expr «expr < »(0, t)] [":=", expr one_le_padic_val_nat_of_dvd (nat.succ_ne_zero «expr + »(k, 1)) (min_fac_dvd _)],
   convert [] [expr h «expr / »(«expr + »(k, 2), «expr ^ »(p, t)) p t (fact.out _) _ _] [],
   { rw [expr nat.mul_div_cancel' hpt] [] },
   { rw ["[", expr nat.dvd_div_iff hpt, ",", "<-", expr pow_succ', "]"] [],
     exact [expr pow_succ_padic_val_nat_not_dvd nat.succ_pos'] },
   apply [expr hk _ (nat.div_lt_of_lt_mul _)],
   rw ["[", expr lt_mul_iff_one_lt_left nat.succ_pos', ",", expr one_lt_pow_iff ht.ne, "]"] [],
   exact [expr (prime.one_lt' p).out]
 end
 end)

/-- Given `P 0`, `P 1`, and `P (p ^ k)` for positive prime powers, and a way to extend `P a` and
`P b` to `P (a * b)` when `a, b` are coprime, you can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def rec_on_pos_prime_coprime {P : ℕ → Sort _} (hp : ∀ (p n : ℕ), Prime p → 0 < n → P (p^n)) (h0 : P 0) (h1 : P 1)
  (h : ∀ a b, coprime a b → P a → P b → P (a*b)) : ∀ a, P a :=
  rec_on_prime_pow h0 h1$
    fun a p n hp' hpa ha =>
      h (p^n) a (prime.coprime_pow_of_not_dvd hp' hpa).symm
        (if h : n = 0 then Eq.ndrec h1 h.symm else hp p n hp'$ Nat.pos_of_ne_zeroₓ h) ha

/-- Given `P 0`, `P (p ^ k)` for all prime powers, and a way to extend `P a` and `P b` to
`P (a * b)` when `a, b` are coprime, you can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def rec_on_prime_coprime {P : ℕ → Sort _} (h0 : P 0) (hp : ∀ (p n : ℕ), Prime p → P (p^n))
  (h : ∀ a b, coprime a b → P a → P b → P (a*b)) : ∀ a, P a :=
  rec_on_pos_prime_coprime (fun p n h _ => hp p n h) h0 (hp 2 0 prime_two) h

/-- Given `P 0`, `P 1`, `P p` for all primes, and a proof that you can extend
`P a` and `P b` to `P (a * b)`, you can define `P` for all natural numbers. -/
@[elab_as_eliminator]
def rec_on_mul {P : ℕ → Sort _} (h0 : P 0) (h1 : P 1) (hp : ∀ p, Prime p → P p) (h : ∀ a b, P a → P b → P (a*b)) :
  ∀ a, P a :=
  let hp : ∀ (p n : ℕ), Prime p → P (p^n) :=
    fun p n hp' =>
      match n with 
      | 0 => h1
      | n+1 =>
        by 
          exact h _ _ (hp p hp') (_match _)
  rec_on_prime_coprime h0 hp$ fun a b _ => h a b

end Nat

