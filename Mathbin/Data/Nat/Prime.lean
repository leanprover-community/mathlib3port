import Mathbin.Data.List.Sort 
import Mathbin.Data.Nat.Gcd 
import Mathbin.Data.Nat.Sqrt 
import Mathbin.Tactic.NormNum 
import Mathbin.Tactic.Wlog

/-!
# Prime numbers

This file deals with prime numbers: natural numbers `p ≥ 2` whose only divisors are `p` and `1`.

## Important declarations

All the following declarations exist in the namespace `nat`.

- `prime`: the predicate that expresses that a natural number `p` is prime
- `primes`: the subtype of natural numbers that are prime
- `min_fac n`: the minimal prime factor of a natural number `n ≠ 1`
- `exists_infinite_primes`: Euclid's theorem that there exist infinitely many prime numbers
- `factors n`: the prime factorization of `n`
- `factors_unique`: uniqueness of the prime factorisation

-/


open Bool Subtype

open_locale Nat

namespace Nat

/-- `prime p` means that `p` is a prime number, that is, a natural number
  at least 2 whose only divisors are `p` and `1`. -/
@[pp_nodot]
def prime (p : ℕ) :=
  2 ≤ p ∧ ∀ m _ : m ∣ p, m = 1 ∨ m = p

theorem prime.two_le {p : ℕ} : prime p → 2 ≤ p :=
  And.left

theorem prime.one_lt {p : ℕ} : prime p → 1 < p :=
  prime.two_le

instance prime.one_lt' (p : ℕ) [hp : _root_.fact p.prime] : _root_.fact (1 < p) :=
  ⟨hp.1.one_lt⟩

theorem prime.ne_one {p : ℕ} (hp : p.prime) : p ≠ 1 :=
  Ne.symm$ ne_of_ltₓ hp.one_lt

theorem prime_def_lt {p : ℕ} : prime p ↔ 2 ≤ p ∧ ∀ m _ : m < p, m ∣ p → m = 1 :=
  and_congr_right$
    fun p2 =>
      forall_congrₓ$
        fun m =>
          ⟨fun h l d => (h d).resolve_right (ne_of_ltₓ l),
            fun h d => (le_of_dvd (le_of_succ_le p2) d).lt_or_eq_dec.imp_left fun l => h l d⟩

theorem prime_def_lt' {p : ℕ} : prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m < p → ¬m ∣ p :=
  prime_def_lt.trans$
    and_congr_right$
      fun p2 =>
        forall_congrₓ$
          fun m =>
            ⟨fun h m2 l d =>
                not_lt_of_geₓ m2
                  ((h l d).symm ▸
                    by 
                      decide),
              fun h l d =>
                by 
                  rcases m with (_ | _ | m)
                  ·
                    rw [eq_zero_of_zero_dvd d] at p2 
                    revert p2 
                    exact
                      by 
                        decide
                  ·
                    rfl
                  ·
                    exact
                      (h
                            (by 
                              decide)
                            l).elim
                        d⟩

theorem prime_def_le_sqrt {p : ℕ} : prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m ≤ sqrt p → ¬m ∣ p :=
  prime_def_lt'.trans$
    and_congr_right$
      fun p2 =>
        ⟨fun a m m2 l => a m m2$ lt_of_le_of_ltₓ l$ sqrt_lt_self p2,
          fun a =>
            have  : ∀ {m k}, m ≤ k → 1 < m → p ≠ m*k :=
              fun m k mk m1 e => a m m1 (le_sqrt.2 (e.symm ▸ Nat.mul_le_mul_leftₓ m mk)) ⟨k, e⟩
            fun m m2 l ⟨k, e⟩ =>
              by 
                cases' le_totalₓ m k with mk km
                ·
                  exact this mk m2 e
                ·
                  rw [mul_commₓ] at e 
                  refine' this km (lt_of_mul_lt_mul_right _ (zero_le m)) e 
                  rwa [one_mulₓ, ←e]⟩

-- error in Data.Nat.Prime: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prime_of_coprime
(n : exprℕ())
(h1 : «expr < »(1, n))
(h : ∀ m «expr < » n, «expr ≠ »(m, 0) → n.coprime m) : prime n :=
begin
  refine [expr prime_def_lt.mpr ⟨h1, λ m mlt mdvd, _⟩],
  have [ident hm] [":", expr «expr ≠ »(m, 0)] [],
  { rintro [ident rfl],
    rw [expr zero_dvd_iff] ["at", ident mdvd],
    exact [expr mlt.ne' mdvd] },
  exact [expr (h m mlt hm).symm.eq_one_of_dvd mdvd]
end

section 

/--
  This instance is slower than the instance `decidable_prime` defined below,
  but has the advantage that it works in the kernel for small values.

  If you need to prove that a particular number is prime, in any case
  you should not use `dec_trivial`, but rather `by norm_num`, which is
  much faster.
  -/
@[local instance]
def decidable_prime_1 (p : ℕ) : Decidable (prime p) :=
  decidableOfIff' _ prime_def_lt'

theorem prime.ne_zero {n : ℕ} (h : prime n) : n ≠ 0 :=
  by 
    rintro rfl 
    revert h 
    decide

theorem prime.pos {p : ℕ} (pp : prime p) : 0 < p :=
  lt_of_succ_lt pp.one_lt

theorem not_prime_zero : ¬prime 0 :=
  by 
    simp [prime]

theorem not_prime_one : ¬prime 1 :=
  by 
    simp [prime]

theorem prime_two : prime 2 :=
  by 
    decide

end 

theorem prime.pred_pos {p : ℕ} (pp : prime p) : 0 < pred p :=
  lt_pred_iff.2 pp.one_lt

theorem succ_pred_prime {p : ℕ} (pp : prime p) : succ (pred p) = p :=
  succ_pred_eq_of_pos pp.pos

theorem dvd_prime {p m : ℕ} (pp : prime p) : m ∣ p ↔ m = 1 ∨ m = p :=
  ⟨fun d => pp.2 m d, fun h => h.elim (fun e => e.symm ▸ one_dvd _) fun e => e.symm ▸ dvd_rfl⟩

theorem dvd_prime_two_le {p m : ℕ} (pp : prime p) (H : 2 ≤ m) : m ∣ p ↔ m = p :=
  (dvd_prime pp).trans$ or_iff_right_of_imp$ Not.elim$ ne_of_gtₓ H

theorem prime_dvd_prime_iff_eq {p q : ℕ} (pp : p.prime) (qp : q.prime) : p ∣ q ↔ p = q :=
  dvd_prime_two_le qp (prime.two_le pp)

theorem prime.not_dvd_one {p : ℕ} (pp : prime p) : ¬p ∣ 1
| d =>
  not_le_of_gtₓ pp.one_lt$
    le_of_dvd
      (by 
        decide)
      d

theorem not_prime_mul {a b : ℕ} (a1 : 1 < a) (b1 : 1 < b) : ¬prime (a*b) :=
  fun h =>
    ne_of_ltₓ (Nat.mul_lt_mul_of_pos_leftₓ b1 (lt_of_succ_lt a1))$
      by 
        simpa using (dvd_prime_two_le h a1).1 (dvd_mul_right _ _)

theorem not_prime_mul' {a b n : ℕ} (h : (a*b) = n) (h₁ : 1 < a) (h₂ : 1 < b) : ¬prime n :=
  by 
    rw [←h]
    exact not_prime_mul h₁ h₂

section MinFac

private theorem min_fac_lemma (n k : ℕ) (h : ¬n < k*k) : sqrt n - k < (sqrt n+2) - k :=
  (tsub_lt_tsub_iff_right$ le_sqrt.2$ le_of_not_gtₓ h).2$
    Nat.lt_add_of_pos_rightₓ
      (by 
        decide)

/-- If `n < k * k`, then `min_fac_aux n k = n`, if `k | n`, then `min_fac_aux n k = k`.
  Otherwise, `min_fac_aux n k = min_fac_aux n (k+2)` using well-founded recursion.
  If `n` is odd and `1 < n`, then then `min_fac_aux n 3` is the smallest prime factor of `n`. -/
def min_fac_aux (n : ℕ) : ℕ → ℕ
| k =>
  if h : n < k*k then n else
    if k ∣ n then k else
      have  := min_fac_lemma n k h 
      min_fac_aux (k+2)

/-- Returns the smallest prime factor of `n ≠ 1`. -/
def min_fac : ℕ → ℕ
| 0 => 2
| 1 => 1
| n+2 => if 2 ∣ n then 2 else min_fac_aux (n+2) 3

@[simp]
theorem min_fac_zero : min_fac 0 = 2 :=
  rfl

@[simp]
theorem min_fac_one : min_fac 1 = 1 :=
  rfl

theorem min_fac_eq : ∀ n, min_fac n = if 2 ∣ n then 2 else min_fac_aux n 3
| 0 =>
  by 
    simp 
| 1 =>
  by 
    simp
        [show 2 ≠ 1 from
          by 
            decide] <;>
      rw [min_fac_aux] <;> rfl
| n+2 =>
  have  : (2 ∣ n+2) ↔ 2 ∣ n :=
    (Nat.dvd_add_iff_left
        (by 
          rfl)).symm
      
  by 
    simp [min_fac, this] <;> congr

private def min_fac_prop (n k : ℕ) :=
  2 ≤ k ∧ k ∣ n ∧ ∀ m, 2 ≤ m → m ∣ n → k ≤ m

-- error in Data.Nat.Prime: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem min_fac_aux_has_prop
{n : exprℕ()}
(n2 : «expr ≤ »(2, n))
(nd2 : «expr¬ »(«expr ∣ »(2, n))) : ∀
k
i, «expr = »(k, «expr + »(«expr * »(2, i), 3)) → ∀
m, «expr ≤ »(2, m) → «expr ∣ »(m, n) → «expr ≤ »(k, m) → min_fac_prop n (min_fac_aux n k)
| k := λ i e a, begin
  rw [expr min_fac_aux] [],
  by_cases [expr h, ":", expr «expr < »(n, «expr * »(k, k))]; simp [] [] [] ["[", expr h, "]"] [] [],
  { have [ident pp] [":", expr prime n] [":=", expr prime_def_le_sqrt.2 ⟨n2, λ
      m m2 l d, «expr $ »(not_lt_of_ge l, lt_of_lt_of_le (sqrt_lt.2 h) (a m m2 d))⟩],
    from [expr ⟨n2, dvd_rfl, λ m m2 d, le_of_eq ((dvd_prime_two_le pp m2).1 d).symm⟩] },
  have [ident k2] [":", expr «expr ≤ »(2, k)] [],
  { subst [expr e],
    exact [expr exprdec_trivial()] },
  by_cases [expr dk, ":", expr «expr ∣ »(k, n)]; simp [] [] [] ["[", expr dk, "]"] [] [],
  { exact [expr ⟨k2, dk, a⟩] },
  { refine [expr have _, from min_fac_lemma n k h,
     min_fac_aux_has_prop «expr + »(k, 2) «expr + »(i, 1) (by simp [] [] [] ["[", expr e, ",", expr left_distrib, "]"] [] []) (λ
      m m2 d, _)],
    cases [expr nat.eq_or_lt_of_le (a m m2 d)] ["with", ident me, ident ml],
    { subst [expr me],
      contradiction },
    apply [expr (nat.eq_or_lt_of_le ml).resolve_left],
    intro [ident me],
    rw ["[", "<-", expr me, ",", expr e, "]"] ["at", ident d],
    change [expr «expr ∣ »(«expr * »(2, «expr + »(i, 2)), n)] [] ["at", ident d],
    have [] [] [":=", expr dvd_of_mul_right_dvd d],
    contradiction }
end

-- error in Data.Nat.Prime: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem min_fac_has_prop {n : exprℕ()} (n1 : «expr ≠ »(n, 1)) : min_fac_prop n (min_fac n) :=
begin
  by_cases [expr n0, ":", expr «expr = »(n, 0)],
  { simp [] [] [] ["[", expr n0, ",", expr min_fac_prop, ",", expr ge, "]"] [] [] },
  have [ident n2] [":", expr «expr ≤ »(2, n)] [],
  { revert [ident n0, ident n1],
    rcases [expr n, "with", "_", "|", "_", "|", "_"]; exact [expr exprdec_trivial()] },
  simp [] [] [] ["[", expr min_fac_eq, "]"] [] [],
  by_cases [expr d2, ":", expr «expr ∣ »(2, n)]; simp [] [] [] ["[", expr d2, "]"] [] [],
  { exact [expr ⟨le_refl _, d2, λ k k2 d, k2⟩] },
  { refine [expr min_fac_aux_has_prop n2 d2 3 0 rfl (λ m m2 d, (nat.eq_or_lt_of_le m2).resolve_left (mt _ d2))],
    exact [expr λ e, «expr ▸ »(e.symm, d)] }
end

theorem min_fac_dvd (n : ℕ) : min_fac n ∣ n :=
  if n1 : n = 1 then
    by 
      simp [n1]
  else (min_fac_has_prop n1).2.1

theorem min_fac_prime {n : ℕ} (n1 : n ≠ 1) : prime (min_fac n) :=
  let ⟨f2, fd, a⟩ := min_fac_has_prop n1 
  prime_def_lt'.2 ⟨f2, fun m m2 l d => not_le_of_gtₓ l (a m m2 (d.trans fd))⟩

theorem min_fac_le_of_dvd {n : ℕ} : ∀ {m : ℕ}, 2 ≤ m → m ∣ n → min_fac n ≤ m :=
  by 
    byCases' n1 : n = 1 <;>
      [exact
        fun m m2 d =>
          n1.symm ▸
            le_transₓ
              (by 
                decide)
              m2,
      exact (min_fac_has_prop n1).2.2]

theorem min_fac_pos (n : ℕ) : 0 < min_fac n :=
  by 
    byCases' n1 : n = 1 <;>
      [exact
        n1.symm ▸
          by 
            decide,
      exact (min_fac_prime n1).Pos]

theorem min_fac_le {n : ℕ} (H : 0 < n) : min_fac n ≤ n :=
  le_of_dvd H (min_fac_dvd n)

theorem le_min_fac {m n : ℕ} : n = 1 ∨ m ≤ min_fac n ↔ ∀ p, prime p → p ∣ n → m ≤ p :=
  ⟨fun h p pp d =>
      h.elim
        (by 
          rintro rfl <;> cases pp.not_dvd_one d)
        fun h => le_transₓ h$ min_fac_le_of_dvd pp.two_le d,
    fun H => or_iff_not_imp_left.2$ fun n1 => H _ (min_fac_prime n1) (min_fac_dvd _)⟩

theorem le_min_fac' {m n : ℕ} : n = 1 ∨ m ≤ min_fac n ↔ ∀ p, 2 ≤ p → p ∣ n → m ≤ p :=
  ⟨fun h p pp : 1 < p d =>
      h.elim
        (by 
          rintro rfl <;>
            cases
              not_le_of_lt pp
                (le_of_dvd
                  (by 
                    decide)
                  d))
        fun h => le_transₓ h$ min_fac_le_of_dvd pp d,
    fun H => le_min_fac.2 fun p pp d => H p pp.two_le d⟩

theorem prime_def_min_fac {p : ℕ} : prime p ↔ 2 ≤ p ∧ min_fac p = p :=
  ⟨fun pp =>
      ⟨pp.two_le,
        let ⟨f2, fd, a⟩ := min_fac_has_prop$ ne_of_gtₓ pp.one_lt
        ((dvd_prime pp).1 fd).resolve_left (ne_of_gtₓ f2)⟩,
    fun ⟨p2, e⟩ => e ▸ min_fac_prime (ne_of_gtₓ p2)⟩

/--
This instance is faster in the virtual machine than `decidable_prime_1`,
but slower in the kernel.

If you need to prove that a particular number is prime, in any case
you should not use `dec_trivial`, but rather `by norm_num`, which is
much faster.
-/
instance decidable_prime (p : ℕ) : Decidable (prime p) :=
  decidableOfIff' _ prime_def_min_fac

theorem not_prime_iff_min_fac_lt {n : ℕ} (n2 : 2 ≤ n) : ¬prime n ↔ min_fac n < n :=
  (not_congr$ prime_def_min_fac.trans$ and_iff_right n2).trans$
    (lt_iff_le_and_ne.trans$ and_iff_right$ min_fac_le$ le_of_succ_le n2).symm

theorem min_fac_le_div {n : ℕ} (pos : 0 < n) (np : ¬prime n) : min_fac n ≤ n / min_fac n :=
  match min_fac_dvd n with 
  | ⟨0, h0⟩ =>
    absurd Pos$
      by 
        rw [h0, mul_zero] <;>
          exact
            by 
              decide
  | ⟨1, h1⟩ =>
    by 
      rw [mul_oneₓ] at h1 
      rw [prime_def_min_fac, not_and_distrib, ←h1, eq_self_iff_true, not_true, or_falseₓ, not_leₓ] at np 
      rw [le_antisymmₓ (le_of_lt_succ np) (succ_le_of_lt Pos), min_fac_one, Nat.div_oneₓ]
  | ⟨x+2, hx⟩ =>
    by 
      convRHS => congr rw [hx]
      rw [Nat.mul_div_cancel_leftₓ _ (min_fac_pos _)]
      exact
        min_fac_le_of_dvd
          (by 
            decide)
          ⟨min_fac n,
            by 
              rwa [mul_commₓ]⟩

/--
The square of the smallest prime factor of a composite number `n` is at most `n`.
-/
theorem min_fac_sq_le_self {n : ℕ} (w : 0 < n) (h : ¬prime n) : min_fac n ^ 2 ≤ n :=
  have t : min_fac n ≤ n / min_fac n := min_fac_le_div w h 
  calc min_fac n ^ 2 = min_fac n*min_fac n := sq (min_fac n)
    _ ≤ (n / min_fac n)*min_fac n := Nat.mul_le_mul_rightₓ (min_fac n) t 
    _ ≤ n := div_mul_le_self n (min_fac n)
    

-- error in Data.Nat.Prime: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem min_fac_eq_one_iff {n : exprℕ()} : «expr ↔ »(«expr = »(min_fac n, 1), «expr = »(n, 1)) :=
begin
  split,
  { intro [ident h],
    by_contradiction [ident hn],
    have [] [] [":=", expr min_fac_prime hn],
    rw [expr h] ["at", ident this],
    exact [expr not_prime_one this] },
  { rintro [ident rfl],
    refl }
end

-- error in Data.Nat.Prime: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem min_fac_eq_two_iff (n : exprℕ()) : «expr ↔ »(«expr = »(min_fac n, 2), «expr ∣ »(2, n)) :=
begin
  split,
  { intro [ident h],
    convert [] [expr min_fac_dvd _] [],
    rw [expr h] [] },
  { intro [ident h],
    have [ident ub] [] [":=", expr min_fac_le_of_dvd (le_refl 2) h],
    have [ident lb] [] [":=", expr min_fac_pos n],
    cases [expr h, ":", expr n.min_fac] ["with", ident m],
    { rw [expr h] ["at", ident lb],
      cases [expr lb] [] },
    { cases [expr m] ["with", ident m],
      { simp [] [] [] [] [] ["at", ident h],
        subst [expr h],
        cases [expr h] ["with", ident n, ident h],
        cases [expr n] []; cases [expr h] [] },
      { cases [expr m] ["with", ident m],
        { refl },
        { rw [expr h] ["at", ident ub],
          cases [expr ub] ["with", "_", ident ub],
          cases [expr ub] ["with", "_", ident ub],
          cases [expr ub] [] } } } }
end

end MinFac

theorem exists_dvd_of_not_prime {n : ℕ} (n2 : 2 ≤ n) (np : ¬prime n) : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
  ⟨min_fac n, min_fac_dvd _, ne_of_gtₓ (min_fac_prime (ne_of_gtₓ n2)).one_lt,
    ne_of_ltₓ$ (not_prime_iff_min_fac_lt n2).1 np⟩

theorem exists_dvd_of_not_prime2 {n : ℕ} (n2 : 2 ≤ n) (np : ¬prime n) : ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n :=
  ⟨min_fac n, min_fac_dvd _, (min_fac_prime (ne_of_gtₓ n2)).two_le, (not_prime_iff_min_fac_lt n2).1 np⟩

theorem exists_prime_and_dvd {n : ℕ} (n2 : 2 ≤ n) : ∃ p, prime p ∧ p ∣ n :=
  ⟨min_fac n, min_fac_prime (ne_of_gtₓ n2), min_fac_dvd _⟩

/-- Euclid's theorem on the **infinitude of primes**.
Here given in the form: for every `n`, there exists a prime number `p ≥ n`. -/
theorem exists_infinite_primes (n : ℕ) : ∃ p, n ≤ p ∧ prime p :=
  let p := min_fac (n !+1)
  have f1 : (n !+1) ≠ 1 := ne_of_gtₓ$ succ_lt_succ$ factorial_pos _ 
  have pp : prime p := min_fac_prime f1 
  have np : n ≤ p :=
    le_of_not_geₓ$
      fun h =>
        have h₁ : p ∣ n ! := dvd_factorial (min_fac_pos _) h 
        have h₂ : p ∣ 1 := (Nat.dvd_add_iff_right h₁).2 (min_fac_dvd _)
        pp.not_dvd_one h₂
  ⟨p, np, pp⟩

theorem prime.eq_two_or_odd {p : ℕ} (hp : prime p) : p = 2 ∨ p % 2 = 1 :=
  (Nat.mod_two_eq_zero_or_oneₓ p).elim
    (fun h =>
      Or.inl
        ((hp.2 2 (dvd_of_mod_eq_zero h)).resolve_left
            (by 
              decide)).symm)
    Or.inr

theorem coprime_of_dvd {m n : ℕ} (H : ∀ k, prime k → k ∣ m → ¬k ∣ n) : coprime m n :=
  by 
    cases' Nat.eq_zero_or_posₓ (gcd m n) with g0 g1
    ·
      rw [eq_zero_of_gcd_eq_zero_left g0, eq_zero_of_gcd_eq_zero_right g0] at H 
      exfalso 
      exact H 2 prime_two (dvd_zero _) (dvd_zero _)
    apply Eq.symm 
    change 1 ≤ _ at g1 
    apply (lt_or_eq_of_leₓ g1).resolve_left 
    intro g2 
    obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd g2 
    apply H p hp <;> apply dvd_trans hpdvd
    ·
      exact gcd_dvd_left _ _
    ·
      exact gcd_dvd_right _ _

theorem coprime_of_dvd' {m n : ℕ} (H : ∀ k, prime k → k ∣ m → k ∣ n → k ∣ 1) : coprime m n :=
  coprime_of_dvd$ fun k kp km kn => not_le_of_gtₓ kp.one_lt$ le_of_dvd zero_lt_one$ H k kp km kn

theorem factors_lemma {k} : (k+2) / min_fac (k+2) < k+2 :=
  div_lt_self
    (by 
      decide)
    (min_fac_prime
        (by 
          decide)).one_lt

/-- `factors n` is the prime factorization of `n`, listed in increasing order. -/
def factors : ℕ → List ℕ
| 0 => []
| 1 => []
| n@(k+2) =>
  let m := min_fac n 
  have  : n / m < n := factors_lemma 
  m :: factors (n / m)

@[simp]
theorem factors_zero : factors 0 = [] :=
  by 
    rw [factors]

@[simp]
theorem factors_one : factors 1 = [] :=
  by 
    rw [factors]

theorem prime_of_mem_factors : ∀ {n p}, p ∈ factors n → prime p
| 0 =>
  by 
    simp 
| 1 =>
  by 
    simp 
| n@(k+2) =>
  fun p h =>
    let m := min_fac n 
    have  : n / m < n := factors_lemma 
    have h₁ : p = m ∨ p ∈ factors (n / m) :=
      (List.mem_cons_iffₓ _ _ _).1
        (by 
          rwa [factors] at h)
    Or.cases_on h₁
      (fun h₂ =>
        h₂.symm ▸
          min_fac_prime
            (by 
              decide))
      prime_of_mem_factors

theorem prod_factors : ∀ {n}, 0 < n → List.prod (factors n) = n
| 0 =>
  by 
    simp 
| 1 =>
  by 
    simp 
| n@(k+2) =>
  fun h =>
    let m := min_fac n 
    have  : n / m < n := factors_lemma 
    show (factors n).Prod = n from
      have h₁ : 0 < n / m :=
        Nat.pos_of_ne_zeroₓ$
          fun h =>
            have  : n = 0*m := (Nat.div_eq_iff_eq_mul_left (min_fac_pos _) (min_fac_dvd _)).1 h 
            by 
              rw [zero_mul] at this <;>
                exact
                  (show (k+2) ≠ 0 from
                      by 
                        decide)
                    this 
      by 
        rw [factors, List.prod_cons, prod_factors h₁, Nat.mul_div_cancel'ₓ (min_fac_dvd _)]

-- error in Data.Nat.Prime: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem factors_prime {p : exprℕ()} (hp : nat.prime p) : «expr = »(p.factors, «expr[ , ]»([p])) :=
begin
  have [] [":", expr «expr = »(p, «expr + »(«expr - »(p, 2), 2))] [":=", expr (tsub_eq_iff_eq_add_of_le hp.1).mp rfl],
  rw ["[", expr this, ",", expr nat.factors, "]"] [],
  simp [] [] ["only"] ["[", expr eq.symm this, "]"] [] [],
  have [] [":", expr «expr = »(nat.min_fac p, p)] [":=", expr (nat.prime_def_min_fac.mp hp).2],
  split,
  { exact [expr this] },
  { simp [] [] ["only"] ["[", expr this, ",", expr nat.factors, ",", expr nat.div_self (nat.prime.pos hp), "]"] [] [] }
end

theorem factors_chain : ∀ {n a}, (∀ p, prime p → p ∣ n → a ≤ p) → List.Chain (· ≤ ·) a (factors n)
| 0 =>
  fun a h =>
    by 
      simp 
| 1 =>
  fun a h =>
    by 
      simp 
| n@(k+2) =>
  fun a h =>
    let m := min_fac n 
    have  : n / m < n := factors_lemma 
    by 
      rw [factors]
      refine'
        List.Chain.cons
          ((le_min_fac.2 h).resolve_left
            (by 
              decide))
          (factors_chain _)
      exact fun p pp d => min_fac_le_of_dvd pp.two_le (d.trans$ div_dvd_of_dvd$ min_fac_dvd _)

theorem factors_chain_2 n : List.Chain (· ≤ ·) 2 (factors n) :=
  factors_chain$ fun p pp _ => pp.two_le

theorem factors_chain' n : List.Chain' (· ≤ ·) (factors n) :=
  @List.Chain'.tail _ _ (_ :: _) (factors_chain_2 _)

theorem factors_sorted (n : ℕ) : List.Sorted (· ≤ ·) (factors n) :=
  (List.chain'_iff_pairwise (@le_transₓ _ _)).1 (factors_chain' _)

/-- `factors` can be constructed inductively by extracting `min_fac`, for sufficiently large `n`. -/
theorem factors_add_two (n : ℕ) : factors (n+2) = min_fac (n+2) :: factors ((n+2) / min_fac (n+2)) :=
  by 
    rw [factors]

@[simp]
theorem factors_eq_nil (n : ℕ) : n.factors = [] ↔ n = 0 ∨ n = 1 :=
  by 
    split  <;> intro h
    ·
      rcases n with (_ | _ | n)
      ·
        exact Or.inl rfl
      ·
        exact Or.inr rfl
      ·
        rw [factors] at h 
        injection h
    ·
      rcases h with (rfl | rfl)
      ·
        exact factors_zero
      ·
        exact factors_one

theorem prime.coprime_iff_not_dvd {p n : ℕ} (pp : prime p) : coprime p n ↔ ¬p ∣ n :=
  ⟨fun co d =>
      pp.not_dvd_one$
        co.dvd_of_dvd_mul_left
          (by 
            simp [d]),
    fun nd => coprime_of_dvd$ fun m m2 mp => ((prime_dvd_prime_iff_eq m2 pp).1 mp).symm ▸ nd⟩

theorem prime.dvd_iff_not_coprime {p n : ℕ} (pp : prime p) : p ∣ n ↔ ¬coprime p n :=
  iff_not_comm.2 pp.coprime_iff_not_dvd

theorem prime.not_coprime_iff_dvd {m n : ℕ} : ¬coprime m n ↔ ∃ p, prime p ∧ p ∣ m ∧ p ∣ n :=
  by 
    apply Iff.intro
    ·
      intro h 
      exact
        ⟨min_fac (gcd m n), min_fac_prime h, (min_fac_dvd (gcd m n)).trans (gcd_dvd_left m n),
          (min_fac_dvd (gcd m n)).trans (gcd_dvd_right m n)⟩
    ·
      intro h 
      cases' h with p hp 
      apply Nat.not_coprime_of_dvd_of_dvdₓ (prime.one_lt hp.1) hp.2.1 hp.2.2

theorem prime.dvd_mul {p m n : ℕ} (pp : prime p) : (p ∣ m*n) ↔ p ∣ m ∨ p ∣ n :=
  ⟨fun H => or_iff_not_imp_left.2$ fun h => (pp.coprime_iff_not_dvd.2 h).dvd_of_dvd_mul_left H,
    Or.ndrec (fun h : p ∣ m => h.mul_right _) fun h : p ∣ n => h.mul_left _⟩

theorem prime.not_dvd_mul {p m n : ℕ} (pp : prime p) (Hm : ¬p ∣ m) (Hn : ¬p ∣ n) : ¬p ∣ m*n :=
  mt pp.dvd_mul.1$
    by 
      simp [Hm, Hn]

theorem prime.dvd_of_dvd_pow {p m n : ℕ} (pp : prime p) (h : p ∣ m ^ n) : p ∣ m :=
  by 
    induction' n with n IH <;> [exact pp.not_dvd_one.elim h,
      ·
        ·
          rw [pow_succₓ] at h 
          exact (pp.dvd_mul.1 h).elim id IH]

theorem prime.pow_dvd_of_dvd_mul_right {p n a b : ℕ} (hp : p.prime) (h : p ^ n ∣ a*b) (hpb : ¬p ∣ b) : p ^ n ∣ a :=
  by 
    induction' n with n ih
    ·
      simp 
    ·
      rw [pow_succ'ₓ] at *
      rcases ih ((dvd_mul_right _ _).trans h) with ⟨c, rfl⟩
      rw [mul_assocₓ] at h 
      rcases hp.dvd_mul.1 (Nat.dvd_of_mul_dvd_mul_leftₓ (pow_pos hp.pos _) h) with (⟨d, rfl⟩ | ⟨d, rfl⟩)
      ·
        rw [←mul_assocₓ]
        exact dvd_mul_right _ _
      ·
        exact (hpb (dvd_mul_right _ _)).elim

theorem prime.pow_dvd_of_dvd_mul_left {p n a b : ℕ} (hp : p.prime) (h : p ^ n ∣ a*b) (hpb : ¬p ∣ a) : p ^ n ∣ b :=
  by 
    rw [mul_commₓ] at h <;> exact hp.pow_dvd_of_dvd_mul_right h hpb

theorem prime.pow_not_prime {x n : ℕ} (hn : 2 ≤ n) : ¬(x ^ n).Prime :=
  fun hp =>
    (hp.2 x$ dvd_trans ⟨x, sq _⟩ (pow_dvd_pow _ hn)).elim (fun hx1 => hp.ne_one$ hx1.symm ▸ one_pow _)
      fun hxn =>
        lt_irreflₓ x$
          calc x = x ^ 1 := (pow_oneₓ _).symm 
            _ < x ^ n := Nat.pow_right_strict_mono (hxn.symm ▸ hp.two_le) hn 
            _ = x := hxn.symm
            

theorem prime.pow_not_prime' {x : ℕ} : ∀ {n : ℕ}, n ≠ 1 → ¬(x ^ n).Prime
| 0 => fun _ => not_prime_one
| 1 => fun h => (h rfl).elim
| n+2 => fun _ => prime.pow_not_prime le_add_self

theorem prime.eq_one_of_pow {x n : ℕ} (h : (x ^ n).Prime) : n = 1 :=
  not_imp_not.mp prime.pow_not_prime' h

theorem prime.pow_eq_iff {p a k : ℕ} (hp : p.prime) : a ^ k = p ↔ a = p ∧ k = 1 :=
  by 
    refine'
      ⟨_,
        fun h =>
          by 
            rw [h.1, h.2, pow_oneₓ]⟩
    rintro rfl 
    rw [hp.eq_one_of_pow, eq_self_iff_true, and_trueₓ, pow_oneₓ]

-- error in Data.Nat.Prime: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem prime.mul_eq_prime_sq_iff
{x y p : exprℕ()}
(hp : p.prime)
(hx : «expr ≠ »(x, 1))
(hy : «expr ≠ »(y, 1)) : «expr ↔ »(«expr = »(«expr * »(x, y), «expr ^ »(p, 2)), «expr ∧ »(«expr = »(x, p), «expr = »(y, p))) :=
⟨λ h, have pdvdxy : «expr ∣ »(p, «expr * »(x, y)), by rw [expr h] []; simp [] [] [] ["[", expr sq, "]"] [] [],
 begin
   wlog [] [] [":=", expr hp.dvd_mul.1 pdvdxy] ["using", ident x, ident y],
   cases [expr case] ["with", ident a, ident ha],
   have [ident hap] [":", expr «expr ∣ »(a, p)] [],
   from [expr ⟨y, by rwa ["[", expr ha, ",", expr sq, ",", expr mul_assoc, ",", expr nat.mul_right_inj hp.pos, ",", expr eq_comm, "]"] ["at", ident h]⟩],
   exact [expr ((nat.dvd_prime hp).1 hap).elim (λ
     _, by clear_aux_decl; simp [] [] [] ["[", "*", ",", expr sq, ",", expr nat.mul_right_inj hp.pos, "]"] [] ["at", "*"] { contextual := tt }) (λ
     _, by clear_aux_decl; simp [] [] [] ["[", "*", ",", expr sq, ",", expr mul_comm, ",", expr mul_assoc, ",", expr nat.mul_right_inj hp.pos, ",", expr nat.mul_right_eq_self_iff hp.pos, "]"] [] ["at", "*"] { contextual := tt })]
 end, λ ⟨h₁, h₂⟩, «expr ▸ »(h₁.symm, «expr ▸ »(h₂.symm, (sq _).symm))⟩

theorem prime.dvd_factorial : ∀ {n p : ℕ} hp : prime p, p ∣ n ! ↔ p ≤ n
| 0, p, hp => iff_of_false hp.not_dvd_one (not_le_of_lt hp.pos)
| n+1, p, hp =>
  by 
    rw [factorial_succ, hp.dvd_mul, prime.dvd_factorial hp]
    exact
      ⟨fun h => h.elim (le_of_dvd (succ_pos _)) le_succ_of_le,
        fun h =>
          (_root_.lt_or_eq_of_le h).elim (Or.inr ∘ le_of_lt_succ)
            fun h =>
              Or.inl$
                by 
                  rw [h]⟩

theorem prime.coprime_pow_of_not_dvd {p m a : ℕ} (pp : prime p) (h : ¬p ∣ a) : coprime a (p ^ m) :=
  (pp.coprime_iff_not_dvd.2 h).symm.pow_right _

theorem coprime_primes {p q : ℕ} (pp : prime p) (pq : prime q) : coprime p q ↔ p ≠ q :=
  pp.coprime_iff_not_dvd.trans$ not_congr$ dvd_prime_two_le pq pp.two_le

theorem coprime_pow_primes {p q : ℕ} (n m : ℕ) (pp : prime p) (pq : prime q) (h : p ≠ q) : coprime (p ^ n) (q ^ m) :=
  ((coprime_primes pp pq).2 h).pow _ _

theorem coprime_or_dvd_of_prime {p} (pp : prime p) (i : ℕ) : coprime p i ∨ p ∣ i :=
  by 
    rw [pp.dvd_iff_not_coprime] <;> apply em

theorem dvd_prime_pow {p : ℕ} (pp : prime p) {m i : ℕ} : i ∣ p ^ m ↔ ∃ (k : _)(_ : k ≤ m), i = p ^ k :=
  by 
    induction' m with m IH generalizing i
    ·
      simp [pow_succₓ, le_zero_iff] at *
    byCases' p ∣ i
    ·
      cases' h with a e 
      subst e 
      rw [pow_succₓ, Nat.mul_dvd_mul_iff_left pp.pos, IH]
      split  <;> intro h <;> rcases h with ⟨k, h, e⟩
      ·
        exact
          ⟨succ k, succ_le_succ h,
            by 
              rw [e, pow_succₓ] <;> rfl⟩
      cases' k with k
      ·
        apply pp.not_dvd_one.elim 
        simp  at e 
        rw [←e]
        apply dvd_mul_right
      ·
        refine' ⟨k, le_of_succ_le_succ h, _⟩
        rwa [mul_commₓ, pow_succ'ₓ, Nat.mul_left_inj pp.pos] at e
    ·
      split  <;> intro d
      ·
        rw [(pp.coprime_pow_of_not_dvd h).eq_one_of_dvd d]
        exact ⟨0, zero_le _, rfl⟩
      ·
        rcases d with ⟨k, l, e⟩
        rw [e]
        exact pow_dvd_pow _ l

/--
If `p` is prime,
and `a` doesn't divide `p^k`, but `a` does divide `p^(k+1)`
then `a = p^(k+1)`.
-/
theorem eq_prime_pow_of_dvd_least_prime_pow {a p k : ℕ} (pp : prime p) (h₁ : ¬a ∣ p ^ k) (h₂ : a ∣ p ^ k+1) :
  a = p ^ k+1 :=
  by 
    obtain ⟨l, ⟨h, rfl⟩⟩ := (dvd_prime_pow pp).1 h₂ 
    congr 
    exact le_antisymmₓ h (not_leₓ.1 ((not_congr (pow_dvd_pow_iff_le_right (prime.one_lt pp))).1 h₁))

section 

open List

theorem mem_list_primes_of_dvd_prod {p : ℕ} (hp : prime p) :
  ∀ {l : List ℕ}, (∀ p _ : p ∈ l, prime p) → p ∣ Prod l → p ∈ l
| [] => fun h₁ h₂ => absurd h₂ (prime.not_dvd_one hp)
| q :: l =>
  fun h₁ h₂ =>
    have h₃ : p ∣ q*Prod l := @prod_cons _ _ l q ▸ h₂ 
    have hq : prime q := h₁ q (mem_cons_self _ _)
    Or.cases_on ((prime.dvd_mul hp).1 h₃)
      (fun h =>
        by 
          rw [prime.dvd_iff_not_coprime hp, coprime_primes hp hq, Ne.def, not_not] at h <;> exact h ▸ mem_cons_self _ _)
      fun h =>
        have hl : ∀ p _ : p ∈ l, prime p := fun p hlp => h₁ p ((mem_cons_iff _ _ _).2 (Or.inr hlp))
        (mem_cons_iff _ _ _).2 (Or.inr (mem_list_primes_of_dvd_prod hl h))

theorem mem_factors_iff_dvd {n p : ℕ} (hn : 0 < n) (hp : prime p) : p ∈ factors n ↔ p ∣ n :=
  ⟨fun h => prod_factors hn ▸ List.dvd_prod h,
    fun h => mem_list_primes_of_dvd_prod hp (@prime_of_mem_factors n) ((prod_factors hn).symm ▸ h)⟩

theorem dvd_of_mem_factors {n p : ℕ} (h : p ∈ n.factors) : p ∣ n :=
  by 
    rcases n.eq_zero_or_pos with (rfl | hn)
    ·
      exact dvd_zero p
    ·
      rwa [←mem_factors_iff_dvd hn (prime_of_mem_factors h)]

theorem mem_factors {n p} (hn : 0 < n) : p ∈ factors n ↔ prime p ∧ p ∣ n :=
  ⟨fun h => ⟨prime_of_mem_factors h, (mem_factors_iff_dvd hn$ prime_of_mem_factors h).mp h⟩,
    fun ⟨hprime, hdvd⟩ => (mem_factors_iff_dvd hn hprime).mpr hdvd⟩

theorem factors_subset_right {n k : ℕ} (h : k ≠ 0) : n.factors ⊆ (n*k).factors :=
  by 
    cases n
    ·
      rw [zero_mul]
      rfl 
    cases n
    ·
      rw [factors_one]
      apply List.nil_subsetₓ 
    intro p hp 
    rw [mem_factors succ_pos'] at hp 
    rw [mem_factors (Nat.mul_posₓ succ_pos' (Nat.pos_of_ne_zeroₓ h))]
    exact ⟨hp.1, hp.2.mul_right k⟩

theorem factors_subset_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) : n.factors ⊆ k.factors :=
  by 
    obtain ⟨a, rfl⟩ := h 
    exact factors_subset_right (right_ne_zero_of_mul h')

theorem perm_of_prod_eq_prod :
  ∀ {l₁ l₂ : List ℕ}, Prod l₁ = Prod l₂ → (∀ p _ : p ∈ l₁, prime p) → (∀ p _ : p ∈ l₂, prime p) → l₁ ~ l₂
| [], [], _, _, _ => perm.nil
| [], a :: l, h₁, h₂, h₃ =>
  have ha : a ∣ 1 := @prod_nil ℕ _ ▸ h₁.symm ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _ 
  absurd ha (prime.not_dvd_one (h₃ a (mem_cons_self _ _)))
| a :: l, [], h₁, h₂, h₃ =>
  have ha : a ∣ 1 := @prod_nil ℕ _ ▸ h₁ ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _ 
  absurd ha (prime.not_dvd_one (h₂ a (mem_cons_self _ _)))
| a :: l₁, b :: l₂, h, hl₁, hl₂ =>
  have hl₁' : ∀ p _ : p ∈ l₁, prime p := fun p hp => hl₁ p (mem_cons_of_mem _ hp)
  have hl₂' : ∀ p _ : p ∈ (b :: l₂).erase a, prime p := fun p hp => hl₂ p (mem_of_mem_erase hp)
  have ha : a ∈ b :: l₂ :=
    mem_list_primes_of_dvd_prod (hl₁ a (mem_cons_self _ _)) hl₂
      (h ▸
        by 
          rw [prod_cons] <;> exact dvd_mul_right _ _)
  have hb : b :: l₂ ~ a :: (b :: l₂).erase a := perm_cons_erase ha 
  have hl : Prod l₁ = Prod ((b :: l₂).erase a) :=
    (Nat.mul_right_inj (prime.pos (hl₁ a (mem_cons_self _ _)))).1$
      by 
        rwa [←prod_cons, ←prod_cons, ←hb.prod_eq]
  perm.trans ((perm_of_prod_eq_prod hl hl₁' hl₂').cons _) hb.symm

/-- **Fundamental theorem of arithmetic**-/
theorem factors_unique {n : ℕ} {l : List ℕ} (h₁ : Prod l = n) (h₂ : ∀ p _ : p ∈ l, prime p) : l ~ factors n :=
  have hn : 0 < n :=
    Nat.pos_of_ne_zeroₓ$
      fun h =>
        by 
          rw [h] at *
          clear h 
          induction' l with a l hi
          ·
            exact
              absurd h₁
                (by 
                  decide)
          ·
            rw [prod_cons] at h₁ 
            exact
              Nat.mul_ne_zero (ne_of_ltₓ (prime.pos (h₂ a (mem_cons_self _ _)))).symm
                (hi fun p hp => h₂ p (mem_cons_of_mem _ hp)) h₁ 
  perm_of_prod_eq_prod
    (by 
      rwa [prod_factors hn])
    h₂ (@prime_of_mem_factors _)

theorem prime.factors_pow {p : ℕ} (hp : p.prime) (n : ℕ) : (p ^ n).factors = List.repeat p n :=
  by 
    symm 
    rw [←List.repeat_perm]
    apply Nat.factors_unique (List.prod_repeat p n)
    ·
      intro q hq 
      rwa [eq_of_mem_repeat hq]

end 

theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : prime p) {m n k l : ℕ} (hpm : p ^ k ∣ m)
  (hpn : p ^ l ∣ n) (hpmn : (p ^ (k+l)+1) ∣ m*n) : (p ^ k+1) ∣ m ∨ (p ^ l+1) ∣ n :=
  have hpd : ((p ^ k+l)*p) ∣ m*n :=
    by 
      rwa [pow_succ'ₓ] at hpmn 
  have hpd2 : p ∣ (m*n) / p ^ k+l := dvd_div_of_mul_dvd hpd 
  have hpd3 : p ∣ (m*n) / (p ^ k)*p ^ l :=
    by 
      simpa [pow_addₓ] using hpd2 
  have hpd4 : p ∣ (m / p ^ k)*n / p ^ l :=
    by 
      simpa [Nat.div_mul_div hpm hpn] using hpd3 
  have hpd5 : p ∣ m / p ^ k ∨ p ∣ n / p ^ l := (prime.dvd_mul p_prime).1 hpd4 
  suffices ((p ^ k)*p) ∣ m ∨ ((p ^ l)*p) ∣ n by 
    rwa [pow_succ'ₓ, pow_succ'ₓ]
  hpd5.elim (fun this : p ∣ m / p ^ k => Or.inl$ mul_dvd_of_dvd_div hpm this)
    fun this : p ∣ n / p ^ l => Or.inr$ mul_dvd_of_dvd_div hpn this

/-- The type of prime numbers -/
def primes :=
  { p : ℕ // p.prime }

namespace Primes

instance  : HasRepr Nat.Primes :=
  ⟨fun p => reprₓ p.val⟩

instance inhabited_primes : Inhabited primes :=
  ⟨⟨2, prime_two⟩⟩

instance coe_nat : Coe Nat.Primes ℕ :=
  ⟨Subtype.val⟩

theorem coe_nat_inj (p q : Nat.Primes) : (p : ℕ) = (q : ℕ) → p = q :=
  fun h => Subtype.eq h

end Primes

instance monoid.prime_pow {α : Type _} [Monoidₓ α] : Pow α primes :=
  ⟨fun x p => x ^ p.val⟩

end Nat

/-! ### Primality prover -/


open NormNum

namespace Tactic

namespace NormNum

theorem is_prime_helper (n : ℕ) (h₁ : 1 < n) (h₂ : Nat.minFac n = n) : Nat.Prime n :=
  Nat.prime_def_min_fac.2 ⟨h₁, h₂⟩

theorem min_fac_bit0 (n : ℕ) : Nat.minFac (bit0 n) = 2 :=
  by 
    simp [Nat.min_fac_eq,
      show 2 ∣ bit0 n by 
        simp [bit0_eq_two_mul n]]

/-- A predicate representing partial progress in a proof of `min_fac`. -/
def min_fac_helper (n k : ℕ) : Prop :=
  0 < k ∧ bit1 k ≤ Nat.minFac (bit1 n)

theorem min_fac_helper.n_pos {n k : ℕ} (h : min_fac_helper n k) : 0 < n :=
  pos_iff_ne_zero.2$
    fun e =>
      by 
        rw [e] at h <;> exact not_le_of_lt (Nat.bit1_lt h.1) h.2

theorem min_fac_ne_bit0 {n k : ℕ} : Nat.minFac (bit1 n) ≠ bit0 k :=
  by 
    rw [bit0_eq_two_mul]
    refine' fun e => absurd ((Nat.dvd_add_iff_right _).2 (dvd_trans ⟨_, e⟩ (Nat.min_fac_dvd _))) _ <;> simp 

-- error in Data.Nat.Prime: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem min_fac_helper_0 (n : exprℕ()) (h : «expr < »(0, n)) : min_fac_helper n 1 :=
begin
  refine [expr ⟨zero_lt_one, lt_of_le_of_ne _ min_fac_ne_bit0.symm⟩],
  refine [expr @lt_of_le_of_ne exprℕ() _ _ _ (nat.min_fac_pos _) _],
  intro [ident e],
  have [] [] [":=", expr nat.min_fac_prime _],
  { rw ["<-", expr e] ["at", ident this],
    exact [expr nat.not_prime_one this] },
  { exact [expr ne_of_gt (nat.bit1_lt h)] }
end

theorem min_fac_helper_1 {n k k' : ℕ} (e : (k+1) = k') (np : Nat.minFac (bit1 n) ≠ bit1 k) (h : min_fac_helper n k) :
  min_fac_helper n k' :=
  by 
    rw [←e]
    refine'
      ⟨Nat.succ_posₓ _, (lt_of_le_of_neₓ (lt_of_le_of_neₓ _ _ : ((k+1)+k) < _) min_fac_ne_bit0.symm : bit0 (k+1) < _)⟩
    ·
      rw [add_right_commₓ]
      exact h.2
    ·
      rw [add_right_commₓ]
      exact np.symm

theorem min_fac_helper_2 (n k k' : ℕ) (e : (k+1) = k') (np : ¬Nat.Prime (bit1 k)) (h : min_fac_helper n k) :
  min_fac_helper n k' :=
  by 
    refine' min_fac_helper_1 e _ h 
    intro e₁ 
    rw [←e₁] at np 
    exact np (Nat.min_fac_prime$ ne_of_gtₓ$ Nat.bit1_lt h.n_pos)

theorem min_fac_helper_3 (n k k' c : ℕ) (e : (k+1) = k') (nc : bit1 n % bit1 k = c) (c0 : 0 < c)
  (h : min_fac_helper n k) : min_fac_helper n k' :=
  by 
    refine' min_fac_helper_1 e _ h 
    refine' mt _ (ne_of_gtₓ c0)
    intro e₁ 
    rw [←nc, ←Nat.dvd_iff_mod_eq_zeroₓ, ←e₁]
    apply Nat.min_fac_dvd

theorem min_fac_helper_4 (n k : ℕ) (hd : bit1 n % bit1 k = 0) (h : min_fac_helper n k) : Nat.minFac (bit1 n) = bit1 k :=
  by 
    rw [←Nat.dvd_iff_mod_eq_zeroₓ] at hd <;> exact le_antisymmₓ (Nat.min_fac_le_of_dvd (Nat.bit1_lt h.1) hd) h.2

-- error in Data.Nat.Prime: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem min_fac_helper_5
(n k k' : exprℕ())
(e : «expr = »(«expr * »(bit1 k, bit1 k), k'))
(hd : «expr < »(bit1 n, k'))
(h : min_fac_helper n k) : «expr = »(nat.min_fac (bit1 n), bit1 n) :=
begin
  refine [expr (nat.prime_def_min_fac.1 (nat.prime_def_le_sqrt.2 ⟨nat.bit1_lt h.n_pos, _⟩)).2],
  rw ["<-", expr e] ["at", ident hd],
  intros [ident m, ident m2, ident hm, ident md],
  have [] [] [":=", expr le_trans h.2 (le_trans (nat.min_fac_le_of_dvd m2 md) hm)],
  rw [expr nat.le_sqrt] ["at", ident this],
  exact [expr not_le_of_lt hd this]
end

/-- Given `e` a natural numeral and `d : nat` a factor of it, return `⊢ ¬ prime e`. -/
unsafe def prove_non_prime (e : expr) (n d₁ : ℕ) : tactic expr :=
  do 
    let e₁ := reflect d₁ 
    let c ← mk_instance_cache (quote.1 Nat)
    let (c, p₁) ← prove_lt_nat c (quote.1 1) e₁ 
    let d₂ := n / d₁ 
    let e₂ := reflect d₂ 
    let (c, e', p) ← prove_mul_nat c e₁ e₂ 
    guardₓ (e' =ₐ e)
    let (c, p₂) ← prove_lt_nat c (quote.1 1) e₂ 
    return$ (quote.1 @Nat.not_prime_mul').mk_app [e₁, e₂, e, p, p₁, p₂]

/-- Given `a`,`a1 := bit1 a`, `n1` the value of `a1`, `b` and `p : min_fac_helper a b`,
  returns `(c, ⊢ min_fac a1 = c)`. -/
unsafe def prove_min_fac_aux (a a1 : expr) (n1 : ℕ) :
  instance_cache → expr → expr → tactic (instance_cache × expr × expr)
| ic, b, p =>
  do 
    let k ← b.to_nat 
    let k1 := bit1 k 
    let b1 := (quote.1 (bit1 : ℕ → ℕ)).mk_app [b]
    if n1 < k1*k1 then
        do 
          let (ic, e', p₁) ← prove_mul_nat ic b1 b1 
          let (ic, p₂) ← prove_lt_nat ic a1 e' 
          return (ic, a1, (quote.1 min_fac_helper_5).mk_app [a, b, e', p₁, p₂, p])
      else
        let d := k1.min_fac 
        if to_bool (d < k1) then
          do 
            let k' := k+1
            let e' := reflect k' 
            let (ic, p₁) ← prove_succ ic b e' 
            let p₂ ← prove_non_prime b1 k1 d 
            prove_min_fac_aux ic e'$ (quote.1 min_fac_helper_2).mk_app [a, b, e', p₁, p₂, p]
        else
          do 
            let nc := n1 % k1 
            let (ic, c, pc) ← prove_div_mod ic a1 b1 tt 
            if nc = 0 then return (ic, b1, (quote.1 min_fac_helper_4).mk_app [a, b, pc, p]) else
                do 
                  let (ic, p₀) ← prove_pos ic c 
                  let k' := k+1
                  let e' := reflect k' 
                  let (ic, p₁) ← prove_succ ic b e' 
                  prove_min_fac_aux ic e'$ (quote.1 min_fac_helper_3).mk_app [a, b, e', c, p₁, pc, p₀, p]

/-- Given `a` a natural numeral, returns `(b, ⊢ min_fac a = b)`. -/
unsafe def prove_min_fac (ic : instance_cache) (e : expr) : tactic (instance_cache × expr × expr) :=
  match match_numeral e with 
  | match_numeral_result.zero => return (ic, quote.1 (2 : ℕ), quote.1 Nat.min_fac_zero)
  | match_numeral_result.one => return (ic, quote.1 (1 : ℕ), quote.1 Nat.min_fac_one)
  | match_numeral_result.bit0 e => return (ic, quote.1 2, (quote.1 min_fac_bit0).mk_app [e])
  | match_numeral_result.bit1 e =>
    do 
      let n ← e.to_nat 
      let c ← mk_instance_cache (quote.1 Nat)
      let (c, p) ← prove_pos c e 
      let a1 := (quote.1 (bit1 : ℕ → ℕ)).mk_app [e]
      prove_min_fac_aux e a1 (bit1 n) c (quote.1 1) ((quote.1 min_fac_helper_0).mk_app [e, p])
  | _ => failed

/-- A partial proof of `factors`. Asserts that `l` is a sorted list of primes, lower bounded by a
prime `p`, which multiplies to `n`. -/
def factors_helper (n p : ℕ) (l : List ℕ) : Prop :=
  p.prime → List.Chain (· ≤ ·) p l ∧ (∀ a _ : a ∈ l, Nat.Prime a) ∧ List.prod l = n

theorem factors_helper_nil (a : ℕ) : factors_helper 1 a [] :=
  fun pa =>
    ⟨List.Chain.nil,
      by 
        rintro _ ⟨⟩,
      List.prod_nil⟩

theorem factors_helper_cons' (n m a b : ℕ) (l : List ℕ) (h₁ : (b*m) = n) (h₂ : a ≤ b) (h₃ : Nat.minFac b = b)
  (H : factors_helper m b l) : factors_helper n a (b :: l) :=
  fun pa =>
    have pb : b.prime := Nat.prime_def_min_fac.2 ⟨le_transₓ pa.two_le h₂, h₃⟩
    let ⟨f₁, f₂, f₃⟩ := H pb
    ⟨List.Chain.cons h₂ f₁, fun c h => h.elim (fun e => e.symm ▸ pb) (f₂ _),
      by 
        rw [List.prod_cons, f₃, h₁]⟩

theorem factors_helper_cons (n m a b : ℕ) (l : List ℕ) (h₁ : (b*m) = n) (h₂ : a < b) (h₃ : Nat.minFac b = b)
  (H : factors_helper m b l) : factors_helper n a (b :: l) :=
  factors_helper_cons' _ _ _ _ _ h₁ h₂.le h₃ H

theorem factors_helper_sn (n a : ℕ) (h₁ : a < n) (h₂ : Nat.minFac n = n) : factors_helper n a [n] :=
  factors_helper_cons _ _ _ _ _ (mul_oneₓ _) h₁ h₂ (factors_helper_nil _)

theorem factors_helper_same (n m a : ℕ) (l : List ℕ) (h : (a*m) = n) (H : factors_helper m a l) :
  factors_helper n a (a :: l) :=
  fun pa => factors_helper_cons' _ _ _ _ _ h (le_reflₓ _) (Nat.prime_def_min_fac.1 pa).2 H pa

theorem factors_helper_same_sn (a : ℕ) : factors_helper a a [a] :=
  factors_helper_same _ _ _ _ (mul_oneₓ _) (factors_helper_nil _)

theorem factors_helper_end (n : ℕ) (l : List ℕ) (H : factors_helper n 2 l) : Nat.factors n = l :=
  let ⟨h₁, h₂, h₃⟩ := H Nat.prime_two 
  have  := (List.chain'_iff_pairwise (@le_transₓ _ _)).1 (@List.Chain'.tail _ _ (_ :: _) h₁)
  (List.eq_of_perm_of_sorted (Nat.factors_unique h₃ h₂) this (Nat.factors_sorted _)).symm

/-- Given `n` and `a` natural numerals, returns `(l, ⊢ factors_helper n a l)`. -/
unsafe def prove_factors_aux : instance_cache → expr → expr → ℕ → ℕ → tactic (instance_cache × expr × expr)
| c, en, ea, n, a =>
  let b := n.min_fac 
  if b < n then
    do 
      let m := n / b 
      let (c, em) ← c.of_nat m 
      if b = a then
          do 
            let (c, _, p₁) ← prove_mul_nat c ea em 
            let (c, l, p₂) ← prove_factors_aux c em ea m a 
            pure (c, quote.1 ((%%ₓea) :: %%ₓl : List ℕ), (quote.1 factors_helper_same).mk_app [en, em, ea, l, p₁, p₂])
        else
          do 
            let (c, eb) ← c.of_nat b 
            let (c, _, p₁) ← prove_mul_nat c eb em 
            let (c, p₂) ← prove_lt_nat c ea eb 
            let (c, _, p₃) ← prove_min_fac c eb 
            let (c, l, p₄) ← prove_factors_aux c em eb m b 
            pure
                (c, quote.1 ((%%ₓeb) :: %%ₓl : List ℕ),
                (quote.1 factors_helper_cons).mk_app [en, em, ea, eb, l, p₁, p₂, p₃, p₄])
  else
    if b = a then pure (c, quote.1 ([%%ₓea] : List ℕ), (quote.1 factors_helper_same_sn).mk_app [ea]) else
      do 
        let (c, p₁) ← prove_lt_nat c ea en 
        let (c, _, p₂) ← prove_min_fac c en 
        pure (c, quote.1 ([%%ₓen] : List ℕ), (quote.1 factors_helper_sn).mk_app [en, ea, p₁, p₂])

/-- Evaluates the `prime` and `min_fac` functions. -/
@[normNum]
unsafe def eval_prime : expr → tactic (expr × expr)
| quote.1 (Nat.Prime (%%ₓe)) =>
  do 
    let n ← e.to_nat 
    match n with 
      | 0 => false_intro (quote.1 Nat.not_prime_zero)
      | 1 => false_intro (quote.1 Nat.not_prime_one)
      | _ =>
        let d₁ := n.min_fac 
        if d₁ < n then prove_non_prime e n d₁ >>= false_intro else
          do 
            let e₁ := reflect d₁ 
            let c ← mk_instance_cache (quote.1 ℕ)
            let (c, p₁) ← prove_lt_nat c (quote.1 1) e₁ 
            let (c, e₁, p) ← prove_min_fac c e 
            true_intro$ (quote.1 is_prime_helper).mk_app [e, p₁, p]
| quote.1 (Nat.minFac (%%ₓe)) =>
  do 
    let ic ← mk_instance_cache (quote.1 ℕ)
    Prod.snd <$> prove_min_fac ic e
| quote.1 (Nat.factors (%%ₓe)) =>
  do 
    let n ← e.to_nat 
    match n with 
      | 0 => pure (quote.1 (@List.nil ℕ), quote.1 Nat.factors_zero)
      | 1 => pure (quote.1 (@List.nil ℕ), quote.1 Nat.factors_one)
      | _ =>
        do 
          let c ← mk_instance_cache (quote.1 ℕ)
          let (c, l, p) ← prove_factors_aux c e (quote.1 2) n 2
          pure (l, (quote.1 factors_helper_end).mk_app [e, l, p])
| _ => failed

end NormNum

end Tactic

namespace Nat

theorem prime_three : prime 3 :=
  by 
    normNum

end Nat

namespace Nat

/-- The only prime divisor of positive prime power `p^k` is `p` itself -/
theorem prime_pow_prime_divisor {p k : ℕ} (hk : 0 < k) (hp : prime p) : (p ^ k).factors.toFinset = {p} :=
  by 
    rw [hp.factors_pow, List.to_finset_repeat_of_ne_zero hk.ne']

theorem mem_factors_mul_of_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (p : ℕ) :
  p ∈ (a*b).factors ↔ p ∈ a.factors ∨ p ∈ b.factors :=
  by 
    rw [mem_factors (mul_pos ha hb), mem_factors ha, mem_factors hb, ←and_or_distrib_left]
    simpa only [And.congr_right_iff] using prime.dvd_mul

/-- If `a`,`b` are positive the prime divisors of `(a * b)` are the union of those of `a` and `b` -/
theorem factors_mul_of_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
  (a*b).factors.toFinset = a.factors.to_finset ∪ b.factors.to_finset :=
  by 
    ext p 
    simp only [Finset.mem_union, List.mem_to_finset, mem_factors_mul_of_pos ha hb p]

/-- The sets of factors of coprime `a` and `b` are disjoint -/
theorem coprime_factors_disjoint {a b : ℕ} (hab : a.coprime b) : List.Disjoint a.factors b.factors :=
  by 
    intro q hqa hqb 
    apply not_prime_one 
    rw [←eq_one_of_dvd_coprimes hab (dvd_of_mem_factors hqa) (dvd_of_mem_factors hqb)]
    exact prime_of_mem_factors hqa

theorem factors_mul_of_coprime {a b : ℕ} (hab : coprime a b) (p : ℕ) : p ∈ (a*b).factors ↔ p ∈ a.factors ∪ b.factors :=
  by 
    rcases a.eq_zero_or_pos with (rfl | ha)
    ·
      simp [(coprime_zero_left _).mp hab]
    rcases b.eq_zero_or_pos with (rfl | hb)
    ·
      simp [(coprime_zero_right _).mp hab]
    rw [mem_factors_mul_of_pos ha hb p, List.mem_union]

end Nat

