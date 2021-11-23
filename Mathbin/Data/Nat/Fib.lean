import Mathbin.Data.Nat.Gcd 
import Mathbin.Data.Stream.Init 
import Mathbin.Tactic.Ring

/-!
# The Fibonacci Sequence

## Summary

Definition of the Fibonacci sequence `F₀ = 0, F₁ = 1, Fₙ₊₂ = Fₙ + Fₙ₊₁`.

## Main Definitions

- `fib` returns the stream of Fibonacci numbers.

## Main Statements

- `fib_succ_succ` : shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.`.
- `fib_gcd`       : `fib n` is a strong divisibility sequence.

## Implementation Notes

For efficiency purposes, the sequence is defined using `stream.iterate`.

## Tags

fib, fibonacci
-/


namespace Nat

/-- Auxiliary function used in the definition of `fib_aux_stream`. -/
private def fib_aux_step : ℕ × ℕ → ℕ × ℕ :=
  fun p => ⟨p.snd, p.fst+p.snd⟩

/-- Auxiliary stream creating Fibonacci pairs `⟨Fₙ, Fₙ₊₁⟩`. -/
private def fib_aux_stream : Streamₓ (ℕ × ℕ) :=
  Streamₓ.iterate fib_aux_step ⟨0, 1⟩

/--
Implementation of the fibonacci sequence satisfying
`fib 0 = 0, fib 1 = 1, fib (n + 2) = fib n + fib (n + 1)`.

*Note:* We use a stream iterator for better performance when compared to the naive recursive
implementation.
-/
@[pp_nodot]
def fib (n : ℕ) : ℕ :=
  (fib_aux_stream n).fst

@[simp]
theorem fib_zero : fib 0 = 0 :=
  rfl

@[simp]
theorem fib_one : fib 1 = 1 :=
  rfl

@[simp]
theorem fib_two : fib 2 = 1 :=
  rfl

private theorem fib_aux_stream_succ {n : ℕ} : fib_aux_stream (n+1) = fib_aux_step (fib_aux_stream n) :=
  by 
    change
      (Streamₓ.nth (n+1)$ Streamₓ.iterate fib_aux_step ⟨0, 1⟩) =
        fib_aux_step (Streamₓ.nth n$ Streamₓ.iterate fib_aux_step ⟨0, 1⟩)
    rw [Streamₓ.nth_succ_iterate, Streamₓ.map_iterate, Streamₓ.nth_map]

/-- Shows that `fib` indeed satisfies the Fibonacci recurrence `Fₙ₊₂ = Fₙ + Fₙ₊₁.` -/
theorem fib_succ_succ {n : ℕ} : fib (n+2) = fib n+fib (n+1) :=
  by 
    simp only [fib, fib_aux_stream_succ, fib_aux_step]

-- error in Data.Nat.Fib: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fib_pos {n : exprℕ()} (n_pos : «expr < »(0, n)) : «expr < »(0, fib n) :=
begin
  induction [expr n] [] ["with", ident n, ident IH] [],
  case [ident nat.zero] { norm_num [] ["at", ident n_pos] },
  case [ident nat.succ] { cases [expr n] [],
    case [ident nat.zero] { simp [] [] [] ["[", expr fib_succ_succ, ",", expr zero_lt_one, "]"] [] [] },
    case [ident nat.succ] { have [] [":", expr «expr ≤ »(0, fib n)] [],
      by simp [] [] [] [] [] [],
      exact [expr «expr $ »(lt_add_of_nonneg_of_lt this, IH n.succ_pos)] } }
end

theorem fib_le_fib_succ {n : ℕ} : fib n ≤ fib (n+1) :=
  by 
    cases n <;> simp [fib_succ_succ]

@[mono]
theorem fib_mono : Monotone fib :=
  monotone_nat_of_le_succ$ fun _ => fib_le_fib_succ

/-- `fib (n + 2)` is strictly monotone. -/
theorem fib_add_two_strict_mono : StrictMono fun n => fib (n+2) :=
  strict_mono_nat_of_lt_succ$ fun n => lt_add_of_pos_left _$ fib_pos succ_pos'

-- error in Data.Nat.Fib: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem le_fib_self {n : exprℕ()} (five_le_n : «expr ≤ »(5, n)) : «expr ≤ »(n, fib n) :=
begin
  induction [expr five_le_n] [] ["with", ident n, ident five_le_n, ident IH] [],
  { have [] [":", expr «expr = »(5, fib 5)] [],
    by refl,
    exact [expr le_of_eq this] },
  { cases [expr n] ["with", ident n'],
    { have [] [":", expr «expr = »(5, 0)] [],
      from [expr nat.le_zero_iff.elim_left five_le_n],
      contradiction },
    rw [expr fib_succ_succ] [],
    suffices [] [":", expr «expr ≤ »(«expr + »(1, «expr + »(n', 1)), «expr + »(fib n', fib «expr + »(n', 1)))],
    by rwa ["[", expr nat.succ_eq_add_one, ",", expr add_comm, "]"] [],
    have [] [":", expr «expr ≠ »(n', 0)] [],
    by { intro [ident h],
      have [] [":", expr «expr ≤ »(5, 1)] [],
      by rwa [expr h] ["at", ident five_le_n],
      norm_num [] ["at", ident this] },
    have [] [":", expr «expr ≤ »(1, fib n')] [],
    from [expr nat.succ_le_of_lt «expr $ »(fib_pos, pos_iff_ne_zero.mpr this)],
    mono [] [] [] [] }
end

/-- Subsequent Fibonacci numbers are coprime,
  see https://proofwiki.org/wiki/Consecutive_Fibonacci_Numbers_are_Coprime -/
theorem fib_coprime_fib_succ (n : ℕ) : Nat.Coprime (fib n) (fib (n+1)) :=
  by 
    unfold coprime 
    induction' n with n ih
    ·
      simp 
    ·
      convert ih using 1
      rw [fib_succ_succ, succ_eq_add_one, gcd_rec, add_mod_right, gcd_comm (fib n), gcd_rec (fib (n+1))]

/-- See https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers -/
theorem fib_add (m n : ℕ) : ((fib m*fib n)+fib (m+1)*fib (n+1)) = fib ((m+n)+1) :=
  by 
    induction' n with n ih generalizing m
    ·
      simp 
    ·
      intros 
      specialize ih (m+1)
      rw [add_assocₓ m 1 n, add_commₓ 1 n] at ih 
      simp only [fib_succ_succ, ←ih]
      ring

theorem gcd_fib_add_self (m n : ℕ) : gcd (fib m) (fib (n+m)) = gcd (fib m) (fib n) :=
  by 
    cases Nat.eq_zero_or_posₓ n
    ·
      rw [h]
      simp 
    replace h := Nat.succ_pred_eq_of_posₓ h 
    rw [←h, succ_eq_add_one]
    calc gcd (fib m) (fib ((n.pred+1)+m)) = gcd (fib m) ((fib n.pred*fib m)+fib (n.pred+1)*fib (m+1)) :=
      by 
        rw [fib_add n.pred _]
        ringNF _ = gcd (fib m) (fib (n.pred+1)*fib (m+1)) :=
      by 
        rw [add_commₓ, gcd_add_mul_self (fib m) _ (fib n.pred)]_ = gcd (fib m) (fib (n.pred+1)) :=
      coprime.gcd_mul_right_cancel_right (fib (n.pred+1)) (coprime.symm (fib_coprime_fib_succ m))

theorem gcd_fib_add_mul_self (m n : ℕ) : ∀ k, gcd (fib m) (fib (n+k*m)) = gcd (fib m) (fib n)
| 0 =>
  by 
    simp 
| k+1 =>
  by 
    rw [←gcd_fib_add_mul_self k, add_mulₓ, ←add_assocₓ, one_mulₓ, gcd_fib_add_self _ _]

/-- `fib n` is a strong divisibility sequence,
  see https://proofwiki.org/wiki/GCD_of_Fibonacci_Numbers -/
theorem fib_gcd (m n : ℕ) : fib (gcd m n) = gcd (fib m) (fib n) :=
  by 
    wlog h : m ≤ n using n m, m n 
    exact le_totalₓ m n
    ·
      apply gcd.induction m n
      ·
        simp 
      intro m n mpos h 
      rw [←gcd_rec m n] at h 
      convRHS => rw [←mod_add_div' n m]
      rwa [gcd_fib_add_mul_self m (n % m) (n / m), gcd_comm (fib m) _]
    rwa [gcd_comm, gcd_comm (fib m)]

theorem fib_dvd (m n : ℕ) (h : m ∣ n) : fib m ∣ fib n :=
  by 
    rwa [gcd_eq_left_iff_dvd, ←fib_gcd, gcd_eq_left_iff_dvd.mp]

end Nat

