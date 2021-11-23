import Mathbin.Tactic.Linarith.Default

/-!
# Bitwise operations on natural numbers

In the first half of this file, we provide theorems for reasoning about natural numbers from their
bitwise properties. In the second half of this file, we show properties of the bitwise operations
`lor`, `land` and `lxor`, which are defined in core.

## Main results
* `eq_of_test_bit_eq`: two natural numbers are equal if they have equal bits at every position.
* `exists_most_significant_bit`: if `n ≠ 0`, then there is some position `i` that contains the most
  significant `1`-bit of `n`.
* `lt_of_test_bit`: if `n` and `m` are numbers and `i` is a position such that the `i`-th bit of
  of `n` is zero, the `i`-th bit of `m` is one, and all more significant bits are equal, then
  `n < m`.

## Future work

There is another way to express bitwise properties of natural number: `digits 2`. The two ways
should be connected.

## Keywords

bitwise, and, or, xor
-/


open Function

namespace Nat

@[simp]
theorem bit_ff : bit ff = bit0 :=
  rfl

@[simp]
theorem bit_tt : bit tt = bit1 :=
  rfl

@[simp]
theorem bit_eq_zero {n : ℕ} {b : Bool} : n.bit b = 0 ↔ n = 0 ∧ b = ff :=
  by 
    cases b <;> normNum [bit0_eq_zero, Nat.bit1_ne_zero]

-- error in Data.Nat.Bitwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem zero_of_test_bit_eq_ff {n : exprℕ()} (h : ∀ i, «expr = »(test_bit n i, ff)) : «expr = »(n, 0) :=
begin
  induction [expr n] ["using", ident nat.binary_rec] ["with", ident b, ident n, ident hn] [],
  { refl },
  { have [] [":", expr «expr = »(b, ff)] [":=", expr by simpa [] [] [] [] [] ["using", expr h 0]],
    rw ["[", expr this, ",", expr bit_ff, ",", expr bit0_val, ",", expr hn (λ
      i, by rw ["[", "<-", expr h «expr + »(i, 1), ",", expr test_bit_succ, "]"] []), ",", expr mul_zero, "]"] [] }
end

@[simp]
theorem zero_test_bit (i : ℕ) : test_bit 0 i = ff :=
  by 
    simp [test_bit]

/-- Bitwise extensionality: Two numbers agree if they agree at every bit position. -/
theorem eq_of_test_bit_eq {n m : ℕ} (h : ∀ i, test_bit n i = test_bit m i) : n = m :=
  by 
    induction' n using Nat.binaryRec with b n hn generalizing m
    ·
      simp only [zero_test_bit] at h 
      exact (zero_of_test_bit_eq_ff fun i => (h i).symm).symm 
    induction' m using Nat.binaryRec with b' m hm
    ·
      simp only [zero_test_bit] at h 
      exact zero_of_test_bit_eq_ff h 
    suffices h' : n = m
    ·
      rw [h',
        show b = b' by 
          simpa using h 0]
    exact
      hn
        fun i =>
          by 
            convert h (i+1) using 1 <;> rw [test_bit_succ]

theorem exists_most_significant_bit {n : ℕ} (h : n ≠ 0) : ∃ i, test_bit n i = tt ∧ ∀ j, i < j → test_bit n j = ff :=
  by 
    induction' n using Nat.binaryRec with b n hn
    ·
      exact False.elim (h rfl)
    byCases' h' : n = 0
    ·
      subst h' 
      rw
        [show b = tt by 
          revert h 
          cases b <;> simp ]
      refine'
        ⟨0,
          ⟨by 
              rw [test_bit_zero],
            fun j hj => _⟩⟩
      obtain ⟨j', rfl⟩ := exists_eq_succ_of_ne_zero (ne_of_gtₓ hj)
      rw [test_bit_succ, zero_test_bit]
    ·
      obtain ⟨k, ⟨hk, hk'⟩⟩ := hn h' 
      refine'
        ⟨k+1,
          ⟨by 
              rw [test_bit_succ, hk],
            fun j hj => _⟩⟩
      obtain ⟨j', rfl⟩ :=
        exists_eq_succ_of_ne_zero
          (show j ≠ 0 by 
            linarith)
      exact (test_bit_succ _ _ _).trans (hk' _ (lt_of_succ_lt_succ hj))

-- error in Data.Nat.Bitwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lt_of_test_bit
{n m : exprℕ()}
(i : exprℕ())
(hn : «expr = »(test_bit n i, ff))
(hm : «expr = »(test_bit m i, tt))
(hnm : ∀ j, «expr < »(i, j) → «expr = »(test_bit n j, test_bit m j)) : «expr < »(n, m) :=
begin
  induction [expr n] ["using", ident nat.binary_rec] ["with", ident b, ident n, ident hn'] ["generalizing", ident i, ident m],
  { contrapose ["!"] [ident hm],
    rw [expr le_zero_iff] ["at", ident hm],
    simp [] [] [] ["[", expr hm, "]"] [] [] },
  induction [expr m] ["using", ident nat.binary_rec] ["with", ident b', ident m, ident hm'] ["generalizing", ident i],
  { exact [expr false.elim (bool.ff_ne_tt ((zero_test_bit i).symm.trans hm))] },
  by_cases [expr hi, ":", expr «expr = »(i, 0)],
  { subst [expr hi],
    simp [] [] ["only"] ["[", expr test_bit_zero, "]"] [] ["at", ident hn, ident hm],
    have [] [":", expr «expr = »(n, m)] [],
    { exact [expr eq_of_test_bit_eq (λ
        i, by convert [] [expr hnm «expr + »(i, 1) exprdec_trivial()] ["using", 1]; rw [expr test_bit_succ] [])] },
    rw ["[", expr hn, ",", expr hm, ",", expr this, ",", expr bit_ff, ",", expr bit_tt, ",", expr bit0_val, ",", expr bit1_val, "]"] [],
    exact [expr lt_add_one _] },
  { obtain ["⟨", ident i', ",", ident rfl, "⟩", ":=", expr exists_eq_succ_of_ne_zero hi],
    simp [] [] ["only"] ["[", expr test_bit_succ, "]"] [] ["at", ident hn, ident hm],
    have [] [] [":=", expr hn' _ hn hm (λ
      j hj, by convert [] [expr hnm j.succ (succ_lt_succ hj)] ["using", 1]; rw [expr test_bit_succ] [])],
    cases [expr b] []; cases [expr b'] []; simp [] [] ["only"] ["[", expr bit_ff, ",", expr bit_tt, ",", expr bit0_val n, ",", expr bit1_val n, ",", expr bit0_val m, ",", expr bit1_val m, "]"] [] []; linarith [] [] [] }
end

@[simp]
theorem test_bit_two_pow_self (n : ℕ) : test_bit (2 ^ n) n = tt :=
  by 
    rw [test_bit, shiftr_eq_div_pow, Nat.div_selfₓ (pow_pos zero_lt_two n), bodd_one]

theorem test_bit_two_pow_of_ne {n m : ℕ} (hm : n ≠ m) : test_bit (2 ^ n) m = ff :=
  by 
    rw [test_bit, shiftr_eq_div_pow]
    cases' hm.lt_or_lt with hm hm
    ·
      rw [Nat.div_eq_zero, bodd_zero]
      exact Nat.pow_lt_pow_of_lt_right one_lt_two hm
    ·
      rw [pow_div hm.le zero_lt_two, ←tsub_add_cancel_of_le (succ_le_of_lt$ tsub_pos_of_lt hm)]
      simp [pow_succₓ]

theorem test_bit_two_pow (n m : ℕ) : test_bit (2 ^ n) m = (n = m) :=
  by 
    byCases' n = m
    ·
      cases h 
      simp 
    ·
      rw [test_bit_two_pow_of_ne h]
      simp [h]

/-- If `f` is a commutative operation on bools such that `f ff ff = ff`, then `bitwise f` is also
    commutative. -/
theorem bitwise_comm {f : Bool → Bool → Bool} (hf : ∀ b b', f b b' = f b' b) (hf' : f ff ff = ff) (n m : ℕ) :
  bitwise f n m = bitwise f m n :=
  suffices bitwise f = swap (bitwise f)by 
    convLHS => rw [this]
  calc bitwise f = bitwise (swap f) := congr_argₓ _$ funext$ fun _ => funext$ hf _ 
    _ = swap (bitwise f) := bitwise_swap hf'
    

theorem lor_comm (n m : ℕ) : lor n m = lor m n :=
  bitwise_comm Bool.bor_comm rfl n m

theorem land_comm (n m : ℕ) : land n m = land m n :=
  bitwise_comm Bool.band_comm rfl n m

theorem lxor_comm (n m : ℕ) : lxor n m = lxor m n :=
  bitwise_comm Bool.bxor_comm rfl n m

@[simp]
theorem zero_lxor (n : ℕ) : lxor 0 n = n :=
  by 
    simp [lxor]

@[simp]
theorem lxor_zero (n : ℕ) : lxor n 0 = n :=
  by 
    simp [lxor]

@[simp]
theorem zero_land (n : ℕ) : land 0 n = 0 :=
  by 
    simp [land]

@[simp]
theorem land_zero (n : ℕ) : land n 0 = 0 :=
  by 
    simp [land]

@[simp]
theorem zero_lor (n : ℕ) : lor 0 n = n :=
  by 
    simp [lor]

@[simp]
theorem lor_zero (n : ℕ) : lor n 0 = n :=
  by 
    simp [lor]

/-- Proving associativity of bitwise operations in general essentially boils down to a huge case
    distinction, so it is shorter to use this tactic instead of proving it in the general case. -/
unsafe def bitwise_assoc_tac : tactic Unit :=
  sorry

theorem lxor_assoc (n m k : ℕ) : lxor (lxor n m) k = lxor n (lxor m k) :=
  by 
    runTac 
      bitwise_assoc_tac

theorem land_assoc (n m k : ℕ) : land (land n m) k = land n (land m k) :=
  by 
    runTac 
      bitwise_assoc_tac

theorem lor_assoc (n m k : ℕ) : lor (lor n m) k = lor n (lor m k) :=
  by 
    runTac 
      bitwise_assoc_tac

@[simp]
theorem lxor_self (n : ℕ) : lxor n n = 0 :=
  zero_of_test_bit_eq_ff$
    fun i =>
      by 
        simp 

theorem lxor_right_inj {n m m' : ℕ} (h : lxor n m = lxor n m') : m = m' :=
  calc m = lxor n (lxor n m') :=
    by 
      simp [←lxor_assoc, ←h]
    _ = m' :=
    by 
      simp [←lxor_assoc]
    

theorem lxor_left_inj {n n' m : ℕ} (h : lxor n m = lxor n' m) : n = n' :=
  by 
    rw [lxor_comm n m, lxor_comm n' m] at h 
    exact lxor_right_inj h

theorem lxor_eq_zero {n m : ℕ} : lxor n m = 0 ↔ n = m :=
  ⟨by 
      rw [←lxor_self m]
      exact lxor_left_inj,
    by 
      rintro rfl 
      exact lxor_self _⟩

-- error in Data.Nat.Bitwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lxor_trichotomy
{a b c : exprℕ()}
(h : «expr ≠ »(lxor a (lxor b c), 0)) : «expr ∨ »(«expr < »(lxor b c, a), «expr ∨ »(«expr < »(lxor a c, b), «expr < »(lxor a b, c))) :=
begin
  set [] [ident v] [] [":="] [expr lxor a (lxor b c)] ["with", ident hv],
  have [ident hab] [":", expr «expr = »(lxor a b, lxor c v)] [],
  { rw [expr hv] [],
    conv_rhs [] [] { rw [expr lxor_comm],
      simp [] ["[", expr lxor_assoc, "]"] [] } },
  have [ident hac] [":", expr «expr = »(lxor a c, lxor b v)] [],
  { rw [expr hv] [],
    conv_rhs [] [] { congr,
      skip,
      rw [expr lxor_comm] },
    rw ["[", "<-", expr lxor_assoc, ",", "<-", expr lxor_assoc, ",", expr lxor_self, ",", expr zero_lxor, ",", expr lxor_comm, "]"] [] },
  have [ident hbc] [":", expr «expr = »(lxor b c, lxor a v)] [],
  { simp [] [] [] ["[", expr hv, ",", "<-", expr lxor_assoc, "]"] [] [] },
  obtain ["⟨", ident i, ",", "⟨", ident hi, ",", ident hi', "⟩", "⟩", ":=", expr exists_most_significant_bit h],
  have [] [":", expr «expr ∨ »(«expr = »(test_bit a i, tt), «expr ∨ »(«expr = »(test_bit b i, tt), «expr = »(test_bit c i, tt)))] [],
  { contrapose ["!"] [ident hi],
    simp [] [] ["only"] ["[", expr eq_ff_eq_not_eq_tt, ",", expr ne, ",", expr test_bit_lxor, "]"] [] ["at", "⊢", ident hi],
    rw ["[", expr hi.1, ",", expr hi.2.1, ",", expr hi.2.2, ",", expr bxor_ff, ",", expr bxor_ff, "]"] [] },
  rcases [expr this, "with", ident h, "|", ident h, "|", ident h]; [{ left,
     rw [expr hbc] [] }, { right,
     left,
     rw [expr hac] [] }, { right,
     right,
     rw [expr hab] [] }]; exact [expr lt_of_test_bit i (by simp [] [] [] ["[", expr h, ",", expr hi, "]"] [] []) h (λ
    j hj, by simp [] [] [] ["[", expr hi' _ hj, "]"] [] [])]
end

end Nat

