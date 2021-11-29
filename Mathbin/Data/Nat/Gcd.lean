import Mathbin.Algebra.GroupPower.Order

/-!
# Definitions and properties of `gcd`, `lcm`, and `coprime`

-/


namespace Nat

/-! ### `gcd` -/


theorem gcd_dvd (m n : ℕ) : gcd m n ∣ m ∧ gcd m n ∣ n :=
  gcd.induction m n
    (fun n =>
      by 
        rw [gcd_zero_left] <;> exact ⟨dvd_zero n, dvd_refl n⟩)
    fun m n npos =>
      by 
        rw [←gcd_rec] <;> exact fun ⟨IH₁, IH₂⟩ => ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩

theorem gcd_dvd_left (m n : ℕ) : gcd m n ∣ m :=
  (gcd_dvd m n).left

theorem gcd_dvd_right (m n : ℕ) : gcd m n ∣ n :=
  (gcd_dvd m n).right

theorem gcd_le_left {m} n (h : 0 < m) : gcd m n ≤ m :=
  le_of_dvd h$ gcd_dvd_left m n

theorem gcd_le_right m {n} (h : 0 < n) : gcd m n ≤ n :=
  le_of_dvd h$ gcd_dvd_right m n

theorem dvd_gcd {m n k : ℕ} : k ∣ m → k ∣ n → k ∣ gcd m n :=
  gcd.induction m n
    (fun n _ kn =>
      by 
        rw [gcd_zero_left] <;> exact kn)
    fun n m mpos IH H1 H2 =>
      by 
        rw [gcd_rec] <;> exact IH ((dvd_mod_iff H1).2 H2) H1

theorem dvd_gcd_iff {m n k : ℕ} : k ∣ gcd m n ↔ k ∣ m ∧ k ∣ n :=
  Iff.intro (fun h => ⟨h.trans (gcd_dvd m n).left, h.trans (gcd_dvd m n).right⟩) fun h => dvd_gcd h.left h.right

theorem gcd_comm (m n : ℕ) : gcd m n = gcd n m :=
  dvd_antisymm (dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n)) (dvd_gcd (gcd_dvd_right n m) (gcd_dvd_left n m))

theorem gcd_eq_left_iff_dvd {m n : ℕ} : m ∣ n ↔ gcd m n = m :=
  ⟨fun h =>
      by 
        rw [gcd_rec, mod_eq_zero_of_dvd h, gcd_zero_left],
    fun h => h ▸ gcd_dvd_right m n⟩

theorem gcd_eq_right_iff_dvd {m n : ℕ} : m ∣ n ↔ gcd n m = m :=
  by 
    rw [gcd_comm] <;> apply gcd_eq_left_iff_dvd

theorem gcd_assoc (m n k : ℕ) : gcd (gcd m n) k = gcd m (gcd n k) :=
  dvd_antisymm
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

@[simp]
theorem gcd_one_right (n : ℕ) : gcd n 1 = 1 :=
  Eq.trans (gcd_comm n 1)$ gcd_one_left n

theorem gcd_mul_left (m n k : ℕ) : gcd (m*n) (m*k) = m*gcd n k :=
  gcd.induction n k
    (fun k =>
      by 
        repeat' 
          first |
            rw [mul_zero]|
            rw [gcd_zero_left])
    fun k n H IH =>
      by 
        rwa [←mul_mod_mul_left, ←gcd_rec, ←gcd_rec] at IH

theorem gcd_mul_right (m n k : ℕ) : gcd (m*n) (k*n) = gcd m k*n :=
  by 
    rw [mul_commₓ m n, mul_commₓ k n, mul_commₓ (gcd m k) n, gcd_mul_left]

theorem gcd_pos_of_pos_left {m : ℕ} (n : ℕ) (mpos : 0 < m) : 0 < gcd m n :=
  pos_of_dvd_of_pos (gcd_dvd_left m n) mpos

theorem gcd_pos_of_pos_right (m : ℕ) {n : ℕ} (npos : 0 < n) : 0 < gcd m n :=
  pos_of_dvd_of_pos (gcd_dvd_right m n) npos

-- error in Data.Nat.Gcd: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem eq_zero_of_gcd_eq_zero_left {m n : exprℕ()} (H : «expr = »(gcd m n, 0)) : «expr = »(m, 0) :=
or.elim (nat.eq_zero_or_pos m) id (assume
 H1 : «expr < »(0, m), absurd (eq.symm H) (ne_of_lt (gcd_pos_of_pos_left _ H1)))

theorem eq_zero_of_gcd_eq_zero_right {m n : ℕ} (H : gcd m n = 0) : n = 0 :=
  by 
    rw [gcd_comm] at H <;> exact eq_zero_of_gcd_eq_zero_left H

theorem gcd_div {m n k : ℕ} (H1 : k ∣ m) (H2 : k ∣ n) : gcd (m / k) (n / k) = gcd m n / k :=
  Or.elim (Nat.eq_zero_or_posₓ k)
    (fun k0 =>
      by 
        rw [k0, Nat.div_zeroₓ, Nat.div_zeroₓ, Nat.div_zeroₓ, gcd_zero_right])
    fun H3 =>
      Nat.eq_of_mul_eq_mul_rightₓ H3$
        by 
          rw [Nat.div_mul_cancelₓ (dvd_gcd H1 H2), ←gcd_mul_right, Nat.div_mul_cancelₓ H1, Nat.div_mul_cancelₓ H2]

theorem gcd_dvd_gcd_of_dvd_left {m k : ℕ} (n : ℕ) (H : m ∣ k) : gcd m n ∣ gcd k n :=
  dvd_gcd ((gcd_dvd_left m n).trans H) (gcd_dvd_right m n)

theorem gcd_dvd_gcd_of_dvd_right {m k : ℕ} (n : ℕ) (H : m ∣ k) : gcd n m ∣ gcd n k :=
  dvd_gcd (gcd_dvd_left n m) ((gcd_dvd_right n m).trans H)

theorem gcd_dvd_gcd_mul_left (m n k : ℕ) : gcd m n ∣ gcd (k*m) n :=
  gcd_dvd_gcd_of_dvd_left _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right (m n k : ℕ) : gcd m n ∣ gcd (m*k) n :=
  gcd_dvd_gcd_of_dvd_left _ (dvd_mul_right _ _)

theorem gcd_dvd_gcd_mul_left_right (m n k : ℕ) : gcd m n ∣ gcd m (k*n) :=
  gcd_dvd_gcd_of_dvd_right _ (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (m n k : ℕ) : gcd m n ∣ gcd m (n*k) :=
  gcd_dvd_gcd_of_dvd_right _ (dvd_mul_right _ _)

theorem gcd_eq_left {m n : ℕ} (H : m ∣ n) : gcd m n = m :=
  dvd_antisymm (gcd_dvd_left _ _) (dvd_gcd dvd_rfl H)

theorem gcd_eq_right {m n : ℕ} (H : n ∣ m) : gcd m n = n :=
  by 
    rw [gcd_comm, gcd_eq_left H]

@[simp]
theorem gcd_mul_left_left (m n : ℕ) : gcd (m*n) n = n :=
  dvd_antisymm (gcd_dvd_right _ _) (dvd_gcd (dvd_mul_left _ _) dvd_rfl)

@[simp]
theorem gcd_mul_left_right (m n : ℕ) : gcd n (m*n) = n :=
  by 
    rw [gcd_comm, gcd_mul_left_left]

@[simp]
theorem gcd_mul_right_left (m n : ℕ) : gcd (n*m) n = n :=
  by 
    rw [mul_commₓ, gcd_mul_left_left]

@[simp]
theorem gcd_mul_right_right (m n : ℕ) : gcd n (n*m) = n :=
  by 
    rw [gcd_comm, gcd_mul_right_left]

@[simp]
theorem gcd_gcd_self_right_left (m n : ℕ) : gcd m (gcd m n) = gcd m n :=
  dvd_antisymm (gcd_dvd_right _ _) (dvd_gcd (gcd_dvd_left _ _) dvd_rfl)

@[simp]
theorem gcd_gcd_self_right_right (m n : ℕ) : gcd m (gcd n m) = gcd n m :=
  by 
    rw [gcd_comm n m, gcd_gcd_self_right_left]

@[simp]
theorem gcd_gcd_self_left_right (m n : ℕ) : gcd (gcd n m) m = gcd n m :=
  by 
    rw [gcd_comm, gcd_gcd_self_right_right]

@[simp]
theorem gcd_gcd_self_left_left (m n : ℕ) : gcd (gcd m n) m = gcd m n :=
  by 
    rw [gcd_comm m n, gcd_gcd_self_left_right]

theorem gcd_add_mul_self (m n k : ℕ) : gcd m (n+k*m) = gcd m n :=
  by 
    simp [gcd_rec m (n+k*m), gcd_rec m n]

theorem gcd_eq_zero_iff {i j : ℕ} : gcd i j = 0 ↔ i = 0 ∧ j = 0 :=
  by 
    split 
    ·
      intro h 
      exact ⟨eq_zero_of_gcd_eq_zero_left h, eq_zero_of_gcd_eq_zero_right h⟩
    ·
      intro h 
      rw [h.1, h.2]
      exact Nat.gcd_zero_rightₓ _

/-! ### `lcm` -/


theorem lcm_comm (m n : ℕ) : lcm m n = lcm n m :=
  by 
    delta' lcm <;> rw [mul_commₓ, gcd_comm]

@[simp]
theorem lcm_zero_left (m : ℕ) : lcm 0 m = 0 :=
  by 
    delta' lcm <;> rw [zero_mul, Nat.zero_divₓ]

@[simp]
theorem lcm_zero_right (m : ℕ) : lcm m 0 = 0 :=
  lcm_comm 0 m ▸ lcm_zero_left m

@[simp]
theorem lcm_one_left (m : ℕ) : lcm 1 m = m :=
  by 
    delta' lcm <;> rw [one_mulₓ, gcd_one_left, Nat.div_oneₓ]

@[simp]
theorem lcm_one_right (m : ℕ) : lcm m 1 = m :=
  lcm_comm 1 m ▸ lcm_one_left m

@[simp]
theorem lcm_self (m : ℕ) : lcm m m = m :=
  Or.elim (Nat.eq_zero_or_posₓ m)
    (fun h =>
      by 
        rw [h, lcm_zero_left])
    fun h =>
      by 
        delta' lcm <;> rw [gcd_self, Nat.mul_div_cancelₓ _ h]

theorem dvd_lcm_left (m n : ℕ) : m ∣ lcm m n :=
  Dvd.intro (n / gcd m n) (Nat.mul_div_assocₓ _$ gcd_dvd_right m n).symm

theorem dvd_lcm_right (m n : ℕ) : n ∣ lcm m n :=
  lcm_comm n m ▸ dvd_lcm_left n m

theorem gcd_mul_lcm (m n : ℕ) : (gcd m n*lcm m n) = m*n :=
  by 
    delta' lcm <;> rw [Nat.mul_div_cancel'ₓ ((gcd_dvd_left m n).trans (dvd_mul_right m n))]

theorem lcm_dvd {m n k : ℕ} (H1 : m ∣ k) (H2 : n ∣ k) : lcm m n ∣ k :=
  Or.elim (Nat.eq_zero_or_posₓ k)
    (fun h =>
      by 
        rw [h] <;> exact dvd_zero _)
    fun kpos =>
      dvd_of_mul_dvd_mul_left (gcd_pos_of_pos_left n (pos_of_dvd_of_pos H1 kpos))$
        by 
          rw [gcd_mul_lcm, ←gcd_mul_right, mul_commₓ n k] <;>
            exact dvd_gcd (mul_dvd_mul_left _ H2) (mul_dvd_mul_right H1 _)

theorem lcm_dvd_iff {m n k : ℕ} : lcm m n ∣ k ↔ m ∣ k ∧ n ∣ k :=
  ⟨fun h => ⟨(dvd_lcm_left _ _).trans h, (dvd_lcm_right _ _).trans h⟩, and_imp.2 lcm_dvd⟩

theorem lcm_assoc (m n k : ℕ) : lcm (lcm m n) k = lcm m (lcm n k) :=
  dvd_antisymm
    (lcm_dvd (lcm_dvd (dvd_lcm_left m (lcm n k)) ((dvd_lcm_left n k).trans (dvd_lcm_right m (lcm n k))))
      ((dvd_lcm_right n k).trans (dvd_lcm_right m (lcm n k))))
    (lcm_dvd ((dvd_lcm_left m n).trans (dvd_lcm_left (lcm m n) k))
      (lcm_dvd ((dvd_lcm_right m n).trans (dvd_lcm_left (lcm m n) k)) (dvd_lcm_right (lcm m n) k)))

theorem lcm_ne_zero {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : lcm m n ≠ 0 :=
  by 
    intro h 
    simpa [h, hm, hn] using gcd_mul_lcm m n

/-!
### `coprime`

See also `nat.coprime_of_dvd` and `nat.coprime_of_dvd'` to prove `nat.coprime m n`.
-/


instance  (m n : ℕ) : Decidable (coprime m n) :=
  by 
    unfold coprime <;> infer_instance

theorem coprime_iff_gcd_eq_one {m n : ℕ} : coprime m n ↔ gcd m n = 1 :=
  Iff.rfl

theorem coprime.gcd_eq_one {m n : ℕ} (h : coprime m n) : gcd m n = 1 :=
  h

theorem coprime.lcm_eq_mul {m n : ℕ} (h : coprime m n) : lcm m n = m*n :=
  by 
    rw [←one_mulₓ (lcm m n), ←h.gcd_eq_one, gcd_mul_lcm]

theorem coprime.symm {m n : ℕ} : coprime n m → coprime m n :=
  (gcd_comm m n).trans

theorem coprime_comm {m n : ℕ} : coprime n m ↔ coprime m n :=
  ⟨coprime.symm, coprime.symm⟩

theorem coprime.dvd_of_dvd_mul_right {m n k : ℕ} (H1 : coprime k n) (H2 : k ∣ m*n) : k ∣ m :=
  let t := dvd_gcd (dvd_mul_left k m) H2 
  by 
    rwa [gcd_mul_left, H1.gcd_eq_one, mul_oneₓ] at t

theorem coprime.dvd_of_dvd_mul_left {m n k : ℕ} (H1 : coprime k m) (H2 : k ∣ m*n) : k ∣ n :=
  by 
    rw [mul_commₓ] at H2 <;> exact H1.dvd_of_dvd_mul_right H2

theorem coprime.dvd_mul_right {m n k : ℕ} (H : coprime k n) : (k ∣ m*n) ↔ k ∣ m :=
  ⟨H.dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h n⟩

theorem coprime.dvd_mul_left {m n k : ℕ} (H : coprime k m) : (k ∣ m*n) ↔ k ∣ n :=
  ⟨H.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h m⟩

theorem coprime.gcd_mul_left_cancel {k : ℕ} (m : ℕ) {n : ℕ} (H : coprime k n) : gcd (k*m) n = gcd m n :=
  have H1 : coprime (gcd (k*m) n) k :=
    by 
      rw [coprime, gcd_assoc, H.symm.gcd_eq_one, gcd_one_right]
  dvd_antisymm (dvd_gcd (H1.dvd_of_dvd_mul_left (gcd_dvd_left _ _)) (gcd_dvd_right _ _)) (gcd_dvd_gcd_mul_left _ _ _)

theorem coprime.gcd_mul_right_cancel (m : ℕ) {k n : ℕ} (H : coprime k n) : gcd (m*k) n = gcd m n :=
  by 
    rw [mul_commₓ m k, H.gcd_mul_left_cancel m]

theorem coprime.gcd_mul_left_cancel_right {k m : ℕ} (n : ℕ) (H : coprime k m) : gcd m (k*n) = gcd m n :=
  by 
    rw [gcd_comm m n, gcd_comm m (k*n), H.gcd_mul_left_cancel n]

theorem coprime.gcd_mul_right_cancel_right {k m : ℕ} (n : ℕ) (H : coprime k m) : gcd m (n*k) = gcd m n :=
  by 
    rw [mul_commₓ n k, H.gcd_mul_left_cancel_right n]

theorem coprime_div_gcd_div_gcd {m n : ℕ} (H : 0 < gcd m n) : coprime (m / gcd m n) (n / gcd m n) :=
  by 
    rw [coprime_iff_gcd_eq_one, gcd_div (gcd_dvd_left m n) (gcd_dvd_right m n), Nat.div_selfₓ H]

theorem not_coprime_of_dvd_of_dvd {m n d : ℕ} (dgt1 : 1 < d) (Hm : d ∣ m) (Hn : d ∣ n) : ¬coprime m n :=
  fun co =>
    not_lt_of_geₓ
      (le_of_dvd zero_lt_one$
        by 
          rw [←co.gcd_eq_one] <;> exact dvd_gcd Hm Hn)
      dgt1

theorem exists_coprime {m n : ℕ} (H : 0 < gcd m n) : ∃ m' n', coprime m' n' ∧ (m = m'*gcd m n) ∧ n = n'*gcd m n :=
  ⟨_, _, coprime_div_gcd_div_gcd H, (Nat.div_mul_cancelₓ (gcd_dvd_left m n)).symm,
    (Nat.div_mul_cancelₓ (gcd_dvd_right m n)).symm⟩

theorem exists_coprime' {m n : ℕ} (H : 0 < gcd m n) : ∃ g m' n', 0 < g ∧ coprime m' n' ∧ (m = m'*g) ∧ n = n'*g :=
  let ⟨m', n', h⟩ := exists_coprime H
  ⟨_, m', n', H, h⟩

theorem coprime.mul {m n k : ℕ} (H1 : coprime m k) (H2 : coprime n k) : coprime (m*n) k :=
  (H1.gcd_mul_left_cancel n).trans H2

theorem coprime.mul_right {k m n : ℕ} (H1 : coprime k m) (H2 : coprime k n) : coprime k (m*n) :=
  (H1.symm.mul H2.symm).symm

theorem coprime.coprime_dvd_left {m k n : ℕ} (H1 : m ∣ k) (H2 : coprime k n) : coprime m n :=
  eq_one_of_dvd_one
    (by 
      delta' coprime  at H2 <;> rw [←H2] <;> exact gcd_dvd_gcd_of_dvd_left _ H1)

theorem coprime.coprime_dvd_right {m k n : ℕ} (H1 : n ∣ m) (H2 : coprime k m) : coprime k n :=
  (H2.symm.coprime_dvd_left H1).symm

theorem coprime.coprime_mul_left {k m n : ℕ} (H : coprime (k*m) n) : coprime m n :=
  H.coprime_dvd_left (dvd_mul_left _ _)

theorem coprime.coprime_mul_right {k m n : ℕ} (H : coprime (m*k) n) : coprime m n :=
  H.coprime_dvd_left (dvd_mul_right _ _)

theorem coprime.coprime_mul_left_right {k m n : ℕ} (H : coprime m (k*n)) : coprime m n :=
  H.coprime_dvd_right (dvd_mul_left _ _)

theorem coprime.coprime_mul_right_right {k m n : ℕ} (H : coprime m (n*k)) : coprime m n :=
  H.coprime_dvd_right (dvd_mul_right _ _)

theorem coprime.coprime_div_left {m n a : ℕ} (cmn : coprime m n) (dvd : a ∣ m) : coprime (m / a) n :=
  by 
    byCases' a_split : a = 0
    ·
      subst a_split 
      rw [zero_dvd_iff] at dvd 
      simpa [dvd] using cmn
    ·
      rcases dvd with ⟨k, rfl⟩
      rw [Nat.mul_div_cancel_leftₓ _ (Nat.pos_of_ne_zeroₓ a_split)]
      exact coprime.coprime_mul_left cmn

theorem coprime.coprime_div_right {m n a : ℕ} (cmn : coprime m n) (dvd : a ∣ n) : coprime m (n / a) :=
  (coprime.coprime_div_left cmn.symm dvd).symm

theorem coprime_mul_iff_left {k m n : ℕ} : coprime (m*n) k ↔ coprime m k ∧ coprime n k :=
  ⟨fun h => ⟨coprime.coprime_mul_right h, coprime.coprime_mul_left h⟩,
    fun ⟨h, _⟩ =>
      by 
        rwa [coprime_iff_gcd_eq_one, coprime.gcd_mul_left_cancel n h]⟩

theorem coprime_mul_iff_right {k m n : ℕ} : coprime k (m*n) ↔ coprime k m ∧ coprime k n :=
  by 
    simpa only [coprime_comm] using coprime_mul_iff_left

theorem coprime.gcd_left (k : ℕ) {m n : ℕ} (hmn : coprime m n) : coprime (gcd k m) n :=
  hmn.coprime_dvd_left$ gcd_dvd_right k m

theorem coprime.gcd_right (k : ℕ) {m n : ℕ} (hmn : coprime m n) : coprime m (gcd k n) :=
  hmn.coprime_dvd_right$ gcd_dvd_right k n

theorem coprime.gcd_both (k l : ℕ) {m n : ℕ} (hmn : coprime m n) : coprime (gcd k m) (gcd l n) :=
  (hmn.gcd_left k).gcd_right l

theorem coprime.mul_dvd_of_dvd_of_dvd {a n m : ℕ} (hmn : coprime m n) (hm : m ∣ a) (hn : n ∣ a) : (m*n) ∣ a :=
  let ⟨k, hk⟩ := hm 
  hk.symm ▸ mul_dvd_mul_left _ (hmn.symm.dvd_of_dvd_mul_left (hk ▸ hn))

theorem coprime_one_left : ∀ n, coprime 1 n :=
  gcd_one_left

theorem coprime_one_right : ∀ n, coprime n 1 :=
  gcd_one_right

theorem coprime.pow_left {m k : ℕ} (n : ℕ) (H1 : coprime m k) : coprime (m ^ n) k :=
  Nat.recOn n (coprime_one_left _) fun n IH => H1.mul IH

theorem coprime.pow_right {m k : ℕ} (n : ℕ) (H1 : coprime k m) : coprime k (m ^ n) :=
  (H1.symm.pow_left n).symm

theorem coprime.pow {k l : ℕ} (m n : ℕ) (H1 : coprime k l) : coprime (k ^ m) (l ^ n) :=
  (H1.pow_left _).pow_right _

theorem coprime_pow_left_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) : Nat.Coprime (a ^ n) b ↔ Nat.Coprime a b :=
  by 
    obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero hn.ne' 
    rw [pow_succₓ, Nat.coprime_mul_iff_leftₓ]
    exact ⟨And.left, fun hab => ⟨hab, hab.pow_left _⟩⟩

theorem coprime_pow_right_iff {n : ℕ} (hn : 0 < n) (a b : ℕ) : Nat.Coprime a (b ^ n) ↔ Nat.Coprime a b :=
  by 
    rw [Nat.coprime_commₓ, coprime_pow_left_iff hn, Nat.coprime_commₓ]

theorem coprime.eq_one_of_dvd {k m : ℕ} (H : coprime k m) (d : k ∣ m) : k = 1 :=
  by 
    rw [←H.gcd_eq_one, gcd_eq_left d]

@[simp]
theorem coprime_zero_left (n : ℕ) : coprime 0 n ↔ n = 1 :=
  by 
    simp [coprime]

@[simp]
theorem coprime_zero_right (n : ℕ) : coprime n 0 ↔ n = 1 :=
  by 
    simp [coprime]

theorem not_coprime_zero_zero : ¬coprime 0 0 :=
  by 
    simp 

@[simp]
theorem coprime_one_left_iff (n : ℕ) : coprime 1 n ↔ True :=
  by 
    simp [coprime]

@[simp]
theorem coprime_one_right_iff (n : ℕ) : coprime n 1 ↔ True :=
  by 
    simp [coprime]

@[simp]
theorem coprime_self (n : ℕ) : coprime n n ↔ n = 1 :=
  by 
    simp [coprime]

theorem coprime.eq_of_mul_eq_zero {m n : ℕ} (h : m.coprime n) (hmn : (m*n) = 0) : m = 0 ∧ n = 1 ∨ m = 1 ∧ n = 0 :=
  (Nat.eq_zero_of_mul_eq_zero hmn).imp (fun hm => ⟨hm, n.coprime_zero_left.mp$ hm ▸ h⟩)
    fun hn => ⟨m.coprime_zero_left.mp$ hn ▸ h.symm, hn⟩

-- error in Data.Nat.Gcd: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`. -/
def prod_dvd_and_dvd_of_dvd_prod
{m n k : exprℕ()}
(H : «expr ∣ »(k, «expr * »(m, n))) : {d : «expr × »({m' // «expr ∣ »(m', m)}, {n' // «expr ∣ »(n', n)}) // «expr = »(k, «expr * »(d.1, d.2))} :=
begin
  cases [expr h0, ":", expr gcd k m] [],
  case [ident nat.zero] { have [] [":", expr «expr = »(k, 0)] [":=", expr eq_zero_of_gcd_eq_zero_left h0],
    subst [expr this],
    have [] [":", expr «expr = »(m, 0)] [":=", expr eq_zero_of_gcd_eq_zero_right h0],
    subst [expr this],
    exact [expr ⟨⟨⟨0, dvd_refl 0⟩, ⟨n, dvd_refl n⟩⟩, (zero_mul n).symm⟩] },
  case [ident nat.succ, ":", ident tmp] { have [ident hpos] [":", expr «expr < »(0, gcd k m)] [":=", expr «expr ▸ »(h0.symm, nat.zero_lt_succ _)]; clear [ident h0, ident tmp],
    have [ident hd] [":", expr «expr = »(«expr * »(gcd k m, «expr / »(k, gcd k m)), k)] [":=", expr nat.mul_div_cancel' (gcd_dvd_left k m)],
    refine [expr ⟨⟨⟨gcd k m, gcd_dvd_right k m⟩, ⟨«expr / »(k, gcd k m), _⟩⟩, hd.symm⟩],
    apply [expr dvd_of_mul_dvd_mul_left hpos],
    rw ["[", expr hd, ",", "<-", expr gcd_mul_right, "]"] [],
    exact [expr dvd_gcd (dvd_mul_right _ _) H] }
end

-- error in Data.Nat.Gcd: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem gcd_mul_dvd_mul_gcd (k m n : exprℕ()) : «expr ∣ »(gcd k «expr * »(m, n), «expr * »(gcd k m, gcd k n)) :=
begin
  rcases [expr «expr $ »(prod_dvd_and_dvd_of_dvd_prod, gcd_dvd_right k «expr * »(m, n)), "with", "⟨", "⟨", "⟨", ident m', ",", ident hm', "⟩", ",", "⟨", ident n', ",", ident hn', "⟩", "⟩", ",", ident h, "⟩"],
  replace [ident h] [":", expr «expr = »(gcd k «expr * »(m, n), «expr * »(m', n'))] [":=", expr h],
  rw [expr h] [],
  have [ident hm'n'] [":", expr «expr ∣ »(«expr * »(m', n'), k)] [":=", expr «expr ▸ »(h, gcd_dvd_left _ _)],
  apply [expr mul_dvd_mul],
  { have [ident hm'k] [":", expr «expr ∣ »(m', k)] [":=", expr (dvd_mul_right m' n').trans hm'n'],
    exact [expr dvd_gcd hm'k hm'] },
  { have [ident hn'k] [":", expr «expr ∣ »(n', k)] [":=", expr (dvd_mul_left n' m').trans hm'n'],
    exact [expr dvd_gcd hn'k hn'] }
end

theorem coprime.gcd_mul (k : ℕ) {m n : ℕ} (h : coprime m n) : gcd k (m*n) = gcd k m*gcd k n :=
  dvd_antisymm (gcd_mul_dvd_mul_gcd k m n)
    ((h.gcd_both k k).mul_dvd_of_dvd_of_dvd (gcd_dvd_gcd_mul_right_right _ _ _) (gcd_dvd_gcd_mul_left_right _ _ _))

-- error in Data.Nat.Gcd: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem pow_dvd_pow_iff
{a b n : exprℕ()}
(n0 : «expr < »(0, n)) : «expr ↔ »(«expr ∣ »(«expr ^ »(a, n), «expr ^ »(b, n)), «expr ∣ »(a, b)) :=
begin
  refine [expr ⟨λ h, _, λ h, pow_dvd_pow_of_dvd h _⟩],
  cases [expr nat.eq_zero_or_pos (gcd a b)] ["with", ident g0, ident g0],
  { simp [] [] [] ["[", expr eq_zero_of_gcd_eq_zero_right g0, "]"] [] [] },
  rcases [expr exists_coprime' g0, "with", "⟨", ident g, ",", ident a', ",", ident b', ",", ident g0', ",", ident co, ",", ident rfl, ",", ident rfl, "⟩"],
  rw ["[", expr mul_pow, ",", expr mul_pow, "]"] ["at", ident h],
  replace [ident h] [] [":=", expr dvd_of_mul_dvd_mul_right (pow_pos g0' _) h],
  have [] [] [":=", expr pow_dvd_pow a' n0],
  rw ["[", expr pow_one, ",", expr (co.pow n n).eq_one_of_dvd h, "]"] ["at", ident this],
  simp [] [] [] ["[", expr eq_one_of_dvd_one this, "]"] [] []
end

theorem gcd_mul_gcd_of_coprime_of_mul_eq_mul {a b c d : ℕ} (cop : c.coprime d) (h : (a*b) = c*d) :
  (a.gcd c*b.gcd c) = c :=
  by 
    apply dvd_antisymm
    ·
      apply Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.mul (cop.gcd_left _) (cop.gcd_left _))
      rw [←h]
      apply mul_dvd_mul (gcd_dvd _ _).1 (gcd_dvd _ _).1
    ·
      rw [gcd_comm a _, gcd_comm b _]
      trans c.gcd (a*b)
      rw [h, gcd_mul_right_right d c]
      apply gcd_mul_dvd_mul_gcd

-- error in Data.Nat.Gcd: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `k:ℕ` divides coprime `a` and `b` then `k = 1` -/
theorem eq_one_of_dvd_coprimes
{a b k : exprℕ()}
(h_ab_coprime : coprime a b)
(hka : «expr ∣ »(k, a))
(hkb : «expr ∣ »(k, b)) : «expr = »(k, 1) :=
begin
  rw [expr coprime_iff_gcd_eq_one] ["at", ident h_ab_coprime],
  have [ident h1] [] [":=", expr dvd_gcd hka hkb],
  rw [expr h_ab_coprime] ["at", ident h1],
  exact [expr nat.dvd_one.mp h1]
end

end Nat

