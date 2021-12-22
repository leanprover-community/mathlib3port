import Mathbin.Data.Int.Gcd
import Mathbin.Data.List.Rotate
import Mathbin.Tactic.Abel

/-!
# Congruences modulo a natural number

This file defines the equivalence relation `a ≡ b [MOD n]` on the natural numbers,
and proves basic properties about it such as the Chinese Remainder Theorem
`modeq_and_modeq_iff_modeq_mul`.

## Notations

`a ≡ b [MOD n]` is notation for `nat.modeq n a b`, which is defined to mean `a % n = b % n`.

## Tags

modeq, congruence, mod, MOD, modulo
-/


namespace Nat

-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler decidable
/--  Modular equality. `n.modeq a b`, or `a ≡ b [MOD n]`, means that `a - b` is a multiple of `n`. -/
def modeq (n a b : ℕ) :=
  a % n = b % n deriving [anonymous]

notation:50 a " ≡ " b " [MOD " n "]" => modeq n a b

variable {m n a b c d : ℕ}

namespace Modeq

@[refl]
protected theorem refl (a : ℕ) : a ≡ a [MOD n] :=
  @rfl _ _

protected theorem rfl : a ≡ a [MOD n] :=
  modeq.refl _

@[symm]
protected theorem symm : a ≡ b [MOD n] → b ≡ a [MOD n] :=
  Eq.symm

@[trans]
protected theorem trans : a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n] :=
  Eq.trans

protected theorem comm : a ≡ b [MOD n] ↔ b ≡ a [MOD n] :=
  ⟨modeq.symm, modeq.symm⟩

end Modeq

theorem modeq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a := by
  rw [modeq, zero_mod, dvd_iff_mod_eq_zero]

theorem _root_.has_dvd.dvd.modeq_zero_nat (h : n ∣ a) : a ≡ 0 [MOD n] :=
  modeq_zero_iff_dvd.2 h

theorem _root_.has_dvd.dvd.zero_modeq_nat (h : n ∣ a) : 0 ≡ a [MOD n] :=
  h.modeq_zero_nat.symm

theorem modeq_iff_dvd : a ≡ b [MOD n] ↔ (n : ℤ) ∣ b - a := by
  rw [modeq, eq_comm, ← Int.coe_nat_inj', Int.coe_nat_mod, Int.coe_nat_mod, Int.mod_eq_mod_iff_mod_sub_eq_zero,
    Int.dvd_iff_mod_eq_zero]

protected theorem modeq.dvd : a ≡ b [MOD n] → (n : ℤ) ∣ b - a :=
  modeq_iff_dvd.1

theorem modeq_of_dvd : (n : ℤ) ∣ b - a → a ≡ b [MOD n] :=
  modeq_iff_dvd.2

/--  A variant of `modeq_iff_dvd` with `nat` divisibility -/
theorem modeq_iff_dvd' (h : a ≤ b) : a ≡ b [MOD n] ↔ n ∣ b - a := by
  rw [modeq_iff_dvd, ← Int.coe_nat_dvd, Int.coe_nat_subₓ h]

theorem mod_modeq a n : a % n ≡ a [MOD n] :=
  mod_mod _ _

namespace Modeq

protected theorem modeq_of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m] :=
  modeq_of_dvd ((Int.coe_nat_dvd.2 d).trans h.dvd)

protected theorem mul_left' (c : ℕ) (h : a ≡ b [MOD n]) : (c*a) ≡ c*b [MOD c*n] := by
  unfold modeq  at * <;> rw [mul_mod_mul_left, mul_mod_mul_left, h]

protected theorem mul_left (c : ℕ) (h : a ≡ b [MOD n]) : (c*a) ≡ c*b [MOD n] :=
  (h.mul_left' _).modeq_of_dvd (dvd_mul_left _ _)

protected theorem mul_right' (c : ℕ) (h : a ≡ b [MOD n]) : (a*c) ≡ b*c [MOD n*c] := by
  rw [mul_commₓ a, mul_commₓ b, mul_commₓ n] <;> exact h.mul_left' c

protected theorem mul_right (c : ℕ) (h : a ≡ b [MOD n]) : (a*c) ≡ b*c [MOD n] := by
  rw [mul_commₓ a, mul_commₓ b] <;> exact h.mul_left c

protected theorem mul (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : (a*c) ≡ b*d [MOD n] :=
  (h₂.mul_left _).trans (h₁.mul_right _)

protected theorem pow (m : ℕ) (h : a ≡ b [MOD n]) : a ^ m ≡ b ^ m [MOD n] := by
  induction' m with d hd
  ·
    rfl
  rw [pow_succₓ, pow_succₓ]
  exact h.mul hd

protected theorem add (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : (a+c) ≡ b+d [MOD n] := by
  rw [modeq_iff_dvd, Int.coe_nat_add, Int.coe_nat_add, add_sub_comm]
  exact dvd_add h₁.dvd h₂.dvd

protected theorem add_left (c : ℕ) (h : a ≡ b [MOD n]) : (c+a) ≡ c+b [MOD n] :=
  modeq.rfl.add h

protected theorem add_right (c : ℕ) (h : a ≡ b [MOD n]) : (a+c) ≡ b+c [MOD n] :=
  h.add modeq.rfl

protected theorem add_left_cancelₓ (h₁ : a ≡ b [MOD n]) (h₂ : (a+c) ≡ b+d [MOD n]) : c ≡ d [MOD n] := by
  simp only [modeq_iff_dvd, Int.coe_nat_add] at *
  rw [add_sub_comm] at h₂
  convert _root_.dvd_sub h₂ h₁ using 1
  rw [add_sub_cancel']

protected theorem add_left_cancel' (c : ℕ) (h : (c+a) ≡ c+b [MOD n]) : a ≡ b [MOD n] :=
  modeq.rfl.add_left_cancel h

protected theorem add_right_cancelₓ (h₁ : c ≡ d [MOD n]) (h₂ : (a+c) ≡ b+d [MOD n]) : a ≡ b [MOD n] := by
  rw [add_commₓ a, add_commₓ b] at h₂
  exact h₁.add_left_cancel h₂

protected theorem add_right_cancel' (c : ℕ) (h : (a+c) ≡ b+c [MOD n]) : a ≡ b [MOD n] :=
  modeq.rfl.add_right_cancel h

theorem of_modeq_mul_left (m : ℕ) (h : a ≡ b [MOD m*n]) : a ≡ b [MOD n] := by
  rw [modeq_iff_dvd] at *
  exact (dvd_mul_left (n : ℤ) (m : ℤ)).trans h

theorem of_modeq_mul_right (m : ℕ) : a ≡ b [MOD n*m] → a ≡ b [MOD n] :=
  mul_commₓ m n ▸ of_modeq_mul_left _

end Modeq

theorem modeq_one : a ≡ b [MOD 1] :=
  modeq_of_dvd (one_dvd _)

theorem modeq_sub (h : b ≤ a) : a ≡ b [MOD a - b] :=
  (modeq_of_dvd $ by
      rw [Int.coe_nat_subₓ h]).symm

@[simp]
theorem modeq_zero_iff {a b : ℕ} : a ≡ b [MOD 0] ↔ a = b := by
  rw [Nat.Modeq, Nat.mod_zeroₓ, Nat.mod_zeroₓ]

@[simp]
theorem add_modeq_left {a n : ℕ} : (n+a) ≡ a [MOD n] := by
  rw [Nat.Modeq, Nat.add_mod_leftₓ]

@[simp]
theorem add_modeq_right {a n : ℕ} : (a+n) ≡ a [MOD n] := by
  rw [Nat.Modeq, Nat.add_mod_rightₓ]

namespace Modeq

theorem le_of_lt_add (h1 : a ≡ b [MOD m]) (h2 : a < b+m) : a ≤ b :=
  (le_totalₓ a b).elim id fun h3 =>
    Nat.le_of_sub_eq_zeroₓ (eq_zero_of_dvd_of_lt ((modeq_iff_dvd' h3).mp h1.symm) ((tsub_lt_iff_left h3).mpr h2))

theorem add_le_of_lt (h1 : a ≡ b [MOD m]) (h2 : a < b) : (a+m) ≤ b :=
  le_of_lt_add (add_modeq_right.trans h1) (add_lt_add_right h2 m)

end Modeq

attribute [local semireducible] Int.Nonneg

/--  The natural number less than `lcm n m` congruent to `a` mod `n` and `b` mod `m` -/
def chinese_remainder' (h : a ≡ b [MOD gcd n m]) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] } :=
  if hn : n = 0 then
    ⟨a, by
      rw [hn, gcd_zero_left] at h
      constructor
      rfl
      exact h⟩
  else
    if hm : m = 0 then
      ⟨b, by
        rw [hm, gcd_zero_right] at h
        constructor
        exact h.symm
        rfl⟩
    else
      ⟨let (c, d) := xgcd n m
        Int.toNat ((((n*c)*b)+(m*d)*a) / gcd n m % lcm n m),
        by
        rw [xgcd_val]
        dsimp [chinese_remainder'._match_1]
        rw [modeq_iff_dvd, modeq_iff_dvd,
          Int.to_nat_of_nonneg (Int.mod_nonneg _ (Int.coe_nat_ne_zero.2 (lcm_ne_zero hn hm)))]
        have hnonzero : (gcd n m : ℤ) ≠ 0 := by
          norm_cast
          rw [Nat.gcd_eq_zero_iffₓ, not_and]
          exact fun _ => hm
        have hcoedvd : ∀ t, (gcd n m : ℤ) ∣ t*b - a := fun t => h.dvd.mul_left _
        have := gcd_eq_gcd_ab n m
        constructor <;>
          rw [Int.mod_def, ← sub_add] <;>
            refine' dvd_add _ (dvd_mul_of_dvd_left _ _) <;>
              try
                norm_cast
        ·
          rw [← sub_eq_iff_eq_add'] at this
          rw [← this, sub_mul, ← add_sub_assoc, add_commₓ, add_sub_assoc, ← mul_sub, Int.add_div_of_dvd_left,
            Int.mul_div_cancel_left _ hnonzero, Int.mul_div_assoc _ h.dvd, ← sub_sub, sub_self, zero_sub, dvd_neg,
            mul_assocₓ]
          exact dvd_mul_right _ _
          norm_cast
          exact dvd_mul_right _ _
        ·
          exact dvd_lcm_left n m
        ·
          rw [← sub_eq_iff_eq_add] at this
          rw [← this, sub_mul, sub_add, ← mul_sub, Int.sub_div_of_dvd, Int.mul_div_cancel_left _ hnonzero,
            Int.mul_div_assoc _ h.dvd, ← sub_add, sub_self, zero_addₓ, mul_assocₓ]
          exact dvd_mul_right _ _
          exact hcoedvd _
        ·
          exact dvd_lcm_right n m⟩

/--  The natural number less than `n*m` congruent to `a` mod `n` and `b` mod `m` -/
def chinese_remainder (co : coprime n m) (a b : ℕ) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] } :=
  chinese_remainder'
    (by
      convert modeq_one)

theorem chinese_remainder'_lt_lcm (h : a ≡ b [MOD gcd n m]) (hn : n ≠ 0) (hm : m ≠ 0) :
    ↑chinese_remainder' h < lcm n m := by
  dsimp only [chinese_remainder']
  rw [dif_neg hn, dif_neg hm, Subtype.coe_mk, xgcd_val, ← Int.to_nat_coe_nat (lcm n m)]
  have lcm_pos := int.coe_nat_pos.mpr (Nat.pos_of_ne_zeroₓ (lcm_ne_zero hn hm))
  exact (Int.to_nat_lt_to_nat lcm_pos).mpr (Int.mod_lt_of_pos _ lcm_pos)

theorem chinese_remainder_lt_mul (co : coprime n m) (a b : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    ↑chinese_remainder co a b < n*m :=
  lt_of_lt_of_leₓ (chinese_remainder'_lt_lcm _ hn hm) (le_of_eqₓ co.lcm_eq_mul)

theorem modeq_and_modeq_iff_modeq_mul {a b m n : ℕ} (hmn : coprime m n) :
    a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD m*n] :=
  ⟨fun h => by
    rw [Nat.modeq_iff_dvd, Nat.modeq_iff_dvd, ← Int.dvd_nat_abs, Int.coe_nat_dvd, ← Int.dvd_nat_abs, Int.coe_nat_dvd] at
      h
    rw [Nat.modeq_iff_dvd, ← Int.dvd_nat_abs, Int.coe_nat_dvd]
    exact hmn.mul_dvd_of_dvd_of_dvd h.1 h.2, fun h => ⟨h.of_modeq_mul_right _, h.of_modeq_mul_left _⟩⟩

theorem coprime_of_mul_modeq_one (b : ℕ) {a n : ℕ} (h : (a*b) ≡ 1 [MOD n]) : coprime a n :=
  Nat.coprime_of_dvd' fun k kp ⟨ka, hka⟩ ⟨kb, hkb⟩ =>
    Int.coe_nat_dvd.1
      (by
        rw [hka, hkb, modeq_iff_dvd] at h
        cases' h with z hz
        rw [sub_eq_iff_eq_add] at hz
        rw [hz, Int.coe_nat_mul, mul_assocₓ, mul_assocₓ, Int.coe_nat_mul, ← mul_addₓ]
        exact dvd_mul_right _ _)

@[simp]
theorem mod_mul_right_mod (a b c : ℕ) : (a % b*c) % b = a % b :=
  (mod_modeq _ _).of_modeq_mul_right _

@[simp]
theorem mod_mul_left_mod (a b c : ℕ) : (a % b*c) % c = a % c :=
  (mod_modeq _ _).of_modeq_mul_left _

theorem div_mod_eq_mod_mul_div (a b c : ℕ) : a / b % c = (a % b*c) / b :=
  if hb0 : b = 0 then by
    simp [hb0]
  else by
    rw [← @add_right_cancel_iffₓ _ _ (c*a / b / c), mod_add_div, Nat.div_div_eq_div_mulₓ, ←
      Nat.mul_right_inj (Nat.pos_of_ne_zeroₓ hb0), ← @add_left_cancel_iffₓ _ _ (a % b), mod_add_div, mul_addₓ, ←
      @add_left_cancel_iffₓ _ _ ((a % b*c) % b), add_left_commₓ, ← add_assocₓ ((a % b*c) % b), mod_add_div, ←
      mul_assocₓ, mod_add_div, mod_mul_right_mod]

theorem add_mod_add_ite (a b c : ℕ) : (((a+b) % c)+if c ≤ (a % c)+b % c then c else 0) = (a % c)+b % c :=
  have : (a+b) % c = ((a % c)+b % c) % c := ((mod_modeq _ _).add $ mod_modeq _ _).symm
  if hc0 : c = 0 then by
    simp [hc0]
  else by
    rw [this]
    split_ifs
    ·
      have h2 : ((a % c)+b % c) / c < 2
      exact
        Nat.div_lt_of_lt_mul
          (by
            rw [mul_two] <;>
              exact add_lt_add (Nat.mod_ltₓ _ (Nat.pos_of_ne_zeroₓ hc0)) (Nat.mod_ltₓ _ (Nat.pos_of_ne_zeroₓ hc0)))
      have h0 : 0 < ((a % c)+b % c) / c
      exact Nat.div_pos h (Nat.pos_of_ne_zeroₓ hc0)
      rw [← @add_right_cancel_iffₓ _ _ (c*((a % c)+b % c) / c), add_commₓ _ c, add_assocₓ, mod_add_div,
        le_antisymmₓ (le_of_lt_succ h2) h0, mul_oneₓ, add_commₓ]
    ·
      rw [Nat.mod_eq_of_ltₓ (lt_of_not_geₓ h), add_zeroₓ]

theorem add_mod_of_add_mod_lt {a b c : ℕ} (hc : ((a % c)+b % c) < c) : (a+b) % c = (a % c)+b % c := by
  rw [← add_mod_add_ite, if_neg (not_le_of_lt hc), add_zeroₓ]

theorem add_mod_add_of_le_add_mod {a b c : ℕ} (hc : c ≤ (a % c)+b % c) : (((a+b) % c)+c) = (a % c)+b % c := by
  rw [← add_mod_add_ite, if_pos hc]

theorem add_div {a b c : ℕ} (hc0 : 0 < c) : (a+b) / c = ((a / c)+b / c)+if c ≤ (a % c)+b % c then 1 else 0 := by
  rw [← Nat.mul_right_inj hc0, ← @add_left_cancel_iffₓ _ _ ((((a+b) % c)+a % c)+b % c)]
  suffices
    (((((a+b) % c)+c*(a+b) / c)+a % c)+b % c) =
      ((((a % c)+c*a / c)+(b % c)+c*b / c)+c*if c ≤ (a % c)+b % c then 1 else 0)+(a+b) % c by
    simpa only [mul_addₓ, add_commₓ, add_left_commₓ, add_assocₓ]
  rw [mod_add_div, mod_add_div, mod_add_div, mul_ite, add_assocₓ, add_assocₓ]
  conv_lhs => rw [← add_mod_add_ite]
  simp
  ac_rfl

theorem add_div_eq_of_add_mod_lt {a b c : ℕ} (hc : ((a % c)+b % c) < c) : (a+b) / c = (a / c)+b / c :=
  if hc0 : c = 0 then by
    simp [hc0]
  else by
    rw [add_div (Nat.pos_of_ne_zeroₓ hc0), if_neg (not_le_of_lt hc), add_zeroₓ]

protected theorem add_div_of_dvd_right {a b c : ℕ} (hca : c ∣ a) : (a+b) / c = (a / c)+b / c :=
  if h : c = 0 then by
    simp [h]
  else
    add_div_eq_of_add_mod_lt
      (by
        rw [Nat.mod_eq_zero_of_dvdₓ hca, zero_addₓ]
        exact Nat.mod_ltₓ _ (pos_iff_ne_zero.mpr h))

protected theorem add_div_of_dvd_left {a b c : ℕ} (hca : c ∣ b) : (a+b) / c = (a / c)+b / c := by
  rwa [add_commₓ, Nat.add_div_of_dvd_right, add_commₓ]

theorem add_div_eq_of_le_mod_add_mod {a b c : ℕ} (hc : c ≤ (a % c)+b % c) (hc0 : 0 < c) :
    (a+b) / c = ((a / c)+b / c)+1 := by
  rw [add_div hc0, if_pos hc]

theorem add_div_le_add_div (a b c : ℕ) : ((a / c)+b / c) ≤ (a+b) / c :=
  if hc0 : c = 0 then by
    simp [hc0]
  else by
    rw [Nat.add_div (Nat.pos_of_ne_zeroₓ hc0)] <;> exact Nat.le_add_rightₓ _ _

theorem le_mod_add_mod_of_dvd_add_of_not_dvd {a b c : ℕ} (h : c ∣ a+b) (ha : ¬c ∣ a) : c ≤ (a % c)+b % c :=
  by_contradiction $ fun hc =>
    have : (a+b) % c = (a % c)+b % c := add_mod_of_add_mod_lt (lt_of_not_geₓ hc)
    by
    simp_all [dvd_iff_mod_eq_zero]

theorem odd_mul_odd {n m : ℕ} : n % 2 = 1 → m % 2 = 1 → (n*m) % 2 = 1 := by
  simpa [Nat.Modeq] using @modeq.mul 2 n 1 m 1

theorem odd_mul_odd_div_two {m n : ℕ} (hm1 : m % 2 = 1) (hn1 : n % 2 = 1) : (m*n) / 2 = (m*n / 2)+m / 2 :=
  have hm0 : 0 < m :=
    Nat.pos_of_ne_zeroₓ fun h => by
      simp_all
  have hn0 : 0 < n :=
    Nat.pos_of_ne_zeroₓ fun h => by
      simp_all
  (Nat.mul_right_inj
        (show 0 < 2 from by
          decide)).1 $
    by
    rw [mul_addₓ, two_mul_odd_div_two hm1, mul_left_commₓ, two_mul_odd_div_two hn1,
      two_mul_odd_div_two (Nat.odd_mul_odd hm1 hn1), mul_tsub, mul_oneₓ, ← add_tsub_assoc_of_le (succ_le_of_lt hm0),
      tsub_add_cancel_of_le (le_mul_of_one_le_right (Nat.zero_leₓ _) hn0)]

theorem odd_of_mod_four_eq_one {n : ℕ} : n % 4 = 1 → n % 2 = 1 := by
  simpa [modeq,
    show (2*2) = 4by
      norm_num] using
    @modeq.of_modeq_mul_left 2 n 1 2

theorem odd_of_mod_four_eq_three {n : ℕ} : n % 4 = 3 → n % 2 = 1 := by
  simpa [modeq,
    show (2*2) = 4by
      norm_num,
    show 3 % 4 = 3by
      norm_num] using
    @modeq.of_modeq_mul_left 2 n 3 2

end Nat

namespace List

variable {α : Type _}

theorem nth_rotate : ∀ {l : List α} {n m : ℕ} hml : m < l.length, (l.rotate n).nth m = l.nth ((m+n) % l.length)
  | [], n, m, hml => (Nat.not_lt_zeroₓ _ hml).elim
  | l, 0, m, hml => by
    simp [Nat.mod_eq_of_ltₓ hml]
  | a :: l, n+1, m, hml =>
    have h₃ : m < List.length (l ++ [a]) := by
      simpa using hml
    (lt_or_eq_of_leₓ (Nat.le_of_lt_succₓ $ Nat.mod_ltₓ (m+n) (lt_of_le_of_ltₓ (Nat.zero_leₓ _) hml))).elim
      (fun hml' =>
        have h₁ : (m+n+1) % (a :: l : List α).length = ((m+n) % (a :: l : List α).length)+1 :=
          calc ((m+n+1) % l.length+1) = (((m+n) % l.length+1)+1) % l.length+1 :=
            add_assocₓ m n 1 ▸ Nat.Modeq.add_right 1 (Nat.mod_modₓ _ _).symm
            _ = ((m+n) % l.length+1)+1 := Nat.mod_eq_of_ltₓ (Nat.succ_lt_succₓ hml')
            
        have h₂ : (m+n) % (l ++ [a]).length < l.length := by
          simpa [Nat.add_one] using hml'
        by
        rw [List.rotate_cons_succ, nth_rotate h₃, List.nth_append h₂, h₁, List.nth] <;> simp )
      fun hml' =>
      have h₁ : ((m+n+1) % l.length+1) = 0 :=
        calc ((m+n+1) % l.length+1) = (l.length+1) % l.length+1 :=
          add_assocₓ m n 1 ▸ Nat.Modeq.add_right 1 (hml'.trans (Nat.mod_eq_of_ltₓ (Nat.lt_succ_selfₓ _)).symm)
          _ = 0 := by
          simp
          
      by
      rw [List.length, List.rotate_cons_succ, nth_rotate h₃, List.length_append, List.length_cons, List.length,
          zero_addₓ, hml', h₁, List.nth_concat_length] <;>
        rfl

theorem rotate_eq_self_iff_eq_repeat [hα : Nonempty α] :
    ∀ {l : List α}, (∀ n, l.rotate n = l) ↔ ∃ a, l = List.repeat a l.length
  | [] =>
    ⟨fun h =>
      Nonempty.elimₓ hα fun a =>
        ⟨a, by
          simp ⟩,
      by
      simp ⟩
  | a :: l =>
    ⟨fun h =>
      ⟨a,
        List.ext_le
            (by
              simp ) $
          fun n hn h₁ => by
          rw [← Option.some_inj, ← List.nth_le_nth]
          conv => lhs rw [← h (List.length (a :: l) - n)]
          rw [nth_rotate hn, add_tsub_cancel_of_le (le_of_ltₓ hn), Nat.mod_selfₓ, nth_le_repeat]
          rfl⟩,
      fun ⟨a, ha⟩ n =>
      ha.symm ▸
        List.ext_le
          (by
            simp )
          fun m hm h =>
          have hm' : (m+n) % (List.repeat a (List.length (a :: l))).length < List.length (a :: l) := by
            rw [List.length_repeat] <;> exact Nat.mod_ltₓ _ (Nat.succ_posₓ _)
          by
          rw [nth_le_repeat, ← Option.some_inj, ← List.nth_le_nth, nth_rotate h, List.nth_le_nth, nth_le_repeat] <;>
            simp_all ⟩

theorem rotate_repeat (a : α) (n : ℕ) (k : ℕ) : (List.repeat a n).rotate k = List.repeat a n :=
  let h : Nonempty α := ⟨a⟩
  by
  exact
    rotate_eq_self_iff_eq_repeat.mpr
      ⟨a, by
        rw [length_repeat]⟩
      k

theorem rotate_one_eq_self_iff_eq_repeat [Nonempty α] {l : List α} :
    l.rotate 1 = l ↔ ∃ a : α, l = List.repeat a l.length :=
  ⟨fun h =>
    rotate_eq_self_iff_eq_repeat.mp fun n =>
      Nat.rec l.rotate_zero
        (fun n hn => by
          rwa [Nat.succ_eq_add_one, ← l.rotate_rotate, hn])
        n,
    fun h => rotate_eq_self_iff_eq_repeat.mpr h 1⟩

end List

