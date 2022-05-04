/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
import Mathbin.Algebra.Hom.Iterate
import Mathbin.Data.Int.Modeq
import Mathbin.Data.Nat.Choose.Dvd
import Mathbin.Data.Nat.Choose.Sum
import Mathbin.GroupTheory.OrderOfElement
import Mathbin.RingTheory.Nilpotent

/-!
# Characteristic of semirings
-/


universe u v

variable (R : Type u)

-- ././Mathport/Syntax/Translate/Basic.lean:1250:30: infer kinds are unsupported in Lean 4: #[`cast_eq_zero_iff] []
/-- The generator of the kernel of the unique homomorphism ℕ → R for a semiring R.

*Warning*: for a semiring `R`, `char_p R 0` and `char_zero R` need not coincide.
* `char_p R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`;
* `char_zero R` requires an injection `ℕ ↪ R`.

For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
`char_zero {0, 1}` does not hold and yet `char_p {0, 1} 0` does.
This example is formalized in `counterexamples/char_p_zero_ne_char_zero`.
 -/
class CharP [AddMonoidₓ R] [One R] (p : ℕ) : Prop where
  cast_eq_zero_iff : ∀ x : ℕ, (x : R) = 0 ↔ p ∣ x

theorem CharP.cast_eq_zero [AddMonoidₓ R] [One R] (p : ℕ) [CharP R p] : (p : R) = 0 :=
  (CharP.cast_eq_zero_iff R p p).2 (dvd_refl p)

@[simp]
theorem CharP.cast_card_eq_zero [AddGroupₓ R] [One R] [Fintype R] : (Fintype.card R : R) = 0 := by
  rw [← nsmul_one, card_nsmul_eq_zero]

theorem CharP.int_cast_eq_zero_iff [AddGroupₓ R] [One R] (p : ℕ) [CharP R p] (a : ℤ) : (a : R) = 0 ↔ (p : ℤ) ∣ a := by
  rcases lt_trichotomyₓ a 0 with (h | rfl | h)
  · rw [← neg_eq_zero, ← Int.cast_neg, ← dvd_neg]
    lift -a to ℕ using neg_nonneg.mpr (le_of_ltₓ h) with b
    rw [Int.cast_coe_nat, CharP.cast_eq_zero_iff R p, Int.coe_nat_dvd]
    
  · simp only [Int.cast_zeroₓ, eq_self_iff_true, dvd_zero]
    
  · lift a to ℕ using le_of_ltₓ h with b
    rw [Int.cast_coe_nat, CharP.cast_eq_zero_iff R p, Int.coe_nat_dvd]
    

theorem CharP.int_coe_eq_int_coe_iff [AddGroupₓ R] [One R] (p : ℕ) [CharP R p] (a b : ℤ) :
    (a : R) = (b : R) ↔ a ≡ b [ZMOD p] := by
  rw [eq_comm, ← sub_eq_zero, ← Int.cast_sub, CharP.int_cast_eq_zero_iff R p, Int.modeq_iff_dvd]

theorem CharP.eq [AddMonoidₓ R] [One R] {p q : ℕ} (c1 : CharP R p) (c2 : CharP R q) : p = q :=
  Nat.dvd_antisymm ((CharP.cast_eq_zero_iff R p q).1 (CharP.cast_eq_zero _ _))
    ((CharP.cast_eq_zero_iff R q p).1 (CharP.cast_eq_zero _ _))

instance CharP.of_char_zero [AddMonoidₓ R] [One R] [CharZero R] : CharP R 0 :=
  ⟨fun x => by
    rw [zero_dvd_iff, ← Nat.cast_zeroₓ, Nat.cast_inj]⟩

theorem CharP.exists [NonAssocSemiringₓ R] : ∃ p, CharP R p := by
  let this := Classical.decEq R <;>
    exact
      Classical.by_cases
        (fun H : ∀ p : ℕ, (p : R) = 0 → p = 0 =>
          ⟨0,
            ⟨fun x => by
              rw [zero_dvd_iff] <;>
                exact
                  ⟨H x, by
                    rintro rfl <;> rfl⟩⟩⟩)
        fun H =>
        ⟨Nat.findₓ (not_forall.1 H),
          ⟨fun x =>
            ⟨fun H1 =>
              Nat.dvd_of_mod_eq_zeroₓ
                (by_contradiction fun H2 =>
                  Nat.find_minₓ (not_forall.1 H)
                    (Nat.mod_ltₓ x <| Nat.pos_of_ne_zeroₓ <| not_of_not_imp <| Nat.find_specₓ (not_forall.1 H))
                    (not_imp_of_and_not
                      ⟨by
                        rwa [← Nat.mod_add_divₓ x (Nat.findₓ (not_forall.1 H)), Nat.cast_addₓ, Nat.cast_mulₓ,
                          of_not_not (not_not_of_not_imp <| Nat.find_specₓ (not_forall.1 H)), zero_mul, add_zeroₓ] at
                          H1,
                        H2⟩)),
              fun H1 => by
              rw [← Nat.mul_div_cancel'ₓ H1, Nat.cast_mulₓ,
                of_not_not (not_not_of_not_imp <| Nat.find_specₓ (not_forall.1 H)), zero_mul]⟩⟩⟩

theorem CharP.exists_unique [NonAssocSemiringₓ R] : ∃! p, CharP R p :=
  let ⟨c, H⟩ := CharP.exists R
  ⟨c, H, fun y H2 => CharP.eq R H2 H⟩

theorem CharP.congr {R : Type u} [AddMonoidₓ R] [One R] {p : ℕ} (q : ℕ) [hq : CharP R q] (h : q = p) : CharP R p :=
  h ▸ hq

/-- Noncomputable function that outputs the unique characteristic of a semiring. -/
noncomputable def ringChar [NonAssocSemiringₓ R] : ℕ :=
  Classical.some (CharP.exists_unique R)

namespace ringChar

variable [NonAssocSemiringₓ R]

theorem spec : ∀ x : ℕ, (x : R) = 0 ↔ ringChar R ∣ x := by
  let this := (Classical.some_spec (CharP.exists_unique R)).1 <;>
    unfold ringChar <;> exact CharP.cast_eq_zero_iff R (ringChar R)

theorem eq (p : ℕ) [C : CharP R p] : ringChar R = p :=
  ((Classical.some_spec (CharP.exists_unique R)).2 p C).symm

instance char_p : CharP R (ringChar R) :=
  ⟨spec R⟩

variable {R}

theorem of_eq {p : ℕ} (h : ringChar R = p) : CharP R p :=
  CharP.congr (ringChar R) h

theorem eq_iff {p : ℕ} : ringChar R = p ↔ CharP R p :=
  ⟨of_eq, @eq R _ p⟩

theorem dvd {x : ℕ} (hx : (x : R) = 0) : ringChar R ∣ x :=
  (spec R x).1 hx

@[simp]
theorem eq_zero [CharZero R] : ringChar R = 0 :=
  eq R 0

end ringChar

theorem add_pow_char_of_commute [Semiringₓ R] {p : ℕ} [Fact p.Prime] [CharP R p] (x y : R) (h : Commute x y) :
    (x + y) ^ p = x ^ p + y ^ p := by
  rw [Commute.add_pow h, Finset.sum_range_succ_comm, tsub_self, pow_zeroₓ, Nat.choose_self]
  rw [Nat.cast_oneₓ, mul_oneₓ, mul_oneₓ]
  congr 1
  convert Finset.sum_eq_single 0 _ _
  · simp only [mul_oneₓ, one_mulₓ, Nat.choose_zero_right, tsub_zero, Nat.cast_oneₓ, pow_zeroₓ]
    
  · intro b h1 h2
    suffices (p.choose b : R) = 0 by
      rw [this]
      simp
    rw [CharP.cast_eq_zero_iff R p]
    refine' Nat.Prime.dvd_choose_self (pos_iff_ne_zero.mpr h2) _ (Fact.out _)
    rwa [← Finset.mem_range]
    
  · intro h1
    contrapose! h1
    rw [Finset.mem_range]
    exact Nat.Prime.pos (Fact.out _)
    

theorem add_pow_char_pow_of_commute [Semiringₓ R] {p : ℕ} [Fact p.Prime] [CharP R p] {n : ℕ} (x y : R)
    (h : Commute x y) : (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n := by
  induction n
  · simp
    
  rw [pow_succ'ₓ, pow_mulₓ, pow_mulₓ, pow_mulₓ, n_ih]
  apply add_pow_char_of_commute
  apply Commute.pow_pow h

theorem sub_pow_char_of_commute [Ringₓ R] {p : ℕ} [Fact p.Prime] [CharP R p] (x y : R) (h : Commute x y) :
    (x - y) ^ p = x ^ p - y ^ p := by
  rw [eq_sub_iff_add_eq, ← add_pow_char_of_commute _ _ _ (Commute.sub_left h rfl)]
  simp
  repeat'
    infer_instance

theorem sub_pow_char_pow_of_commute [Ringₓ R] {p : ℕ} [Fact p.Prime] [CharP R p] {n : ℕ} (x y : R) (h : Commute x y) :
    (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n := by
  induction n
  · simp
    
  rw [pow_succ'ₓ, pow_mulₓ, pow_mulₓ, pow_mulₓ, n_ih]
  apply sub_pow_char_of_commute
  apply Commute.pow_pow h

theorem add_pow_char [CommSemiringₓ R] {p : ℕ} [Fact p.Prime] [CharP R p] (x y : R) : (x + y) ^ p = x ^ p + y ^ p :=
  add_pow_char_of_commute _ _ _ (Commute.all _ _)

theorem add_pow_char_pow [CommSemiringₓ R] {p : ℕ} [Fact p.Prime] [CharP R p] {n : ℕ} (x y : R) :
    (x + y) ^ p ^ n = x ^ p ^ n + y ^ p ^ n :=
  add_pow_char_pow_of_commute _ _ _ (Commute.all _ _)

theorem sub_pow_char [CommRingₓ R] {p : ℕ} [Fact p.Prime] [CharP R p] (x y : R) : (x - y) ^ p = x ^ p - y ^ p :=
  sub_pow_char_of_commute _ _ _ (Commute.all _ _)

theorem sub_pow_char_pow [CommRingₓ R] {p : ℕ} [Fact p.Prime] [CharP R p] {n : ℕ} (x y : R) :
    (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n :=
  sub_pow_char_pow_of_commute _ _ _ (Commute.all _ _)

theorem eq_iff_modeq_int [Ringₓ R] (p : ℕ) [CharP R p] (a b : ℤ) : (a : R) = b ↔ a ≡ b [ZMOD p] := by
  rw [eq_comm, ← sub_eq_zero, ← Int.cast_sub, CharP.int_cast_eq_zero_iff R p, Int.modeq_iff_dvd]

theorem CharP.neg_one_ne_one [Ringₓ R] (p : ℕ) [CharP R p] [Fact (2 < p)] : (-1 : R) ≠ (1 : R) := by
  suffices (2 : R) ≠ 0 by
    symm
    rw [Ne.def, ← sub_eq_zero, sub_neg_eq_add]
    exact this
  intro h
  rw
    [show (2 : R) = (2 : ℕ) by
      norm_cast] at
    h
  have := (CharP.cast_eq_zero_iff R p 2).mp h
  have :=
    Nat.le_of_dvdₓ
      (by
        decide)
      this
  rw [fact_iff] at *
  linarith

theorem CharP.neg_one_pow_char [CommRingₓ R] (p : ℕ) [CharP R p] [Fact p.Prime] : (-1 : R) ^ p = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 1[← one_pow p]
  rw [← add_pow_char, add_left_negₓ, zero_pow (Fact.out (Nat.Prime p)).Pos]

theorem CharP.neg_one_pow_char_pow [CommRingₓ R] (p n : ℕ) [CharP R p] [Fact p.Prime] : (-1 : R) ^ p ^ n = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  nth_rw 1[← one_pow (p ^ n)]
  rw [← add_pow_char_pow, add_left_negₓ, zero_pow (pow_pos (Fact.out (Nat.Prime p)).Pos _)]

theorem RingHom.char_p_iff_char_p {K L : Type _} [DivisionRing K] [Semiringₓ L] [Nontrivial L] (f : K →+* L) (p : ℕ) :
    CharP K p ↔ CharP L p := by
  constructor <;>
    · intro _c
      constructor
      intro n
      rw [← @CharP.cast_eq_zero_iff _ _ _ p _c n, ← f.injective.eq_iff, map_nat_cast f, f.map_zero]
      

section frobenius

section CommSemiringₓ

variable [CommSemiringₓ R] {S : Type v} [CommSemiringₓ S] (f : R →* S) (g : R →+* S) (p : ℕ) [Fact p.Prime] [CharP R p]
  [CharP S p] (x y : R)

/-- The frobenius map that sends x to x^p -/
def frobenius : R →+* R where
  toFun := fun x => x ^ p
  map_one' := one_pow p
  map_mul' := fun x y => mul_powₓ x y p
  map_zero' := zero_pow (Fact.out (Nat.Prime p)).Pos
  map_add' := add_pow_char R

variable {R}

theorem frobenius_def : frobenius R p x = x ^ p :=
  rfl

theorem iterate_frobenius (n : ℕ) : (frobenius R p^[n]) x = x ^ p ^ n := by
  induction n
  · simp
    
  rw [Function.iterate_succ', pow_succ'ₓ, pow_mulₓ, Function.comp_applyₓ, frobenius_def, n_ih]

theorem frobenius_mul : frobenius R p (x * y) = frobenius R p x * frobenius R p y :=
  (frobenius R p).map_mul x y

theorem frobenius_one : frobenius R p 1 = 1 :=
  one_pow _

theorem MonoidHom.map_frobenius : f (frobenius R p x) = frobenius S p (f x) :=
  f.map_pow x p

theorem RingHom.map_frobenius : g (frobenius R p x) = frobenius S p (g x) :=
  g.map_pow x p

theorem MonoidHom.map_iterate_frobenius (n : ℕ) : f ((frobenius R p^[n]) x) = (frobenius S p^[n]) (f x) :=
  Function.Semiconj.iterate_right (f.map_frobenius p) n x

theorem RingHom.map_iterate_frobenius (n : ℕ) : g ((frobenius R p^[n]) x) = (frobenius S p^[n]) (g x) :=
  g.toMonoidHom.map_iterate_frobenius p x n

theorem MonoidHom.iterate_map_frobenius (f : R →* R) (p : ℕ) [Fact p.Prime] [CharP R p] (n : ℕ) :
    (f^[n]) (frobenius R p x) = frobenius R p ((f^[n]) x) :=
  f.iterate_map_pow _ _ _

theorem RingHom.iterate_map_frobenius (f : R →+* R) (p : ℕ) [Fact p.Prime] [CharP R p] (n : ℕ) :
    (f^[n]) (frobenius R p x) = frobenius R p ((f^[n]) x) :=
  f.iterate_map_pow _ _ _

variable (R)

theorem frobenius_zero : frobenius R p 0 = 0 :=
  (frobenius R p).map_zero

theorem frobenius_add : frobenius R p (x + y) = frobenius R p x + frobenius R p y :=
  (frobenius R p).map_add x y

theorem frobenius_nat_cast (n : ℕ) : frobenius R p n = n :=
  map_nat_cast (frobenius R p) n

open BigOperators

variable {R}

theorem list_sum_pow_char (l : List R) : l.Sum ^ p = (l.map (· ^ p)).Sum :=
  (frobenius R p).map_list_sum _

theorem multiset_sum_pow_char (s : Multiset R) : s.Sum ^ p = (s.map (· ^ p)).Sum :=
  (frobenius R p).map_multiset_sum _

theorem sum_pow_char {ι : Type _} (s : Finset ι) (f : ι → R) : (∑ i in s, f i) ^ p = ∑ i in s, f i ^ p :=
  (frobenius R p).map_sum _ _

end CommSemiringₓ

section CommRingₓ

variable [CommRingₓ R] {S : Type v} [CommRingₓ S] (f : R →* S) (g : R →+* S) (p : ℕ) [Fact p.Prime] [CharP R p]
  [CharP S p] (x y : R)

theorem frobenius_neg : frobenius R p (-x) = -frobenius R p x :=
  (frobenius R p).map_neg x

theorem frobenius_sub : frobenius R p (x - y) = frobenius R p x - frobenius R p y :=
  (frobenius R p).map_sub x y

end CommRingₓ

end frobenius

theorem frobenius_inj [CommRingₓ R] [IsReduced R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    Function.Injective (frobenius R p) := fun x h H => by
  rw [← sub_eq_zero] at H⊢
  rw [← frobenius_sub] at H
  exact IsReduced.eq_zero _ ⟨_, H⟩

namespace CharP

section

variable [Ringₓ R]

theorem char_p_to_char_zero (R : Type _) [AddLeftCancelMonoid R] [One R] [CharP R 0] : CharZero R :=
  char_zero_of_inj_zero fun n h0 => eq_zero_of_zero_dvd ((cast_eq_zero_iff R 0 n).mp h0)

theorem cast_eq_mod (p : ℕ) [CharP R p] (k : ℕ) : (k : R) = (k % p : ℕ) :=
  calc
    (k : R) = ↑(k % p + p * (k / p)) := by
      rw [Nat.mod_add_divₓ]
    _ = ↑(k % p) := by
      simp [cast_eq_zero]
    

theorem char_ne_zero_of_fintype (p : ℕ) [hc : CharP R p] [Fintype R] : p ≠ 0 := fun h : p = 0 =>
  have : CharZero R := @char_p_to_char_zero R _ _ (h ▸ hc)
  absurd (@Nat.cast_injective R _ _ this) (not_injective_infinite_fintype coe)

end

section Semiringₓ

open Nat

variable [NonAssocSemiringₓ R]

theorem char_ne_one [Nontrivial R] (p : ℕ) [hc : CharP R p] : p ≠ 1 := fun hp : p = 1 =>
  have : (1 : R) = 0 := by
    simpa using (cast_eq_zero_iff R p 1).mpr (hp ▸ dvd_refl p)
  absurd this one_ne_zero

section NoZeroDivisors

variable [NoZeroDivisors R]

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (d «expr ∣ » p)
theorem char_is_prime_of_two_le (p : ℕ) [hc : CharP R p] (hp : 2 ≤ p) : Nat.Prime p :=
  suffices ∀ d _ : d ∣ p, d = 1 ∨ d = p from Nat.prime_def_lt''.mpr ⟨hp, this⟩
  fun hdvd : ∃ e, p = d * e =>
  let ⟨e, hmul⟩ := hdvd
  have : (p : R) = 0 := (cast_eq_zero_iff R p p).mpr (dvd_refl p)
  have : (d : R) * e = 0 := @cast_mulₓ R _ d e ▸ hmul ▸ this
  Or.elim (eq_zero_or_eq_zero_of_mul_eq_zero this)
    (fun hd : (d : R) = 0 =>
      have : p ∣ d := (cast_eq_zero_iff R p d).mp hd
      show d = 1 ∨ d = p from Or.inr (dvd_antisymm ⟨e, hmul⟩ this))
    fun he : (e : R) = 0 =>
    have : p ∣ e := (cast_eq_zero_iff R p e).mp he
    have : e ∣ p := dvd_of_mul_left_eq d (Eq.symm hmul)
    have : e = p := dvd_antisymm ‹e ∣ p› ‹p ∣ e›
    have h₀ : p > 0 := gt_of_ge_of_gtₓ hp (Nat.zero_lt_succₓ 1)
    have : d * p = 1 * p := by
      rw [‹e = p›] at hmul <;> rw [one_mulₓ] <;> exact Eq.symm hmul
    show d = 1 ∨ d = p from Or.inl (eq_of_mul_eq_mul_rightₓ h₀ this)

section Nontrivial

variable [Nontrivial R]

theorem char_is_prime_or_zero (p : ℕ) [hc : CharP R p] : Nat.Prime p ∨ p = 0 :=
  match p, hc with
  | 0, _ => Or.inr rfl
  | 1, hc => absurd (Eq.refl (1 : ℕ)) (@char_ne_one R _ _ (1 : ℕ) hc)
  | m + 2, hc => Or.inl (@char_is_prime_of_two_le R _ _ (m + 2) hc (Nat.le_add_leftₓ 2 m))

theorem char_is_prime_of_pos (p : ℕ) [h : Fact (0 < p)] [CharP R p] : Fact p.Prime :=
  ⟨(CharP.char_is_prime_or_zero R _).resolve_right (pos_iff_ne_zero.1 h.1)⟩

end Nontrivial

end NoZeroDivisors

end Semiringₓ

section Ringₓ

variable (R) [Ringₓ R] [NoZeroDivisors R] [Nontrivial R] [Fintype R]

theorem char_is_prime (p : ℕ) [CharP R p] : p.Prime :=
  Or.resolve_right (char_is_prime_or_zero R p) (char_ne_zero_of_fintype R p)

end Ringₓ

section CharOne

variable {R} [NonAssocSemiringₓ R]

-- see Note [lower instance priority]
instance (priority := 100) [CharP R 1] : Subsingleton R :=
  Subsingleton.intro <|
    suffices ∀ r : R, r = 0 from fun a b =>
      show a = b by
        rw [this a, this b]
    fun r =>
    calc
      r = 1 * r := by
        rw [one_mulₓ]
      _ = (1 : ℕ) * r := by
        rw [Nat.cast_oneₓ]
      _ = 0 * r := by
        rw [CharP.cast_eq_zero]
      _ = 0 := by
        rw [zero_mul]
      

theorem false_of_nontrivial_of_char_one [Nontrivial R] [CharP R 1] : False :=
  false_of_nontrivial_of_subsingleton R

theorem ring_char_ne_one [Nontrivial R] : ringChar R ≠ 1 := by
  intro h
  apply @zero_ne_one R
  symm
  rw [← Nat.cast_oneₓ, ringChar.spec, h]

theorem nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) [hr : CharP R v] : Nontrivial R :=
  ⟨⟨(1 : ℕ), 0, fun h =>
      hv <| by
        rwa [CharP.cast_eq_zero_iff _ v, Nat.dvd_one] at h <;> assumption⟩⟩

theorem ring_char_of_prime_eq_zero [Nontrivial R] {p : ℕ} (hprime : Nat.Prime p) (hp0 : (p : R) = 0) : ringChar R = p :=
  Or.resolve_left ((Nat.dvd_prime hprime).1 (ringChar.dvd hp0)) ring_char_ne_one

end CharOne

end CharP

section

variable (R) [CommRingₓ R] [Fintype R] (n : ℕ)

theorem char_p_of_ne_zero (hn : Fintype.card R = n) (hR : ∀, ∀ i < n, ∀, (i : R) = 0 → i = 0) : CharP R n :=
  { cast_eq_zero_iff := by
      have H : (n : R) = 0 := by
        rw [← hn, CharP.cast_card_eq_zero]
      intro k
      constructor
      · intro h
        rw [← Nat.mod_add_divₓ k n, Nat.cast_addₓ, Nat.cast_mulₓ, H, zero_mul, add_zeroₓ] at h
        rw [Nat.dvd_iff_mod_eq_zeroₓ]
        apply hR _ (Nat.mod_ltₓ _ _) h
        rw [← hn, Fintype.card_pos_iff]
        exact ⟨0⟩
        
      · rintro ⟨k, rfl⟩
        rw [Nat.cast_mulₓ, H, zero_mul]
         }

theorem char_p_of_prime_pow_injective (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : Fintype.card R = p ^ n)
    (hR : ∀, ∀ i ≤ n, ∀, (p ^ i : R) = 0 → i = n) : CharP R (p ^ n) := by
  obtain ⟨c, hc⟩ := CharP.exists R
  skip
  have hcpn : c ∣ p ^ n := by
    rw [← CharP.cast_eq_zero_iff R c, ← hn, CharP.cast_card_eq_zero]
  obtain ⟨i, hi, hc⟩ : ∃ i ≤ n, c = p ^ i := by
    rwa [Nat.dvd_prime_pow hp.1] at hcpn
  obtain rfl : i = n := by
    apply hR i hi
    rw [← Nat.cast_powₓ, ← hc, CharP.cast_eq_zero]
  rwa [← hc]

end

section Prod

variable (S : Type v) [Semiringₓ R] [Semiringₓ S] (p q : ℕ) [CharP R p]

/-- The characteristic of the product of rings is the least common multiple of the
characteristics of the two rings. -/
instance [CharP S q] : CharP (R × S) (Nat.lcmₓ p q) where
  cast_eq_zero_iff := by
    simp [Prod.ext_iff, CharP.cast_eq_zero_iff R p, CharP.cast_eq_zero_iff S q, Nat.lcm_dvd_iff]

/-- The characteristic of the product of two rings of the same characteristic
  is the same as the characteristic of the rings -/
instance Prod.char_p [CharP S p] : CharP (R × S) p := by
  convert Nat.lcmₓ.char_p R S p p <;> simp

end Prod

