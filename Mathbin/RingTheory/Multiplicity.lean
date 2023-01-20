/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Chris Hughes

! This file was ported from Lean 3 source module ring_theory.multiplicity
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Associated
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.RingTheory.Valuation.Basic

/-!
# Multiplicity of a divisor

For a commutative monoid, this file introduces the notion of multiplicity of a divisor and proves
several basic results on it.

## Main definitions

* `multiplicity a b`: for two elements `a` and `b` of a commutative monoid returns the largest
  number `n` such that `a ^ n ∣ b` or infinity, written `⊤`, if `a ^ n ∣ b` for all natural numbers
  `n`.
* `multiplicity.finite a b`: a predicate denoting that the multiplicity of `a` in `b` is finite.
-/


variable {α : Type _}

open Nat Part

open BigOperators

/-- `multiplicity a b` returns the largest natural number `n` such that
  `a ^ n ∣ b`, as an `part_enat` or natural with infinity. If `∀ n, a ^ n ∣ b`,
  then it returns `⊤`-/
def multiplicity [Monoid α] [DecidableRel ((· ∣ ·) : α → α → Prop)] (a b : α) : PartEnat :=
  PartEnat.find fun n => ¬a ^ (n + 1) ∣ b
#align multiplicity multiplicity

namespace multiplicity

section Monoid

variable [Monoid α]

/-- `multiplicity.finite a b` indicates that the multiplicity of `a` in `b` is finite. -/
@[reducible]
def Finite (a b : α) : Prop :=
  ∃ n : ℕ, ¬a ^ (n + 1) ∣ b
#align multiplicity.finite multiplicity.Finite

theorem finite_iff_dom [DecidableRel ((· ∣ ·) : α → α → Prop)] {a b : α} :
    Finite a b ↔ (multiplicity a b).Dom :=
  Iff.rfl
#align multiplicity.finite_iff_dom multiplicity.finite_iff_dom

theorem finite_def {a b : α} : Finite a b ↔ ∃ n : ℕ, ¬a ^ (n + 1) ∣ b :=
  Iff.rfl
#align multiplicity.finite_def multiplicity.finite_def

theorem not_dvd_one_of_finite_one_right {a : α} : Finite a 1 → ¬a ∣ 1 := fun ⟨n, hn⟩ ⟨d, hd⟩ =>
  hn ⟨d ^ (n + 1), (pow_mul_pow_eq_one (n + 1) hd.symm).symm⟩
#align multiplicity.not_dvd_one_of_finite_one_right multiplicity.not_dvd_one_of_finite_one_right

@[norm_cast]
theorem Int.coe_nat_multiplicity (a b : ℕ) : multiplicity (a : ℤ) (b : ℤ) = multiplicity a b :=
  by
  apply Part.ext'
  · repeat' rw [← finite_iff_dom, finite_def]
    norm_cast
  · intro h1 h2
    apply _root_.le_antisymm <;>
      · apply Nat.find_mono
        norm_cast
        simp
#align multiplicity.int.coe_nat_multiplicity multiplicity.Int.coe_nat_multiplicity

theorem not_finite_iff_forall {a b : α} : ¬Finite a b ↔ ∀ n : ℕ, a ^ n ∣ b :=
  ⟨fun h n =>
    Nat.casesOn n
      (by
        rw [pow_zero]
        exact one_dvd _)
      (by simpa [Finite, not_not] using h),
    by simp [Finite, multiplicity, not_not] <;> tauto⟩
#align multiplicity.not_finite_iff_forall multiplicity.not_finite_iff_forall

theorem not_unit_of_finite {a b : α} (h : Finite a b) : ¬IsUnit a :=
  let ⟨n, hn⟩ := h
  hn ∘ IsUnit.dvd ∘ IsUnit.pow (n + 1)
#align multiplicity.not_unit_of_finite multiplicity.not_unit_of_finite

theorem finite_of_finite_mul_right {a b c : α} : Finite a (b * c) → Finite a b := fun ⟨n, hn⟩ =>
  ⟨n, fun h => hn (h.trans (dvd_mul_right _ _))⟩
#align multiplicity.finite_of_finite_mul_right multiplicity.finite_of_finite_mul_right

variable [DecidableRel ((· ∣ ·) : α → α → Prop)]

theorem pow_dvd_of_le_multiplicity {a b : α} {k : ℕ} :
    (k : PartEnat) ≤ multiplicity a b → a ^ k ∣ b :=
  by
  rw [← PartEnat.some_eq_coe]
  exact
    Nat.casesOn k
      (fun _ => by
        rw [pow_zero]
        exact one_dvd _)
      fun k ⟨h₁, h₂⟩ => by_contradiction fun hk => Nat.find_min _ (lt_of_succ_le (h₂ ⟨k, hk⟩)) hk
#align multiplicity.pow_dvd_of_le_multiplicity multiplicity.pow_dvd_of_le_multiplicity

theorem pow_multiplicity_dvd {a b : α} (h : Finite a b) : a ^ get (multiplicity a b) h ∣ b :=
  pow_dvd_of_le_multiplicity (by rw [PartEnat.coe_get])
#align multiplicity.pow_multiplicity_dvd multiplicity.pow_multiplicity_dvd

theorem is_greatest {a b : α} {m : ℕ} (hm : multiplicity a b < m) : ¬a ^ m ∣ b := fun h => by
  rw [PartEnat.lt_coe_iff] at hm <;> exact Nat.find_spec hm.fst ((pow_dvd_pow _ hm.snd).trans h)
#align multiplicity.is_greatest multiplicity.is_greatest

theorem is_greatest' {a b : α} {m : ℕ} (h : Finite a b) (hm : get (multiplicity a b) h < m) :
    ¬a ^ m ∣ b :=
  is_greatest (by rwa [← PartEnat.coe_lt_coe, PartEnat.coe_get] at hm)
#align multiplicity.is_greatest' multiplicity.is_greatest'

theorem pos_of_dvd {a b : α} (hfin : Finite a b) (hdiv : a ∣ b) : 0 < (multiplicity a b).get hfin :=
  by
  refine' zero_lt_iff.2 fun h => _
  simpa [hdiv] using is_greatest' hfin (lt_one_iff.mpr h)
#align multiplicity.pos_of_dvd multiplicity.pos_of_dvd

theorem unique {a b : α} {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
    (k : PartEnat) = multiplicity a b :=
  le_antisymm (le_of_not_gt fun hk' => is_greatest hk' hk) <|
    by
    have : Finite a b := ⟨k, hsucc⟩
    rw [PartEnat.le_coe_iff]
    exact ⟨this, Nat.find_min' _ hsucc⟩
#align multiplicity.unique multiplicity.unique

theorem unique' {a b : α} {k : ℕ} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) :
    k = get (multiplicity a b) ⟨k, hsucc⟩ := by
  rw [← PartEnat.coe_inj, PartEnat.coe_get, Unique hk hsucc]
#align multiplicity.unique' multiplicity.unique'

theorem le_multiplicity_of_pow_dvd {a b : α} {k : ℕ} (hk : a ^ k ∣ b) :
    (k : PartEnat) ≤ multiplicity a b :=
  le_of_not_gt fun hk' => is_greatest hk' hk
#align multiplicity.le_multiplicity_of_pow_dvd multiplicity.le_multiplicity_of_pow_dvd

theorem pow_dvd_iff_le_multiplicity {a b : α} {k : ℕ} :
    a ^ k ∣ b ↔ (k : PartEnat) ≤ multiplicity a b :=
  ⟨le_multiplicity_of_pow_dvd, pow_dvd_of_le_multiplicity⟩
#align multiplicity.pow_dvd_iff_le_multiplicity multiplicity.pow_dvd_iff_le_multiplicity

theorem multiplicity_lt_iff_neg_dvd {a b : α} {k : ℕ} :
    multiplicity a b < (k : PartEnat) ↔ ¬a ^ k ∣ b := by rw [pow_dvd_iff_le_multiplicity, not_le]
#align multiplicity.multiplicity_lt_iff_neg_dvd multiplicity.multiplicity_lt_iff_neg_dvd

theorem eq_coe_iff {a b : α} {n : ℕ} :
    multiplicity a b = (n : PartEnat) ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b :=
  by
  rw [← PartEnat.some_eq_coe]
  exact
    ⟨fun h =>
      let ⟨h₁, h₂⟩ := eq_some_iff.1 h
      h₂ ▸
        ⟨pow_multiplicity_dvd _,
          IsGreatest
            (by
              rw [PartEnat.lt_coe_iff]
              exact ⟨h₁, lt_succ_self _⟩)⟩,
      fun h => eq_some_iff.2 ⟨⟨n, h.2⟩, Eq.symm <| unique' h.1 h.2⟩⟩
#align multiplicity.eq_coe_iff multiplicity.eq_coe_iff

theorem eq_top_iff {a b : α} : multiplicity a b = ⊤ ↔ ∀ n : ℕ, a ^ n ∣ b :=
  (PartEnat.find_eq_top_iff _).trans <| by
    simp only [not_not]
    exact
      ⟨fun h n =>
        Nat.casesOn n
          (by
            rw [pow_zero]
            exact one_dvd _)
          fun n => h _,
        fun h n => h _⟩
#align multiplicity.eq_top_iff multiplicity.eq_top_iff

@[simp]
theorem is_unit_left {a : α} (b : α) (ha : IsUnit a) : multiplicity a b = ⊤ :=
  eq_top_iff.2 fun _ => IsUnit.dvd (ha.pow _)
#align multiplicity.is_unit_left multiplicity.is_unit_left

@[simp]
theorem one_left (b : α) : multiplicity 1 b = ⊤ :=
  is_unit_left b isUnit_one
#align multiplicity.one_left multiplicity.one_left

@[simp]
theorem get_one_right {a : α} (ha : Finite a 1) : get (multiplicity a 1) ha = 0 :=
  by
  rw [PartEnat.get_eq_iff_eq_coe, eq_coe_iff, pow_zero]
  simp [not_dvd_one_of_finite_one_right ha]
#align multiplicity.get_one_right multiplicity.get_one_right

@[simp]
theorem unit_left (a : α) (u : αˣ) : multiplicity (u : α) a = ⊤ :=
  is_unit_left a u.IsUnit
#align multiplicity.unit_left multiplicity.unit_left

theorem multiplicity_eq_zero {a b : α} : multiplicity a b = 0 ↔ ¬a ∣ b :=
  by
  rw [← Nat.cast_zero, eq_coe_iff]
  simp
#align multiplicity.multiplicity_eq_zero multiplicity.multiplicity_eq_zero

theorem eq_top_iff_not_finite {a b : α} : multiplicity a b = ⊤ ↔ ¬Finite a b :=
  Part.eq_none_iff'
#align multiplicity.eq_top_iff_not_finite multiplicity.eq_top_iff_not_finite

theorem ne_top_iff_finite {a b : α} : multiplicity a b ≠ ⊤ ↔ Finite a b := by
  rw [Ne.def, eq_top_iff_not_finite, not_not]
#align multiplicity.ne_top_iff_finite multiplicity.ne_top_iff_finite

theorem lt_top_iff_finite {a b : α} : multiplicity a b < ⊤ ↔ Finite a b := by
  rw [lt_top_iff_ne_top, ne_top_iff_finite]
#align multiplicity.lt_top_iff_finite multiplicity.lt_top_iff_finite

theorem exists_eq_pow_mul_and_not_dvd {a b : α} (hfin : Finite a b) :
    ∃ c : α, b = a ^ (multiplicity a b).get hfin * c ∧ ¬a ∣ c :=
  by
  obtain ⟨c, hc⟩ := multiplicity.pow_multiplicity_dvd hfin
  refine' ⟨c, hc, _⟩
  rintro ⟨k, hk⟩
  rw [hk, ← mul_assoc, ← pow_succ'] at hc
  have h₁ : a ^ ((multiplicity a b).get hfin + 1) ∣ b := ⟨k, hc⟩
  exact (multiplicity.eq_coe_iff.1 (by simp)).2 h₁
#align multiplicity.exists_eq_pow_mul_and_not_dvd multiplicity.exists_eq_pow_mul_and_not_dvd

open Classical

theorem multiplicity_le_multiplicity_iff {a b c d : α} :
    multiplicity a b ≤ multiplicity c d ↔ ∀ n : ℕ, a ^ n ∣ b → c ^ n ∣ d :=
  ⟨fun h n hab => pow_dvd_of_le_multiplicity (le_trans (le_multiplicity_of_pow_dvd hab) h), fun h =>
    if hab : Finite a b then by
      rw [← PartEnat.coe_get (finite_iff_dom.1 hab)] <;>
        exact le_multiplicity_of_pow_dvd (h _ (pow_multiplicity_dvd _))
    else by
      have : ∀ n : ℕ, c ^ n ∣ d := fun n => h n (not_finite_iff_forall.1 hab _)
      rw [eq_top_iff_not_finite.2 hab, eq_top_iff_not_finite.2 (not_finite_iff_forall.2 this)]⟩
#align multiplicity.multiplicity_le_multiplicity_iff multiplicity.multiplicity_le_multiplicity_iff

theorem multiplicity_eq_multiplicity_iff {a b c d : α} :
    multiplicity a b = multiplicity c d ↔ ∀ n : ℕ, a ^ n ∣ b ↔ c ^ n ∣ d :=
  ⟨fun h n =>
    ⟨multiplicity_le_multiplicity_iff.mp h.le n, multiplicity_le_multiplicity_iff.mp h.ge n⟩,
    fun h =>
    le_antisymm (multiplicity_le_multiplicity_iff.mpr fun n => (h n).mp)
      (multiplicity_le_multiplicity_iff.mpr fun n => (h n).mpr)⟩
#align multiplicity.multiplicity_eq_multiplicity_iff multiplicity.multiplicity_eq_multiplicity_iff

theorem multiplicity_le_multiplicity_of_dvd_right {a b c : α} (h : b ∣ c) :
    multiplicity a b ≤ multiplicity a c :=
  multiplicity_le_multiplicity_iff.2 fun n hb => hb.trans h
#align multiplicity.multiplicity_le_multiplicity_of_dvd_right multiplicity.multiplicity_le_multiplicity_of_dvd_right

theorem eq_of_associated_right {a b c : α} (h : Associated b c) :
    multiplicity a b = multiplicity a c :=
  le_antisymm (multiplicity_le_multiplicity_of_dvd_right h.Dvd)
    (multiplicity_le_multiplicity_of_dvd_right h.symm.Dvd)
#align multiplicity.eq_of_associated_right multiplicity.eq_of_associated_right

theorem dvd_of_multiplicity_pos {a b : α} (h : (0 : PartEnat) < multiplicity a b) : a ∣ b :=
  by
  rw [← pow_one a]
  apply pow_dvd_of_le_multiplicity
  simpa only [Nat.cast_one, PartEnat.pos_iff_one_le] using h
#align multiplicity.dvd_of_multiplicity_pos multiplicity.dvd_of_multiplicity_pos

theorem dvd_iff_multiplicity_pos {a b : α} : (0 : PartEnat) < multiplicity a b ↔ a ∣ b :=
  ⟨dvd_of_multiplicity_pos, fun hdvd =>
    lt_of_le_of_ne (zero_le _) fun heq =>
      is_greatest
        (show multiplicity a b < ↑1 by
          simpa only [HEq, Nat.cast_zero] using part_enat.coe_lt_coe.mpr zero_lt_one)
        (by rwa [pow_one a])⟩
#align multiplicity.dvd_iff_multiplicity_pos multiplicity.dvd_iff_multiplicity_pos

theorem finite_nat_iff {a b : ℕ} : Finite a b ↔ a ≠ 1 ∧ 0 < b :=
  by
  rw [← not_iff_not, not_finite_iff_forall, not_and_or, Ne.def, not_not, not_lt, le_zero_iff]
  exact
    ⟨fun h =>
      or_iff_not_imp_right.2 fun hb =>
        have ha : a ≠ 0 := fun ha => by simpa [ha] using h 1
        by_contradiction fun ha1 : a ≠ 1 =>
          have ha_gt_one : 1 < a :=
            lt_of_not_ge fun ha' => by
              clear h
              revert ha ha1
              decide!
          not_lt_of_ge (le_of_dvd (Nat.pos_of_ne_zero hb) (h b)) (lt_pow_self ha_gt_one b),
      fun h => by cases h <;> simp [*]⟩
#align multiplicity.finite_nat_iff multiplicity.finite_nat_iff

alias dvd_iff_multiplicity_pos ↔ _ _root_.has_dvd.dvd.multiplicity_pos
#align has_dvd.dvd.multiplicity_pos Dvd.Dvd.multiplicity_pos

end Monoid

section CommMonoid

variable [CommMonoid α]

theorem finite_of_finite_mul_left {a b c : α} : Finite a (b * c) → Finite a c := by
  rw [mul_comm] <;> exact finite_of_finite_mul_right
#align multiplicity.finite_of_finite_mul_left multiplicity.finite_of_finite_mul_left

variable [DecidableRel ((· ∣ ·) : α → α → Prop)]

theorem is_unit_right {a b : α} (ha : ¬IsUnit a) (hb : IsUnit b) : multiplicity a b = 0 :=
  eq_coe_iff.2
    ⟨show a ^ 0 ∣ b by simp only [pow_zero, one_dvd],
      by
      rw [pow_one]
      exact fun h => mt (isUnit_of_dvd_unit h) ha hb⟩
#align multiplicity.is_unit_right multiplicity.is_unit_right

theorem one_right {a : α} (ha : ¬IsUnit a) : multiplicity a 1 = 0 :=
  is_unit_right ha isUnit_one
#align multiplicity.one_right multiplicity.one_right

theorem unit_right {a : α} (ha : ¬IsUnit a) (u : αˣ) : multiplicity a u = 0 :=
  is_unit_right ha u.IsUnit
#align multiplicity.unit_right multiplicity.unit_right

open Classical

theorem multiplicity_le_multiplicity_of_dvd_left {a b c : α} (hdvd : a ∣ b) :
    multiplicity b c ≤ multiplicity a c :=
  multiplicity_le_multiplicity_iff.2 fun n h => (pow_dvd_pow_of_dvd hdvd n).trans h
#align multiplicity.multiplicity_le_multiplicity_of_dvd_left multiplicity.multiplicity_le_multiplicity_of_dvd_left

theorem eq_of_associated_left {a b c : α} (h : Associated a b) :
    multiplicity b c = multiplicity a c :=
  le_antisymm (multiplicity_le_multiplicity_of_dvd_left h.Dvd)
    (multiplicity_le_multiplicity_of_dvd_left h.symm.Dvd)
#align multiplicity.eq_of_associated_left multiplicity.eq_of_associated_left

alias dvd_iff_multiplicity_pos ↔ _ _root_.has_dvd.dvd.multiplicity_pos
#align has_dvd.dvd.multiplicity_pos Dvd.Dvd.multiplicity_pos

end CommMonoid

section MonoidWithZero

variable [MonoidWithZero α]

theorem ne_zero_of_finite {a b : α} (h : Finite a b) : b ≠ 0 :=
  let ⟨n, hn⟩ := h
  fun hb => by simpa [hb] using hn
#align multiplicity.ne_zero_of_finite multiplicity.ne_zero_of_finite

variable [DecidableRel ((· ∣ ·) : α → α → Prop)]

@[simp]
protected theorem zero (a : α) : multiplicity a 0 = ⊤ :=
  Part.eq_none_iff.2 fun n ⟨⟨k, hk⟩, _⟩ => hk (dvd_zero _)
#align multiplicity.zero multiplicity.zero

@[simp]
theorem multiplicity_zero_eq_zero_of_ne_zero (a : α) (ha : a ≠ 0) : multiplicity 0 a = 0 :=
  multiplicity.multiplicity_eq_zero.2 <| mt zero_dvd_iff.1 ha
#align multiplicity.multiplicity_zero_eq_zero_of_ne_zero multiplicity.multiplicity_zero_eq_zero_of_ne_zero

end MonoidWithZero

section CommMonoidWithZero

variable [CommMonoidWithZero α]

variable [DecidableRel ((· ∣ ·) : α → α → Prop)]

theorem multiplicity_mk_eq_multiplicity
    [DecidableRel ((· ∣ ·) : Associates α → Associates α → Prop)] {a b : α} :
    multiplicity (Associates.mk a) (Associates.mk b) = multiplicity a b :=
  by
  by_cases h : Finite a b
  · rw [← PartEnat.coe_get (finite_iff_dom.mp h)]
    refine'
        (multiplicity.unique
            (show Associates.mk a ^ (multiplicity a b).get h ∣ Associates.mk b from _) _).symm <;>
      rw [← Associates.mk_pow, Associates.mk_dvd_mk]
    · exact pow_multiplicity_dvd h
    ·
      exact
        IsGreatest
          ((PartEnat.lt_coe_iff _ _).mpr (Exists.intro (finite_iff_dom.mp h) (Nat.lt_succ_self _)))
  · suffices ¬Finite (Associates.mk a) (Associates.mk b)
      by
      rw [finite_iff_dom, PartEnat.not_dom_iff_eq_top] at h this
      rw [h, this]
    refine'
      not_finite_iff_forall.mpr fun n =>
        by
        rw [← Associates.mk_pow, Associates.mk_dvd_mk]
        exact not_finite_iff_forall.mp h n
#align multiplicity.multiplicity_mk_eq_multiplicity multiplicity.multiplicity_mk_eq_multiplicity

end CommMonoidWithZero

section Semiring

variable [Semiring α] [DecidableRel ((· ∣ ·) : α → α → Prop)]

theorem min_le_multiplicity_add {p a b : α} :
    min (multiplicity p a) (multiplicity p b) ≤ multiplicity p (a + b) :=
  (le_total (multiplicity p a) (multiplicity p b)).elim
    (fun h => by
      rw [min_eq_left h, multiplicity_le_multiplicity_iff] <;>
        exact fun n hn => dvd_add hn (multiplicity_le_multiplicity_iff.1 h n hn))
    fun h => by
    rw [min_eq_right h, multiplicity_le_multiplicity_iff] <;>
      exact fun n hn => dvd_add (multiplicity_le_multiplicity_iff.1 h n hn) hn
#align multiplicity.min_le_multiplicity_add multiplicity.min_le_multiplicity_add

end Semiring

section Ring

variable [Ring α] [DecidableRel ((· ∣ ·) : α → α → Prop)]

@[simp]
protected theorem neg (a b : α) : multiplicity a (-b) = multiplicity a b :=
  Part.ext' (by simp only [multiplicity, PartEnat.find, dvd_neg]) fun h₁ h₂ =>
    PartEnat.coe_inj.1
      (by
        rw [PartEnat.coe_get] <;>
          exact
            Eq.symm
              (Unique ((dvd_neg _ _).2 (pow_multiplicity_dvd _))
                (mt (dvd_neg _ _).1 (is_greatest' _ (lt_succ_self _)))))
#align multiplicity.neg multiplicity.neg

theorem Int.nat_abs (a : ℕ) (b : ℤ) : multiplicity a b.natAbs = multiplicity (a : ℤ) b :=
  by
  cases' Int.natAbs_eq b with h h <;> conv_rhs => rw [h]
  · rw [int.coe_nat_multiplicity]
  · rw [multiplicity.neg, int.coe_nat_multiplicity]
#align multiplicity.int.nat_abs multiplicity.Int.nat_abs

theorem multiplicity_add_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a) :
    multiplicity p (a + b) = multiplicity p b :=
  by
  apply le_antisymm
  · apply PartEnat.le_of_lt_add_one
    cases' part_enat.ne_top_iff.mp (PartEnat.ne_top_of_lt h) with k hk
    rw [hk]
    rw_mod_cast [multiplicity_lt_iff_neg_dvd]
    intro h_dvd
    rw [← dvd_add_iff_right] at h_dvd
    apply multiplicity.is_greatest _ h_dvd
    rw [hk]
    apply_mod_cast Nat.lt_succ_self
    rw [pow_dvd_iff_le_multiplicity, Nat.cast_add, ← hk, Nat.cast_one]
    exact PartEnat.add_one_le_of_lt h
  · convert min_le_multiplicity_add
    rw [min_eq_right (le_of_lt h)]
#align multiplicity.multiplicity_add_of_gt multiplicity.multiplicity_add_of_gt

theorem multiplicity_sub_of_gt {p a b : α} (h : multiplicity p b < multiplicity p a) :
    multiplicity p (a - b) = multiplicity p b := by
  rw [sub_eq_add_neg, multiplicity_add_of_gt] <;> rwa [multiplicity.neg]
#align multiplicity.multiplicity_sub_of_gt multiplicity.multiplicity_sub_of_gt

theorem multiplicity_add_eq_min {p a b : α} (h : multiplicity p a ≠ multiplicity p b) :
    multiplicity p (a + b) = min (multiplicity p a) (multiplicity p b) :=
  by
  rcases lt_trichotomy (multiplicity p a) (multiplicity p b) with (hab | hab | hab)
  · rw [add_comm, multiplicity_add_of_gt hab, min_eq_left]
    exact le_of_lt hab
  · contradiction
  · rw [multiplicity_add_of_gt hab, min_eq_right]
    exact le_of_lt hab
#align multiplicity.multiplicity_add_eq_min multiplicity.multiplicity_add_eq_min

end Ring

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α]

theorem finite_mul_aux {p : α} (hp : Prime p) :
    ∀ {n m : ℕ} {a b : α}, ¬p ^ (n + 1) ∣ a → ¬p ^ (m + 1) ∣ b → ¬p ^ (n + m + 1) ∣ a * b
  | n, m => fun a b ha hb ⟨s, hs⟩ =>
    have : p ∣ a * b := ⟨p ^ (n + m) * s, by simp [hs, pow_add, mul_comm, mul_assoc, mul_left_comm]⟩
    (hp.2.2 a b this).elim
      (fun ⟨x, hx⟩ =>
        have hn0 : 0 < n :=
          Nat.pos_of_ne_zero fun hn0 => by clear _fun_match _fun_match <;> simpa [hx, hn0] using ha
        have wf : n - 1 < n := tsub_lt_self hn0 (by decide)
        have hpx : ¬p ^ (n - 1 + 1) ∣ x := fun ⟨y, hy⟩ =>
          ha
            (hx.symm ▸
              ⟨y,
                mul_right_cancel₀ hp.1 <| by
                  rw [tsub_add_cancel_of_le (succ_le_of_lt hn0)] at hy <;>
                    simp [hy, pow_add, mul_comm, mul_assoc, mul_left_comm]⟩)
        have : 1 ≤ n + m := le_trans hn0 (Nat.le_add_right n m)
        finite_mul_aux hpx hb
          ⟨s,
            mul_right_cancel₀ hp.1
              (by
                rw [tsub_add_eq_add_tsub (succ_le_of_lt hn0), tsub_add_cancel_of_le this]
                clear _fun_match _fun_match finite_mul_aux
                simp_all [mul_comm, mul_assoc, mul_left_comm, pow_add])⟩)
      fun ⟨x, hx⟩ =>
      have hm0 : 0 < m :=
        Nat.pos_of_ne_zero fun hm0 => by clear _fun_match _fun_match <;> simpa [hx, hm0] using hb
      have wf : m - 1 < m := tsub_lt_self hm0 (by decide)
      have hpx : ¬p ^ (m - 1 + 1) ∣ x := fun ⟨y, hy⟩ =>
        hb
          (hx.symm ▸
            ⟨y,
              mul_right_cancel₀ hp.1 <| by
                rw [tsub_add_cancel_of_le (succ_le_of_lt hm0)] at hy <;>
                  simp [hy, pow_add, mul_comm, mul_assoc, mul_left_comm]⟩)
      finite_mul_aux ha hpx
        ⟨s,
          mul_right_cancel₀ hp.1
            (by
              rw [add_assoc, tsub_add_cancel_of_le (succ_le_of_lt hm0)]
              clear _fun_match _fun_match finite_mul_aux
              simp_all [mul_comm, mul_assoc, mul_left_comm, pow_add])⟩
#align multiplicity.finite_mul_aux multiplicity.finite_mul_aux

theorem finite_mul {p a b : α} (hp : Prime p) : Finite p a → Finite p b → Finite p (a * b) :=
  fun ⟨n, hn⟩ ⟨m, hm⟩ => ⟨n + m, finite_mul_aux hp hn hm⟩
#align multiplicity.finite_mul multiplicity.finite_mul

theorem finite_mul_iff {p a b : α} (hp : Prime p) : Finite p (a * b) ↔ Finite p a ∧ Finite p b :=
  ⟨fun h => ⟨finite_of_finite_mul_right h, finite_of_finite_mul_left h⟩, fun h =>
    finite_mul hp h.1 h.2⟩
#align multiplicity.finite_mul_iff multiplicity.finite_mul_iff

theorem finite_pow {p a : α} (hp : Prime p) : ∀ {k : ℕ} (ha : Finite p a), Finite p (a ^ k)
  | 0, ha => ⟨0, by simp [mt isUnit_iff_dvd_one.2 hp.2.1]⟩
  | k + 1, ha => by rw [pow_succ] <;> exact finite_mul hp ha (finite_pow ha)
#align multiplicity.finite_pow multiplicity.finite_pow

variable [DecidableRel ((· ∣ ·) : α → α → Prop)]

@[simp]
theorem multiplicity_self {a : α} (ha : ¬IsUnit a) (ha0 : a ≠ 0) : multiplicity a a = 1 :=
  by
  rw [← Nat.cast_one]
  exact
    eq_coe_iff.2
      ⟨by simp, fun ⟨b, hb⟩ =>
        ha
          (isUnit_iff_dvd_one.2
            ⟨b,
              mul_left_cancel₀ ha0 <| by
                clear _fun_match
                simpa [pow_succ, mul_assoc] using hb⟩)⟩
#align multiplicity.multiplicity_self multiplicity.multiplicity_self

@[simp]
theorem get_multiplicity_self {a : α} (ha : Finite a a) : get (multiplicity a a) ha = 1 :=
  PartEnat.get_eq_iff_eq_coe.2
    (eq_coe_iff.2
      ⟨by simp, fun ⟨b, hb⟩ => by
        rw [← mul_one a, pow_add, pow_one, mul_assoc, mul_assoc,
            mul_right_inj' (ne_zero_of_finite ha)] at hb <;>
          exact
            mt isUnit_iff_dvd_one.2 (not_unit_of_finite ha) ⟨b, by clear _fun_match <;> simp_all⟩⟩)
#align multiplicity.get_multiplicity_self multiplicity.get_multiplicity_self

protected theorem mul' {p a b : α} (hp : Prime p) (h : (multiplicity p (a * b)).Dom) :
    get (multiplicity p (a * b)) h =
      get (multiplicity p a) ((finite_mul_iff hp).1 h).1 +
        get (multiplicity p b) ((finite_mul_iff hp).1 h).2 :=
  by
  have hdiva : p ^ get (multiplicity p a) ((finite_mul_iff hp).1 h).1 ∣ a := pow_multiplicity_dvd _
  have hdivb : p ^ get (multiplicity p b) ((finite_mul_iff hp).1 h).2 ∣ b := pow_multiplicity_dvd _
  have hpoweq :
    p ^
        (get (multiplicity p a) ((finite_mul_iff hp).1 h).1 +
          get (multiplicity p b) ((finite_mul_iff hp).1 h).2) =
      p ^ get (multiplicity p a) ((finite_mul_iff hp).1 h).1 *
        p ^ get (multiplicity p b) ((finite_mul_iff hp).1 h).2 :=
    by simp [pow_add]
  have hdiv :
    p ^
        (get (multiplicity p a) ((finite_mul_iff hp).1 h).1 +
          get (multiplicity p b) ((finite_mul_iff hp).1 h).2) ∣
      a * b :=
    by rw [hpoweq] <;> apply mul_dvd_mul <;> assumption
  have hsucc :
    ¬p ^
          (get (multiplicity p a) ((finite_mul_iff hp).1 h).1 +
              get (multiplicity p b) ((finite_mul_iff hp).1 h).2 +
            1) ∣
        a * b :=
    fun h =>
    not_or_of_not (is_greatest' _ (lt_succ_self _)) (is_greatest' _ (lt_succ_self _))
      (_root_.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul hp hdiva hdivb h)
  rw [← PartEnat.coe_inj, PartEnat.coe_get, eq_coe_iff] <;> exact ⟨hdiv, hsucc⟩
#align multiplicity.mul' multiplicity.mul'

open Classical

protected theorem mul {p a b : α} (hp : Prime p) :
    multiplicity p (a * b) = multiplicity p a + multiplicity p b :=
  if h : Finite p a ∧ Finite p b then by
    rw [← PartEnat.coe_get (finite_iff_dom.1 h.1), ← PartEnat.coe_get (finite_iff_dom.1 h.2), ←
        PartEnat.coe_get (finite_iff_dom.1 (finite_mul hp h.1 h.2)), ← Nat.cast_add,
        PartEnat.coe_inj, multiplicity.mul' hp] <;>
      rfl
  else by
    rw [eq_top_iff_not_finite.2 (mt (finite_mul_iff hp).1 h)]
    cases' not_and_or.1 h with h h <;> simp [eq_top_iff_not_finite.2 h]
#align multiplicity.mul multiplicity.mul

theorem Finset.prod {β : Type _} {p : α} (hp : Prime p) (s : Finset β) (f : β → α) :
    multiplicity p (∏ x in s, f x) = ∑ x in s, multiplicity p (f x) := by
  classical
    induction' s using Finset.induction with a s has ih h
    · simp only [Finset.sum_empty, Finset.prod_empty]
      convert one_right hp.not_unit
    · simp [has, ← ih]
      convert multiplicity.mul hp
#align multiplicity.finset.prod multiplicity.Finset.prod

protected theorem pow' {p a : α} (hp : Prime p) (ha : Finite p a) :
    ∀ {k : ℕ}, get (multiplicity p (a ^ k)) (finite_pow hp ha) = k * get (multiplicity p a) ha
  | 0 => by simp [one_right hp.not_unit]
  | k + 1 =>
    by
    have : multiplicity p (a ^ (k + 1)) = multiplicity p (a * a ^ k) := by rw [pow_succ]
    rw [get_eq_get_of_eq _ _ this, multiplicity.mul' hp, pow', add_mul, one_mul, add_comm]
#align multiplicity.pow' multiplicity.pow'

theorem pow {p a : α} (hp : Prime p) : ∀ {k : ℕ}, multiplicity p (a ^ k) = k • multiplicity p a
  | 0 => by simp [one_right hp.not_unit]
  | succ k => by simp [pow_succ, succ_nsmul, pow, multiplicity.mul hp]
#align multiplicity.pow multiplicity.pow

theorem multiplicity_pow_self {p : α} (h0 : p ≠ 0) (hu : ¬IsUnit p) (n : ℕ) :
    multiplicity p (p ^ n) = n := by
  rw [eq_coe_iff]
  use dvd_rfl
  rw [pow_dvd_pow_iff h0 hu]
  apply Nat.not_succ_le_self
#align multiplicity.multiplicity_pow_self multiplicity.multiplicity_pow_self

theorem multiplicity_pow_self_of_prime {p : α} (hp : Prime p) (n : ℕ) :
    multiplicity p (p ^ n) = n :=
  multiplicity_pow_self hp.NeZero hp.not_unit n
#align multiplicity.multiplicity_pow_self_of_prime multiplicity.multiplicity_pow_self_of_prime

end CancelCommMonoidWithZero

section Valuation

variable {R : Type _} [CommRing R] [IsDomain R] {p : R} [DecidableRel (Dvd.Dvd : R → R → Prop)]

/-- `multiplicity` of a prime inan integral domain as an additive valuation to `part_enat`. -/
noncomputable def addValuation (hp : Prime p) : AddValuation R PartEnat :=
  AddValuation.of (multiplicity p) (multiplicity.zero _) (one_right hp.not_unit)
    (fun _ _ => min_le_multiplicity_add) fun a b => multiplicity.mul hp
#align multiplicity.add_valuation multiplicity.addValuation

@[simp]
theorem add_valuation_apply {hp : Prime p} {r : R} : addValuation hp r = multiplicity p r :=
  rfl
#align multiplicity.add_valuation_apply multiplicity.add_valuation_apply

end Valuation

end multiplicity

section Nat

open multiplicity

theorem multiplicity_eq_zero_of_coprime {p a b : ℕ} (hp : p ≠ 1)
    (hle : multiplicity p a ≤ multiplicity p b) (hab : Nat.Coprime a b) : multiplicity p a = 0 :=
  by
  rw [multiplicity_le_multiplicity_iff] at hle
  rw [← nonpos_iff_eq_zero, ← not_lt, PartEnat.pos_iff_one_le, ← Nat.cast_one, ←
    pow_dvd_iff_le_multiplicity]
  intro h
  have := Nat.dvd_gcd h (hle _ h)
  rw [coprime.gcd_eq_one hab, Nat.dvd_one, pow_one] at this
  exact hp this
#align multiplicity_eq_zero_of_coprime multiplicity_eq_zero_of_coprime

end Nat

