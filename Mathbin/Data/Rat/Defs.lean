/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.rat.defs
! leanprover-community/mathlib commit d4f69d96f3532729da8ebb763f4bc26fcf640f06
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Rat.Init
import Mathbin.Data.Int.Cast.Defs
import Mathbin.Data.Int.Dvd.Basic
import Mathbin.Algebra.Ring.Regular
import Mathbin.Data.Nat.Gcd.Basic
import Mathbin.Data.Pnat.Defs

/-!
# Basics for the Rational Numbers

## Summary

We define the integral domain structure on `ℚ` and prove basic lemmas about it.
The definition of the field structure on `ℚ` will be done in `data.rat.basic` once the
`field` class has been defined.

## Main Definitions

- `rat.mk n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notations

- `/.` is infix notation for `rat.mk`.

-/


namespace Rat

#print Rat.ofInt /-
/-- Embed an integer as a rational number. You should use the coercion `coe : ℤ → ℚ` instead. -/
def ofInt (n : ℤ) : ℚ :=
  ⟨n, 1, Nat.one_pos, Nat.coprime_one_right _⟩
#align rat.of_int Rat.ofInt
-/

instance : IntCast ℚ :=
  ⟨ofInt⟩

@[simp]
theorem of_int_eq_cast (n : ℤ) : ofInt n = n :=
  rfl
#align rat.of_int_eq_cast Rat.of_int_eq_cast

@[simp, norm_cast]
theorem coe_int_num (n : ℤ) : (n : ℚ).num = n :=
  rfl
#align rat.coe_int_num Rat.coe_int_num

@[simp, norm_cast]
theorem coe_int_denom (n : ℤ) : (n : ℚ).denom = 1 :=
  rfl
#align rat.coe_int_denom Rat.coe_int_denom

instance : Zero ℚ :=
  ⟨(0 : ℤ)⟩

instance : One ℚ :=
  ⟨(1 : ℤ)⟩

instance : Inhabited ℚ :=
  ⟨0⟩

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ+` (not necessarily coprime) -/
def mkPnat (n : ℤ) : ℕ+ → ℚ
  | ⟨d, dpos⟩ =>
    let n' := n.natAbs
    let g := n'.gcd d
    ⟨n / g, d / g, by
      apply (Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_right _ dpos)).2
      rw [one_mul]; exact Nat.le_of_dvd dpos (Nat.gcd_dvd_right _ _), by
      have : Int.natAbs (n / ↑g) = n' / g := by
        cases' Int.natAbs_eq n with e e <;> rw [e]
        · rfl
        rw [Int.neg_ediv_of_dvd, Int.natAbs_neg]
        · rfl
        exact Int.coe_nat_dvd.2 (Nat.gcd_dvd_left _ _)
      rw [this]
      exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ dpos)⟩
#align rat.mk_pnat Rat.mkPnat

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ`. In the case `d = 0`, we
  define `n / 0 = 0` by convention. -/
def mkNat (n : ℤ) (d : ℕ) : ℚ :=
  if d0 : d = 0 then 0 else mkPnat n ⟨d, Nat.pos_of_ne_zero d0⟩
#align rat.mk_nat Rat.mkNat

/- warning: rat.mk clashes with rat.mk' -> Rat.mk
warning: rat.mk -> Rat.mk is a dubious translation:
lean 3 declaration is
  Int -> Int -> Rat
but is expected to have type
  forall (ᾰ : Int) (ᾰ_1 : Nat), (autoParam.{0} (Ne.{1} Nat ᾰ_1 (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) _auto._@.Std.Data.Rat.Basic._hyg.4) -> (autoParam.{0} (Nat.coprime (Int.natAbs ᾰ) ᾰ_1) _auto._@.Std.Data.Rat.Basic._hyg.33) -> Rat
Case conversion may be inaccurate. Consider using '#align rat.mk Rat.mkₓ'. -/
/-- Form the quotient `n / d` where `n d : ℤ`. -/
def mk : ℤ → ℤ → ℚ
  | n, (d : ℕ) => mkNat n d
  | n, -[d+1] => mkPnat (-n) d.succPnat
#align rat.mk Rat.mk

-- mathport name: rat.mk
scoped infixl:70 " /. " => Rat.mk

theorem mk_pnat_eq (n d h) : mkPnat n ⟨d, h⟩ = n /. d := by
  change n /. d with dite _ _ _ <;> simp [ne_of_gt h]
#align rat.mk_pnat_eq Rat.mk_pnat_eq

theorem mk_nat_eq (n d) : mkNat n d = n /. d :=
  rfl
#align rat.mk_nat_eq Rat.mk_nat_eq

/- warning: rat.mk_zero -> Rat.mk_zero is a dubious translation:
lean 3 declaration is
  forall (n : Int), Eq.{1} Rat (Rat.mk n (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero)))
but is expected to have type
  forall {n : Nat}, Eq.{1} Rat (mkRat (OfNat.ofNat.{0} Int 0 (instOfNatInt 0)) n) (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0))
Case conversion may be inaccurate. Consider using '#align rat.mk_zero Rat.mk_zeroₓ'. -/
@[simp]
theorem mk_zero (n) : n /. 0 = 0 :=
  rfl
#align rat.mk_zero Rat.mk_zero

@[simp]
theorem zero_mk_pnat (n) : mkPnat 0 n = 0 := by
  cases' n with n npos
  simp only [mk_pnat, Int.natAbs_zero, Nat.div_self npos, Nat.gcd_zero_left, Int.zero_div]
  rfl
#align rat.zero_mk_pnat Rat.zero_mk_pnat

@[simp]
theorem zero_mk_nat (n) : mkNat 0 n = 0 := by by_cases n = 0 <;> simp [*, mk_nat]
#align rat.zero_mk_nat Rat.zero_mk_nat

@[simp]
theorem zero_mk (n) : 0 /. n = 0 := by cases n <;> simp [mk]
#align rat.zero_mk Rat.zero_mk

private theorem gcd_abs_dvd_left {a b} : (Nat.gcd (Int.natAbs a) b : ℤ) ∣ a :=
  Int.dvd_natAbs.1 <| Int.coe_nat_dvd.2 <| Nat.gcd_dvd_left (Int.natAbs a) b
#align rat.gcd_abs_dvd_left rat.gcd_abs_dvd_left

@[simp]
theorem mk_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 := by
  refine'
    ⟨fun h => _, by 
      rintro rfl
      simp⟩
  have : ∀ {a b}, mk_pnat a b = 0 → a = 0 := by
    rintro a ⟨b, h⟩ e
    injection e with e
    apply Int.eq_mul_of_ediv_eq_right gcd_abs_dvd_left e
  cases' b with b <;> simp only [mk, mk_nat, Int.ofNat_eq_coe, dite_eq_left_iff] at h
  · simp only [mt (congr_arg Int.ofNat) b0, not_false_iff, forall_true_left] at h
    exact this h
  · apply neg_injective
    simp [this h]
#align rat.mk_eq_zero Rat.mk_eq_zero

theorem mk_ne_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b ≠ 0 ↔ a ≠ 0 :=
  (mk_eq_zero b0).Not
#align rat.mk_ne_zero Rat.mk_ne_zero

theorem mk_eq : ∀ {a b c d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0), a /. b = c /. d ↔ a * d = c * b := by
  suffices ∀ a b c d hb hd, mkPnat a ⟨b, hb⟩ = mkPnat c ⟨d, hd⟩ ↔ a * d = c * b by
    intros ; cases' b with b b <;> simp [mk, mk_nat, Nat.succPNat]
    simp [mt (congr_arg Int.ofNat) hb]
    all_goals 
      cases' d with d d <;> simp [mk, mk_nat, Nat.succPNat]
      simp [mt (congr_arg Int.ofNat) hd]
      all_goals rw [this]; try rfl
    · change a * ↑d.succ = -c * ↑b ↔ a * -d.succ = c * b
      constructor <;> intro h <;> apply neg_injective <;>
        simpa [left_distrib, neg_add_eq_iff_eq_add, eq_neg_iff_add_eq_zero,
          neg_eq_iff_add_eq_zero] using h
    · change -a * ↑d = c * b.succ ↔ a * d = c * -b.succ
      constructor <;> intro h <;> apply neg_injective <;> simpa [left_distrib, eq_comm] using h
    · change -a * d.succ = -c * b.succ ↔ a * -d.succ = c * -b.succ
      simp [left_distrib, sub_eq_add_neg]
      cc
  intros ; simp [mk_pnat]; constructor <;> intro h
  · cases' h with ha hb
    have ha := by 
      have dv := @gcd_abs_dvd_left
      have := Int.eq_mul_of_ediv_eq_right dv ha
      rw [← Int.mul_ediv_assoc _ dv] at this
      exact Int.eq_mul_of_ediv_eq_left (dv.mul_left _) this.symm
    have hb := by 
      have dv := fun {a b} => Nat.gcd_dvd_right (Int.natAbs a) b
      have := Nat.eq_mul_of_div_eq_right dv hb
      rw [← Nat.mul_div_assoc _ dv] at this
      exact Nat.eq_mul_of_div_eq_left (dv.mul_left _) this.symm
    have m0 : (a.nat_abs.gcd b * c.nat_abs.gcd d : ℤ) ≠ 0 := by
      refine' Int.coe_nat_ne_zero.2 (ne_of_gt _)
      apply mul_pos <;> apply Nat.gcd_pos_of_pos_right <;> assumption
    apply mul_right_cancel₀ m0
    simpa [mul_comm, mul_left_comm] using congr (congr_arg (· * ·) ha.symm) (congr_arg coe hb)
  · suffices ∀ a c, a * d = c * b → a / a.gcd b = c / c.gcd d ∧ b / a.gcd b = d / c.gcd d by
      cases' this a.nat_abs c.nat_abs (by simpa [Int.natAbs_mul] using congr_arg Int.natAbs h) with
        h₁ h₂
      have hs := congr_arg Int.sign h
      simp [Int.sign_eq_one_of_pos (Int.ofNat_lt.2 hb),
        Int.sign_eq_one_of_pos (Int.ofNat_lt.2 hd)] at hs
      conv in a => rw [← Int.sign_mul_natAbs a]
      conv in c => rw [← Int.sign_mul_natAbs c]
      rw [Int.mul_ediv_assoc, Int.mul_ediv_assoc]
      exact ⟨congr (congr_arg (· * ·) hs) (congr_arg coe h₁), h₂⟩
      all_goals exact Int.coe_nat_dvd.2 (Nat.gcd_dvd_left _ _)
    intro a c h
    suffices bd : b / a.gcd b = d / c.gcd d
    · refine' ⟨_, bd⟩
      apply Nat.eq_of_mul_eq_mul_left hb
      rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _), mul_comm,
        Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), bd, ←
        Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), h, mul_comm,
        Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _)]
    suffices ∀ {a c : ℕ}, ∀ b > 0, ∀ d > 0, a * d = c * b → b / a.gcd b ≤ d / c.gcd d by
      exact le_antisymm (this _ hb _ hd h) (this _ hd _ hb h.symm)
    intro a c b hb d hd h
    have gb0 := Nat.gcd_pos_of_pos_right a hb
    have gd0 := Nat.gcd_pos_of_pos_right c hd
    apply Nat.le_of_dvd
    apply (Nat.le_div_iff_mul_le gd0).2
    simp
    apply Nat.le_of_dvd hd (Nat.gcd_dvd_right _ _)
    apply (Nat.coprime_div_gcd_div_gcd gb0).symm.dvd_of_dvd_mul_left
    refine' ⟨c / c.gcd d, _⟩
    rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _), ← Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]
    apply congr_arg (· / c.gcd d)
    rw [mul_comm, ← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _), mul_comm, h,
      Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), mul_comm]
#align rat.mk_eq Rat.mk_eq

@[simp]
theorem div_mk_div_cancel_left {a b c : ℤ} (c0 : c ≠ 0) : a * c /. (b * c) = a /. b := by
  by_cases b0 : b = 0;
  · subst b0
    simp
  apply (mk_eq (mul_ne_zero b0 c0) b0).2; simp [mul_comm, mul_assoc]
#align rat.div_mk_div_cancel_left Rat.div_mk_div_cancel_left

@[simp]
theorem num_denom : ∀ {a : ℚ}, a.num /. a.denom = a
  | ⟨n, d, h, (c : _ = 1)⟩ => show mkNat n d = _ by simp [mk_nat, ne_of_gt h, mk_pnat, c]
#align rat.num_denom Rat.num_denom

theorem num_denom' {n d h c} : (⟨n, d, h, c⟩ : ℚ) = n /. d :=
  num_denom.symm
#align rat.num_denom' Rat.num_denom'

theorem coe_int_eq_mk (z : ℤ) : (z : ℚ) = z /. 1 :=
  num_denom'
#align rat.coe_int_eq_mk Rat.coe_int_eq_mk

/- warning: rat.num_denom_cases_on -> Rat.numDenomCasesOn is a dubious translation:
lean 3 declaration is
  forall {C : Rat -> Sort.{u1}} (a : Rat), (forall (n : Int) (d : Nat), (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) d) -> (Nat.Coprime (Int.natAbs n) d) -> (C (Rat.mk n ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (CoeTCₓ.mk.{1, 1} Nat Int Int.ofNat))) d)))) -> (C a)
but is expected to have type
  PUnit.{imax (succ u1) 1 (imax 1 1 u1) u1}
Case conversion may be inaccurate. Consider using '#align rat.num_denom_cases_on Rat.numDenomCasesOnₓ'. -/
/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `0 < d` and coprime `n`, `d`. -/
@[elab_as_elim]
def numDenomCasesOn.{u} {C : ℚ → Sort u} :
    ∀ (a : ℚ) (H : ∀ n d, 0 < d → (Int.natAbs n).Coprime d → C (n /. d)), C a
  | ⟨n, d, h, c⟩, H => by rw [num_denom'] <;> exact H n d h c
#align rat.num_denom_cases_on Rat.numDenomCasesOn

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `d ≠ 0`. -/
@[elab_as_elim]
def numDenomCasesOn'.{u} {C : ℚ → Sort u} (a : ℚ) (H : ∀ (n : ℤ) (d : ℕ), d ≠ 0 → C (n /. d)) :
    C a :=
  (numDenomCasesOn a) fun n d h c => H n d h.ne'
#align rat.num_denom_cases_on' Rat.numDenomCasesOn'

#print Rat.add /-
/-- Addition of rational numbers. Use `(+)` instead. -/
protected def add : ℚ → ℚ → ℚ
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => mkPnat (n₁ * d₂ + n₂ * d₁) ⟨d₁ * d₂, mul_pos h₁ h₂⟩
#align rat.add Rat.add
-/

instance : Add ℚ :=
  ⟨Rat.add⟩

theorem lift_binop_eq (f : ℚ → ℚ → ℚ) (f₁ : ℤ → ℤ → ℤ → ℤ → ℤ) (f₂ : ℤ → ℤ → ℤ → ℤ → ℤ)
    (fv :
      ∀ {n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂},
        f ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ = f₁ n₁ d₁ n₂ d₂ /. f₂ n₁ d₁ n₂ d₂)
    (f0 : ∀ {n₁ d₁ n₂ d₂} (d₁0 : d₁ ≠ 0) (d₂0 : d₂ ≠ 0), f₂ n₁ d₁ n₂ d₂ ≠ 0) (a b c d : ℤ)
    (b0 : b ≠ 0) (d0 : d ≠ 0)
    (H :
      ∀ {n₁ d₁ n₂ d₂} (h₁ : a * d₁ = n₁ * b) (h₂ : c * d₂ = n₂ * d),
        f₁ n₁ d₁ n₂ d₂ * f₂ a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂) :
    f (a /. b) (c /. d) = f₁ a b c d /. f₂ a b c d := by
  generalize ha : a /. b = x; cases' x with n₁ d₁ h₁ c₁; rw [num_denom'] at ha
  generalize hc : c /. d = x; cases' x with n₂ d₂ h₂ c₂; rw [num_denom'] at hc
  rw [fv]
  have d₁0 := ne_of_gt (Int.ofNat_lt.2 h₁)
  have d₂0 := ne_of_gt (Int.ofNat_lt.2 h₂)
  exact (mk_eq (f0 d₁0 d₂0) (f0 b0 d0)).2 (H ((mk_eq b0 d₁0).1 ha) ((mk_eq d0 d₂0).1 hc))
#align rat.lift_binop_eq Rat.lift_binop_eq

@[simp]
theorem add_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
    a /. b + c /. d = (a * d + c * b) /. (b * d) := by
  apply lift_binop_eq Rat.add <;> intros <;> try assumption
  · apply mk_pnat_eq
  · apply mul_ne_zero d₁0 d₂0
  calc
    (n₁ * d₂ + n₂ * d₁) * (b * d) = n₁ * b * d₂ * d + n₂ * d * (d₁ * b) := by
      simp [mul_add, mul_comm, mul_left_comm]
    _ = a * d₁ * d₂ * d + c * d₂ * (d₁ * b) := by rw [h₁, h₂]
    _ = (a * d + c * b) * (d₁ * d₂) := by simp [mul_add, mul_comm, mul_left_comm]
    
#align rat.add_def Rat.add_def

#print Rat.neg /-
/-- Negation of rational numbers. Use `-r` instead. -/
protected def neg (r : ℚ) : ℚ :=
  ⟨-r.num, r.denom, r.Pos, by simp [r.cop]⟩
#align rat.neg Rat.neg
-/

instance : Neg ℚ :=
  ⟨Rat.neg⟩

@[simp]
theorem neg_def {a b : ℤ} : -(a /. b) = -a /. b := by
  by_cases b0 : b = 0;
  · subst b0
    simp
    rfl
  generalize ha : a /. b = x; cases' x with n₁ d₁ h₁ c₁; rw [num_denom'] at ha
  show Rat.mk _ _ _ _ = _; rw [num_denom']
  have d0 := ne_of_gt (Int.ofNat_lt.2 h₁)
  apply (mk_eq d0 b0).2; have h₁ := (mk_eq b0 d0).1 ha
  simp only [neg_mul, congr_arg Neg.neg h₁]
#align rat.neg_def Rat.neg_def

@[simp]
theorem mk_neg_denom (n d : ℤ) : n /. -d = -n /. d := by
  by_cases hd : d = 0 <;> simp [Rat.mk_eq, hd]
#align rat.mk_neg_denom Rat.mk_neg_denom

#print Rat.mul /-
/-- Multiplication of rational numbers. Use `(*)` instead. -/
protected def mul : ℚ → ℚ → ℚ
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => mkPnat (n₁ * n₂) ⟨d₁ * d₂, mul_pos h₁ h₂⟩
#align rat.mul Rat.mul
-/

instance : Mul ℚ :=
  ⟨Rat.mul⟩

@[simp]
theorem mul_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) : a /. b * (c /. d) = a * c /. (b * d) := by
  apply lift_binop_eq Rat.mul <;> intros <;> try assumption
  · apply mk_pnat_eq
  · apply mul_ne_zero d₁0 d₂0
  cc
#align rat.mul_def Rat.mul_def

#print Rat.inv /-
/-- Inverse rational number. Use `r⁻¹` instead. -/
protected def inv : ℚ → ℚ
  | ⟨(n + 1 : ℕ), d, h, c⟩ => ⟨d, n + 1, n.succ_pos, c.symm⟩
  | ⟨0, d, h, c⟩ => 0
  | ⟨-[n+1], d, h, c⟩ => ⟨-d, n + 1, n.succ_pos, Nat.Coprime.symm <| by simp <;> exact c⟩
#align rat.inv Rat.inv
-/

instance : Inv ℚ :=
  ⟨Rat.inv⟩

instance : Div ℚ :=
  ⟨fun a b => a * b⁻¹⟩

@[simp]
theorem inv_def {a b : ℤ} : (a /. b)⁻¹ = b /. a := by
  by_cases a0 : a = 0
  · subst a0
    simp
    rfl
  by_cases b0 : b = 0
  · subst b0
    simp
    rfl
  generalize ha : a /. b = x
  cases' x with n d h c
  rw [num_denom'] at ha
  refine' Eq.trans (_ : Rat.inv ⟨n, d, h, c⟩ = d /. n) _
  · cases' n with n <;> [cases' n with n, skip]
    · rfl
    · change Int.ofNat n.succ with (n + 1 : ℕ)
      unfold Rat.inv
      rw [num_denom']
    · unfold Rat.inv
      rw [num_denom']
      rfl
  have n0 : n ≠ 0 := by 
    rintro rfl
    rw [Rat.zero_mk, mk_eq_zero b0] at ha
    exact a0 ha
  have d0 := ne_of_gt (Int.ofNat_lt.2 h)
  have ha := (mk_eq b0 d0).1 ha
  apply (mk_eq n0 a0).2
  cc
#align rat.inv_def Rat.inv_def

variable (a b c : ℚ)

protected theorem add_zero : a + 0 = a :=
  (numDenomCasesOn' a) fun n d h => by rw [← zero_mk d] <;> simp [h, -zero_mk]
#align rat.add_zero Rat.add_zero

protected theorem zero_add : 0 + a = a :=
  (numDenomCasesOn' a) fun n d h => by rw [← zero_mk d] <;> simp [h, -zero_mk]
#align rat.zero_add Rat.zero_add

protected theorem add_comm : a + b = b + a :=
  (numDenomCasesOn' a) fun n₁ d₁ h₁ => (numDenomCasesOn' b) fun n₂ d₂ h₂ => by simp [h₁, h₂] <;> cc
#align rat.add_comm Rat.add_comm

protected theorem add_assoc : a + b + c = a + (b + c) :=
  (numDenomCasesOn' a) fun n₁ d₁ h₁ =>
    (numDenomCasesOn' b) fun n₂ d₂ h₂ =>
      (numDenomCasesOn' c) fun n₃ d₃ h₃ => by
        simp [h₁, h₂, h₃, mul_ne_zero, mul_add, mul_comm, mul_left_comm, add_left_comm, add_assoc]
#align rat.add_assoc Rat.add_assoc

protected theorem add_left_neg : -a + a = 0 :=
  (numDenomCasesOn' a) fun n d h => by simp [h]
#align rat.add_left_neg Rat.add_left_neg

@[simp]
theorem mk_zero_one : 0 /. 1 = 0 :=
  show mkPnat _ _ = _ by 
    rw [mk_pnat]
    simp
    rfl
#align rat.mk_zero_one Rat.mk_zero_one

@[simp]
theorem mk_one_one : 1 /. 1 = 1 :=
  show mkPnat _ _ = _ by 
    rw [mk_pnat]
    simp
    rfl
#align rat.mk_one_one Rat.mk_one_one

@[simp]
theorem mk_neg_one_one : -1 /. 1 = -1 :=
  show mkPnat _ _ = _ by 
    rw [mk_pnat]
    simp
    rfl
#align rat.mk_neg_one_one Rat.mk_neg_one_one

protected theorem mul_one : a * 1 = a :=
  (numDenomCasesOn' a) fun n d h => by 
    rw [← mk_one_one]
    simp [h, -mk_one_one]
#align rat.mul_one Rat.mul_one

protected theorem one_mul : 1 * a = a :=
  (numDenomCasesOn' a) fun n d h => by 
    rw [← mk_one_one]
    simp [h, -mk_one_one]
#align rat.one_mul Rat.one_mul

protected theorem mul_comm : a * b = b * a :=
  (numDenomCasesOn' a) fun n₁ d₁ h₁ =>
    (numDenomCasesOn' b) fun n₂ d₂ h₂ => by simp [h₁, h₂, mul_comm]
#align rat.mul_comm Rat.mul_comm

protected theorem mul_assoc : a * b * c = a * (b * c) :=
  (numDenomCasesOn' a) fun n₁ d₁ h₁ =>
    (numDenomCasesOn' b) fun n₂ d₂ h₂ =>
      (numDenomCasesOn' c) fun n₃ d₃ h₃ => by
        simp [h₁, h₂, h₃, mul_ne_zero, mul_comm, mul_left_comm]
#align rat.mul_assoc Rat.mul_assoc

protected theorem add_mul : (a + b) * c = a * c + b * c :=
  (numDenomCasesOn' a) fun n₁ d₁ h₁ =>
    (numDenomCasesOn' b) fun n₂ d₂ h₂ =>
      (numDenomCasesOn' c) fun n₃ d₃ h₃ => by
        simp [h₁, h₂, h₃, mul_ne_zero] <;>
            refine' (div_mk_div_cancel_left (Int.coe_nat_ne_zero.2 h₃)).symm.trans _ <;>
          simp [mul_add, mul_comm, mul_assoc, mul_left_comm]
#align rat.add_mul Rat.add_mul

protected theorem mul_add : a * (b + c) = a * b + a * c := by
  rw [Rat.mul_comm, Rat.add_mul, Rat.mul_comm, Rat.mul_comm c a]
#align rat.mul_add Rat.mul_add

protected theorem zero_ne_one : 0 ≠ (1 : ℚ) := by
  rw [ne_comm, ← mk_one_one, mk_ne_zero one_ne_zero]
  exact one_ne_zero
#align rat.zero_ne_one Rat.zero_ne_one

protected theorem mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1 :=
  (numDenomCasesOn' a) fun n d h a0 => by
    have n0 : n ≠ 0 :=
      mt
        (by 
          rintro rfl
          simp)
        a0
    simpa [h, n0, mul_comm] using @div_mk_div_cancel_left 1 1 _ n0
#align rat.mul_inv_cancel Rat.mul_inv_cancel

protected theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
  Eq.trans (Rat.mul_comm _ _) (Rat.mul_inv_cancel _ h)
#align rat.inv_mul_cancel Rat.inv_mul_cancel

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.mk_dec_eq_instance -/
instance : DecidableEq ℚ := by
  run_tac
    tactic.mk_dec_eq_instance

/-! At this point in the import hierarchy we have not defined the `field` typeclass.
Instead we'll instantiate `comm_ring` and `comm_group_with_zero` at this point.
The `rat.field` instance and any field-specific lemmas can be found in `data.rat.basic`.
-/


instance : CommRing ℚ where 
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  one := 1
  mul := (· * ·)
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  add_left_neg := Rat.add_left_neg
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  left_distrib := Rat.mul_add
  right_distrib := Rat.add_mul
  intCast := coe
  /- Important: We do not set `nat_cast := λ n, ((n : ℤ) : ℚ)` (even though it's defeq) as that
    makes `int.cast_coe_nat` and `coe_coe` loop in `simp`. -/
  natCast n := ofInt n
  nat_cast_zero := rfl
  nat_cast_succ n := by
    simp only [of_int_eq_cast, coe_int_eq_mk, add_def one_ne_zero one_ne_zero, ← mk_one_one,
      Nat.cast_add, Nat.cast_one, mul_one]

instance : CommGroupWithZero ℚ :=
  { Rat.commRing with 
    zero := 0
    one := 1
    mul := (· * ·)
    inv := Inv.inv
    div := (· / ·)
    exists_pair_ne := ⟨0, 1, Rat.zero_ne_one⟩
    inv_zero := rfl
    mul_inv_cancel := Rat.mul_inv_cancel
    mul_zero := mul_zero
    zero_mul := zero_mul }

instance : IsDomain ℚ :=
  NoZeroDivisors.toIsDomain _

-- Extra instances to short-circuit type class resolution 
-- TODO(Mario): this instance slows down data.real.basic
instance : Nontrivial ℚ := by infer_instance

--instance : ring ℚ             := by apply_instance
instance : CommSemiring ℚ := by infer_instance

instance : Semiring ℚ := by infer_instance

instance : AddCommGroup ℚ := by infer_instance

instance : AddGroup ℚ := by infer_instance

instance : AddCommMonoid ℚ := by infer_instance

instance : AddMonoid ℚ := by infer_instance

instance : AddLeftCancelSemigroup ℚ := by infer_instance

instance : AddRightCancelSemigroup ℚ := by infer_instance

instance : AddCommSemigroup ℚ := by infer_instance

instance : AddSemigroup ℚ := by infer_instance

instance : CommMonoid ℚ := by infer_instance

instance : Monoid ℚ := by infer_instance

instance : CommSemigroup ℚ := by infer_instance

instance : Semigroup ℚ := by infer_instance

theorem denom_ne_zero (q : ℚ) : q.denom ≠ 0 :=
  ne_of_gt q.Pos
#align rat.denom_ne_zero Rat.denom_ne_zero

theorem eq_iff_mul_eq_mul {p q : ℚ} : p = q ↔ p.num * q.denom = q.num * p.denom := by
  conv => 
    lhs
    rw [← @num_denom p, ← @num_denom q]
  apply Rat.mk_eq <;>
    · rw [← Nat.cast_zero, Ne, Int.ofNat_inj]
      apply denom_ne_zero
#align rat.eq_iff_mul_eq_mul Rat.eq_iff_mul_eq_mul

theorem sub_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
    a /. b - c /. d = (a * d - c * b) /. (b * d) := by simp [b0, d0, sub_eq_add_neg]
#align rat.sub_def Rat.sub_def

@[simp]
theorem denom_neg_eq_denom (q : ℚ) : (-q).denom = q.denom :=
  rfl
#align rat.denom_neg_eq_denom Rat.denom_neg_eq_denom

@[simp]
theorem num_neg_eq_neg_num (q : ℚ) : (-q).num = -q.num :=
  rfl
#align rat.num_neg_eq_neg_num Rat.num_neg_eq_neg_num

@[simp]
theorem num_zero : Rat.num 0 = 0 :=
  rfl
#align rat.num_zero Rat.num_zero

@[simp]
theorem denom_zero : Rat.den 0 = 1 :=
  rfl
#align rat.denom_zero Rat.denom_zero

theorem zero_of_num_zero {q : ℚ} (hq : q.num = 0) : q = 0 := by
  have : q = q.num /. q.denom := num_denom.symm
  simpa [hq]
#align rat.zero_of_num_zero Rat.zero_of_num_zero

theorem zero_iff_num_zero {q : ℚ} : q = 0 ↔ q.num = 0 :=
  ⟨fun _ => by simp [*], zero_of_num_zero⟩
#align rat.zero_iff_num_zero Rat.zero_iff_num_zero

theorem num_ne_zero_of_ne_zero {q : ℚ} (h : q ≠ 0) : q.num ≠ 0 := fun this : q.num = 0 =>
  h <| zero_of_num_zero this
#align rat.num_ne_zero_of_ne_zero Rat.num_ne_zero_of_ne_zero

@[simp]
theorem num_one : (1 : ℚ).num = 1 :=
  rfl
#align rat.num_one Rat.num_one

@[simp]
theorem denom_one : (1 : ℚ).denom = 1 :=
  rfl
#align rat.denom_one Rat.denom_one

theorem mk_num_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : n ≠ 0 :=
  fun this : n = 0 => hq <| by simpa [this] using hqnd
#align rat.mk_num_ne_zero_of_ne_zero Rat.mk_num_ne_zero_of_ne_zero

theorem mk_denom_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : d ≠ 0 :=
  fun this : d = 0 => hq <| by simpa [this] using hqnd
#align rat.mk_denom_ne_zero_of_ne_zero Rat.mk_denom_ne_zero_of_ne_zero

theorem mk_ne_zero_of_ne_zero {n d : ℤ} (h : n ≠ 0) (hd : d ≠ 0) : n /. d ≠ 0 :=
  (mk_ne_zero hd).mpr h
#align rat.mk_ne_zero_of_ne_zero Rat.mk_ne_zero_of_ne_zero

theorem mul_num_denom (q r : ℚ) : q * r = q.num * r.num /. ↑(q.denom * r.denom) := by
  have hq' : (↑q.denom : ℤ) ≠ 0 := by have := denom_ne_zero q <;> simpa
  have hr' : (↑r.denom : ℤ) ≠ 0 := by have := denom_ne_zero r <;> simpa
  suffices q.num /. ↑q.denom * (r.num /. ↑r.denom) = q.num * r.num /. ↑(q.denom * r.denom) by
    simpa using this
  simp [mul_def hq' hr', -num_denom]
#align rat.mul_num_denom Rat.mul_num_denom

theorem div_num_denom (q r : ℚ) : q / r = q.num * r.denom /. (q.denom * r.num) :=
  if hr : r.num = 0 then by 
    have hr' : r = 0 := zero_of_num_zero hr
    simp [*]
  else
    calc
      q / r = q * r⁻¹ := div_eq_mul_inv q r
      _ = q.num /. q.denom * (r.num /. r.denom)⁻¹ := by simp
      _ = q.num /. q.denom * (r.denom /. r.num) := by rw [inv_def]
      _ = q.num * r.denom /. (q.denom * r.num) := mul_def (by simpa using denom_ne_zero q) hr
      
#align rat.div_num_denom Rat.div_num_denom

section Casts

protected theorem add_mk (a b c : ℤ) : (a + b) /. c = a /. c + b /. c :=
  if h : c = 0 then by simp [h]
  else by 
    rw [add_def h h, mk_eq h (mul_ne_zero h h)]
    simp [add_mul, mul_assoc]
#align rat.add_mk Rat.add_mk

theorem mk_eq_div (n d : ℤ) : n /. d = (n : ℚ) / d := by
  by_cases d0 : d = 0; · simp [d0, div_zero]
  simp [division_def, coe_int_eq_mk, mul_def one_ne_zero d0]
#align rat.mk_eq_div Rat.mk_eq_div

theorem mk_mul_mk_cancel {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : n /. x * (x /. d) = n /. d := by
  by_cases hd : d = 0
  · rw [hd]
    simp
  rw [mul_def hx hd, mul_comm x, div_mk_div_cancel_left hx]
#align rat.mk_mul_mk_cancel Rat.mk_mul_mk_cancel

theorem mk_div_mk_cancel_left {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : n /. x / (d /. x) = n /. d := by
  rw [div_eq_mul_inv, inv_def, mk_mul_mk_cancel hx]
#align rat.mk_div_mk_cancel_left Rat.mk_div_mk_cancel_left

theorem mk_div_mk_cancel_right {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : x /. n / (x /. d) = d /. n := by
  rw [div_eq_mul_inv, inv_def, mul_comm, mk_mul_mk_cancel hx]
#align rat.mk_div_mk_cancel_right Rat.mk_div_mk_cancel_right

theorem coe_int_div_eq_mk {n d : ℤ} : (n : ℚ) / ↑d = n /. d := by
  repeat' rw [coe_int_eq_mk]
  exact mk_div_mk_cancel_left one_ne_zero n d
#align rat.coe_int_div_eq_mk Rat.coe_int_div_eq_mk

@[simp]
theorem num_div_denom (r : ℚ) : (r.num / r.denom : ℚ) = r := by
  rw [← Int.cast_ofNat, ← mk_eq_div, num_denom]
#align rat.num_div_denom Rat.num_div_denom

theorem coe_int_num_of_denom_eq_one {q : ℚ} (hq : q.denom = 1) : ↑q.num = q := by
  conv_rhs => rw [← @num_denom q, hq]
  rw [coe_int_eq_mk]
  rfl
#align rat.coe_int_num_of_denom_eq_one Rat.coe_int_num_of_denom_eq_one

theorem denom_eq_one_iff (r : ℚ) : r.denom = 1 ↔ ↑r.num = r :=
  ⟨Rat.coe_int_num_of_denom_eq_one, fun h => h ▸ Rat.coe_int_denom r.num⟩
#align rat.denom_eq_one_iff Rat.denom_eq_one_iff

instance canLift : CanLift ℚ ℤ coe fun q => q.denom = 1 :=
  ⟨fun q hq => ⟨q.num, coe_int_num_of_denom_eq_one hq⟩⟩
#align rat.can_lift Rat.canLift

theorem coe_nat_eq_mk (n : ℕ) : ↑n = n /. 1 := by rw [← Int.cast_ofNat, coe_int_eq_mk]
#align rat.coe_nat_eq_mk Rat.coe_nat_eq_mk

@[simp, norm_cast]
theorem coe_nat_num (n : ℕ) : (n : ℚ).num = n := by rw [← Int.cast_ofNat, coe_int_num]
#align rat.coe_nat_num Rat.coe_nat_num

@[simp, norm_cast]
theorem coe_nat_denom (n : ℕ) : (n : ℚ).denom = 1 := by rw [← Int.cast_ofNat, coe_int_denom]
#align rat.coe_nat_denom Rat.coe_nat_denom

-- Will be subsumed by `int.coe_inj` after we have defined
-- `linear_ordered_field ℚ` (which implies characteristic zero).
theorem coe_int_inj (m n : ℤ) : (m : ℚ) = n ↔ m = n :=
  ⟨congr_arg num, congr_arg _⟩
#align rat.coe_int_inj Rat.coe_int_inj

end Casts

end Rat

-- Guard against import creep.
assert_not_exists Field

