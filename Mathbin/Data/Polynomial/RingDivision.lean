/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker, Johan Commelin

! This file was ported from Lean 3 source module data.polynomial.ring_division
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharZero.Infinite
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.Data.Polynomial.Degree.Lemmas
import Mathbin.Data.Polynomial.Div
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.Algebra.Polynomial.BigOperators

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $ R[X] $

## Main definitions

* `polynomial.roots p`: The multiset containing all the roots of `p`, including their
  multiplicities.
* `polynomial.root_set p E`: The set of distinct roots of `p` in an algebra `E`.

## Main statements

* `polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C`: If a polynomial has as many roots as its
  degree, it can be written as the product of its leading coefficient with `∏ (X - a)` where `a`
  ranges through its roots.

-/


noncomputable section

open Classical Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R] {p q : R[X]}

section

variable [Semiring S]

theorem nat_degree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S}
    (hz : aeval z p = 0) (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.natDegree :=
  nat_degree_pos_of_eval₂_root hp (algebraMap R S) hz inj
#align polynomial.nat_degree_pos_of_aeval_root Polynomial.nat_degree_pos_of_aeval_root

theorem degree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p ≠ 0) {z : S} (hz : aeval z p = 0)
    (inj : ∀ x : R, algebraMap R S x = 0 → x = 0) : 0 < p.degree :=
  nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_aeval_root hp hz inj)
#align polynomial.degree_pos_of_aeval_root Polynomial.degree_pos_of_aeval_root

theorem mod_by_monic_eq_of_dvd_sub (hq : q.Monic) {p₁ p₂ : R[X]} (h : q ∣ p₁ - p₂) :
    p₁ %ₘ q = p₂ %ₘ q := by
  nontriviality R
  obtain ⟨f, sub_eq⟩ := h
  refine' (div_mod_by_monic_unique (p₂ /ₘ q + f) _ hq ⟨_, degree_mod_by_monic_lt _ hq⟩).2
  rw [sub_eq_iff_eq_add.mp sub_eq, mul_add, ← add_assoc, mod_by_monic_add_div _ hq, add_comm]
#align polynomial.mod_by_monic_eq_of_dvd_sub Polynomial.mod_by_monic_eq_of_dvd_sub

theorem add_mod_by_monic (p₁ p₂ : R[X]) : (p₁ + p₂) %ₘ q = p₁ %ₘ q + p₂ %ₘ q :=
  by
  by_cases hq : q.monic
  · nontriviality R
    exact
      (div_mod_by_monic_unique (p₁ /ₘ q + p₂ /ₘ q) _ hq
          ⟨by
            rw [mul_add, add_left_comm, add_assoc, mod_by_monic_add_div _ hq, ← add_assoc,
              add_comm (q * _), mod_by_monic_add_div _ hq],
            (degree_add_le _ _).trans_lt
              (max_lt (degree_mod_by_monic_lt _ hq) (degree_mod_by_monic_lt _ hq))⟩).2
  · simp_rw [mod_by_monic_eq_of_not_monic _ hq]
#align polynomial.add_mod_by_monic Polynomial.add_mod_by_monic

theorem smul_mod_by_monic (c : R) (p : R[X]) : c • p %ₘ q = c • (p %ₘ q) :=
  by
  by_cases hq : q.monic
  · nontriviality R
    exact
      (div_mod_by_monic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
          ⟨by rw [mul_smul_comm, ← smul_add, mod_by_monic_add_div p hq],
            (degree_smul_le _ _).trans_lt (degree_mod_by_monic_lt _ hq)⟩).2
  · simp_rw [mod_by_monic_eq_of_not_monic _ hq]
#align polynomial.smul_mod_by_monic Polynomial.smul_mod_by_monic

/-- `_ %ₘ q` as an `R`-linear map. -/
@[simps]
def modByMonicHom (q : R[X]) : R[X] →ₗ[R] R[X]
    where
  toFun p := p %ₘ q
  map_add' := add_mod_by_monic
  map_smul' := smul_mod_by_monic
#align polynomial.mod_by_monic_hom Polynomial.modByMonicHom

end

section

variable [Ring S]

theorem aeval_mod_by_monic_eq_self_of_root [Algebra R S] {p q : R[X]} (hq : q.Monic) {x : S}
    (hx : aeval x q = 0) : aeval x (p %ₘ q) = aeval x p :=
  by-- `eval₂_mod_by_monic_eq_self_of_root` doesn't work here as it needs commutativity
  rw [mod_by_monic_eq_sub_mul_div p hq, _root_.map_sub, _root_.map_mul, hx, zero_mul, sub_zero]
#align polynomial.aeval_mod_by_monic_eq_self_of_root Polynomial.aeval_mod_by_monic_eq_self_of_root

end

end CommRing

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

instance : NoZeroDivisors R[X]
    where eq_zero_or_eq_zero_of_mul_eq_zero a b h :=
    by
    rw [← leading_coeff_eq_zero, ← leading_coeff_eq_zero]
    refine' eq_zero_or_eq_zero_of_mul_eq_zero _
    rw [← leading_coeff_zero, ← leading_coeff_mul, h]

theorem nat_degree_mul (hp : p ≠ 0) (hq : q ≠ 0) : natDegree (p * q) = natDegree p + natDegree q :=
  by
  rw [← WithBot.coe_eq_coe, ← degree_eq_nat_degree (mul_ne_zero hp hq), WithBot.coe_add, ←
    degree_eq_nat_degree hp, ← degree_eq_nat_degree hq, degree_mul]
#align polynomial.nat_degree_mul Polynomial.nat_degree_mul

theorem trailing_degree_mul : (p * q).trailingDegree = p.trailingDegree + q.trailingDegree :=
  by
  by_cases hp : p = 0
  · rw [hp, zero_mul, trailing_degree_zero, top_add]
  by_cases hq : q = 0
  · rw [hq, mul_zero, trailing_degree_zero, add_top]
  rw [trailing_degree_eq_nat_trailing_degree hp, trailing_degree_eq_nat_trailing_degree hq,
    trailing_degree_eq_nat_trailing_degree (mul_ne_zero hp hq), nat_trailing_degree_mul hp hq,
    WithTop.coe_add]
#align polynomial.trailing_degree_mul Polynomial.trailing_degree_mul

@[simp]
theorem nat_degree_pow (p : R[X]) (n : ℕ) : natDegree (p ^ n) = n * natDegree p :=
  if hp0 : p = 0 then
    if hn0 : n = 0 then by simp [hp0, hn0]
    else by rw [hp0, zero_pow (Nat.pos_of_ne_zero hn0)] <;> simp
  else
    nat_degree_pow'
      (by rw [← leading_coeff_pow, Ne.def, leading_coeff_eq_zero] <;> exact pow_ne_zero _ hp0)
#align polynomial.nat_degree_pow Polynomial.nat_degree_pow

theorem degree_le_mul_left (p : R[X]) (hq : q ≠ 0) : degree p ≤ degree (p * q) :=
  if hp : p = 0 then by simp only [hp, zero_mul, le_refl]
  else by
    rw [degree_mul, degree_eq_nat_degree hp, degree_eq_nat_degree hq] <;>
      exact WithBot.coe_le_coe.2 (Nat.le_add_right _ _)
#align polynomial.degree_le_mul_left Polynomial.degree_le_mul_left

theorem nat_degree_le_of_dvd {p q : R[X]} (h1 : p ∣ q) (h2 : q ≠ 0) : p.natDegree ≤ q.natDegree :=
  by
  rcases h1 with ⟨q, rfl⟩; rw [mul_ne_zero_iff] at h2
  rw [nat_degree_mul h2.1 h2.2]; exact Nat.le_add_right _ _
#align polynomial.nat_degree_le_of_dvd Polynomial.nat_degree_le_of_dvd

theorem degree_le_of_dvd {p q : R[X]} (h1 : p ∣ q) (h2 : q ≠ 0) : degree p ≤ degree q :=
  by
  rcases h1 with ⟨q, rfl⟩; rw [mul_ne_zero_iff] at h2
  exact degree_le_mul_left p h2.2
#align polynomial.degree_le_of_dvd Polynomial.degree_le_of_dvd

/-- This lemma is useful for working with the `int_degree` of a rational function. -/
theorem nat_degree_sub_eq_of_prod_eq {p₁ p₂ q₁ q₂ : R[X]} (hp₁ : p₁ ≠ 0) (hq₁ : q₁ ≠ 0)
    (hp₂ : p₂ ≠ 0) (hq₂ : q₂ ≠ 0) (h_eq : p₁ * q₂ = p₂ * q₁) :
    (p₁.natDegree : ℤ) - q₁.natDegree = (p₂.natDegree : ℤ) - q₂.natDegree :=
  by
  rw [sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← nat_degree_mul hp₁ hq₂, ← nat_degree_mul hp₂ hq₁, h_eq]
#align polynomial.nat_degree_sub_eq_of_prod_eq Polynomial.nat_degree_sub_eq_of_prod_eq

theorem nat_degree_eq_zero_of_is_unit (h : IsUnit p) : natDegree p = 0 :=
  by
  nontriviality R
  obtain ⟨q, hq⟩ := h.exists_right_inv
  have := nat_degree_mul (left_ne_zero_of_mul_eq_one hq) (right_ne_zero_of_mul_eq_one hq)
  rw [hq, nat_degree_one, eq_comm, add_eq_zero_iff] at this
  exact this.1
#align polynomial.nat_degree_eq_zero_of_is_unit Polynomial.nat_degree_eq_zero_of_is_unit

theorem degree_eq_zero_of_is_unit [Nontrivial R] (h : IsUnit p) : degree p = 0 :=
  (nat_degree_eq_zero_iff_degree_le_zero.mp <| nat_degree_eq_zero_of_is_unit h).antisymm
    (zero_le_degree_iff.mpr h.NeZero)
#align polynomial.degree_eq_zero_of_is_unit Polynomial.degree_eq_zero_of_is_unit

@[simp]
theorem degree_coe_units [Nontrivial R] (u : R[X]ˣ) : degree (u : R[X]) = 0 :=
  degree_eq_zero_of_is_unit ⟨u, rfl⟩
#align polynomial.degree_coe_units Polynomial.degree_coe_units

theorem is_unit_iff : IsUnit p ↔ ∃ r : R, IsUnit r ∧ c r = p :=
  ⟨fun hp =>
    ⟨p.coeff 0,
      let h := eq_C_of_nat_degree_eq_zero (nat_degree_eq_zero_of_is_unit hp)
      ⟨is_unit_C.1 (h ▸ hp), h.symm⟩⟩,
    fun ⟨r, hr, hrp⟩ => hrp ▸ is_unit_C.2 hr⟩
#align polynomial.is_unit_iff Polynomial.is_unit_iff

variable [CharZero R]

@[simp]
theorem degree_bit0_eq (p : R[X]) : degree (bit0 p) = degree p := by
  rw [bit0_eq_two_mul, degree_mul, (by simp : (2 : R[X]) = C 2),
    @Polynomial.degree_C R _ _ two_ne_zero, zero_add]
#align polynomial.degree_bit0_eq Polynomial.degree_bit0_eq

@[simp]
theorem nat_degree_bit0_eq (p : R[X]) : natDegree (bit0 p) = natDegree p :=
  nat_degree_eq_of_degree_eq <| degree_bit0_eq p
#align polynomial.nat_degree_bit0_eq Polynomial.nat_degree_bit0_eq

@[simp]
theorem nat_degree_bit1_eq (p : R[X]) : natDegree (bit1 p) = natDegree p :=
  by
  rw [bit1]
  apply le_antisymm
  convert nat_degree_add_le _ _
  · simp
  by_cases h : p.nat_degree = 0
  · simp [h]
  apply le_nat_degree_of_ne_zero
  intro hh
  apply h
  simp_all [coeff_one, if_neg (Ne.symm h)]
#align polynomial.nat_degree_bit1_eq Polynomial.nat_degree_bit1_eq

theorem degree_bit1_eq {p : R[X]} (hp : 0 < degree p) : degree (bit1 p) = degree p :=
  by
  rw [bit1, degree_add_eq_left_of_degree_lt, degree_bit0_eq]
  rwa [degree_one, degree_bit0_eq]
#align polynomial.degree_bit1_eq Polynomial.degree_bit1_eq

end NoZeroDivisors

section NoZeroDivisors

variable [CommSemiring R] [NoZeroDivisors R] {p q : R[X]}

theorem irreducible_of_monic (hp : p.Monic) (hp1 : p ≠ 1) :
    Irreducible p ↔ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f = 1 ∨ g = 1 :=
  by
  refine'
    ⟨fun h f g hf hg hp => (h.2 f g hp.symm).imp hf.eq_one_of_is_unit hg.eq_one_of_is_unit, fun h =>
      ⟨hp1 ∘ hp.eq_one_of_is_unit, fun f g hfg =>
        (h (g * C f.leadingCoeff) (f * C g.leadingCoeff) _ _ _).symm.imp (isUnit_of_mul_eq_one f _)
          (isUnit_of_mul_eq_one g _)⟩⟩
  · rwa [monic, leading_coeff_mul, leading_coeff_C, ← leading_coeff_mul, mul_comm, ← hfg, ← monic]
  · rwa [monic, leading_coeff_mul, leading_coeff_C, ← leading_coeff_mul, ← hfg, ← monic]
  ·
    rw [mul_mul_mul_comm, ← C_mul, ← leading_coeff_mul, ← hfg, hp.leading_coeff, C_1, mul_one,
      mul_comm, ← hfg]
#align polynomial.irreducible_of_monic Polynomial.irreducible_of_monic

theorem Monic.irreducible_iff_nat_degree (hp : p.Monic) :
    Irreducible p ↔
      p ≠ 1 ∧ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f.natDegree = 0 ∨ g.natDegree = 0 :=
  by
  by_cases hp1 : p = 1; · simp [hp1]
  rw [irreducible_of_monic hp hp1, and_iff_right hp1]
  refine' forall₄_congr fun a b ha hb => _
  rw [ha.nat_degree_eq_zero_iff_eq_one, hb.nat_degree_eq_zero_iff_eq_one]
#align polynomial.monic.irreducible_iff_nat_degree Polynomial.Monic.irreducible_iff_nat_degree

theorem Monic.irreducible_iff_nat_degree' (hp : p.Monic) :
    Irreducible p ↔
      p ≠ 1 ∧ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → g.natDegree ∉ ioc 0 (p.natDegree / 2) :=
  by
  simp_rw [hp.irreducible_iff_nat_degree, mem_Ioc, Nat.le_div_iff_mul_le zero_lt_two, mul_two]
  apply and_congr_right'
  constructor <;> intro h f g hf hg he <;> subst he
  · rw [hf.nat_degree_mul hg, add_le_add_iff_right]
    exact fun ha => (h f g hf hg rfl).elim (ha.1.trans_le ha.2).ne' ha.1.ne'
  · simp_rw [hf.nat_degree_mul hg, pos_iff_ne_zero] at h
    contrapose! h
    obtain hl | hl := le_total f.nat_degree g.nat_degree
    · exact ⟨g, f, hg, hf, mul_comm g f, h.1, add_le_add_left hl _⟩
    · exact ⟨f, g, hf, hg, rfl, h.2, add_le_add_right hl _⟩
#align polynomial.monic.irreducible_iff_nat_degree' Polynomial.Monic.irreducible_iff_nat_degree'

theorem Monic.not_irreducible_iff_exists_add_mul_eq_coeff (hm : p.Monic) (hnd : p.natDegree = 2) :
    ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂ :=
  by
  cases subsingleton_or_nontrivial R
  · simpa only [nat_degree_of_subsingleton] using hnd
  rw [hm.irreducible_iff_nat_degree', and_iff_right, hnd]
  push_neg; constructor
  · rintro ⟨a, b, ha, hb, rfl, hdb | ⟨⟨⟩⟩⟩
    have hda := hnd
    rw [ha.nat_degree_mul hb, hdb] at hda
    use a.coeff 0, b.coeff 0, mul_coeff_zero a b
    simpa only [next_coeff, hnd, add_right_cancel hda, hdb] using ha.next_coeff_mul hb
  · rintro ⟨c₁, c₂, hmul, hadd⟩
    refine'
      ⟨X + C c₁, X + C c₂, monic_X_add_C _, monic_X_add_C _, _, Or.inl <| nat_degree_X_add_C _⟩
    rw [p.as_sum_range_C_mul_X_pow, hnd, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, ← hnd, hm.coeff_nat_degree, hnd, hmul, hadd, C_mul, C_add, C_1]
    ring
  · rintro rfl
    simpa only [nat_degree_one] using hnd
#align
  polynomial.monic.not_irreducible_iff_exists_add_mul_eq_coeff Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff

theorem root_mul : IsRoot (p * q) a ↔ IsRoot p a ∨ IsRoot q a := by
  simp_rw [is_root, eval_mul, mul_eq_zero]
#align polynomial.root_mul Polynomial.root_mul

theorem root_or_root_of_root_mul (h : IsRoot (p * q) a) : IsRoot p a ∨ IsRoot q a :=
  root_mul.1 h
#align polynomial.root_or_root_of_root_mul Polynomial.root_or_root_of_root_mul

end NoZeroDivisors

section Ring

variable [Ring R] [IsDomain R] {p q : R[X]}

instance : IsDomain R[X] :=
  NoZeroDivisors.to_isDomain _

end Ring

section CommRing

variable [CommRing R]

/-- The multiplicity of `a` as root of a nonzero polynomial `p` is at least `n` iff
  `(X - a) ^ n` divides `p`. -/
theorem le_root_multiplicity_iff {p : R[X]} (p0 : p ≠ 0) {a : R} {n : ℕ} :
    n ≤ rootMultiplicity a p ↔ (X - c a) ^ n ∣ p :=
  by
  simp_rw [root_multiplicity, dif_neg p0, Nat.le_find_iff, not_not]
  refine' ⟨fun h => _, fun h m hm => (pow_dvd_pow _ hm).trans h⟩
  cases n;
  · rw [pow_zero]
    apply one_dvd; · exact h n n.lt_succ_self
#align polynomial.le_root_multiplicity_iff Polynomial.le_root_multiplicity_iff

theorem root_multiplicity_le_iff {p : R[X]} (p0 : p ≠ 0) (a : R) (n : ℕ) :
    rootMultiplicity a p ≤ n ↔ ¬(X - c a) ^ (n + 1) ∣ p := by
  rw [← (le_root_multiplicity_iff p0).Not, not_le, Nat.lt_add_one_iff]
#align polynomial.root_multiplicity_le_iff Polynomial.root_multiplicity_le_iff

theorem pow_root_multiplicity_not_dvd {p : R[X]} (p0 : p ≠ 0) (a : R) :
    ¬(X - c a) ^ (rootMultiplicity a p + 1) ∣ p := by rw [← root_multiplicity_le_iff p0]
#align polynomial.pow_root_multiplicity_not_dvd Polynomial.pow_root_multiplicity_not_dvd

/-- The multiplicity of `p + q` is at least the minimum of the multiplicities. -/
theorem root_multiplicity_add {p q : R[X]} (a : R) (hzero : p + q ≠ 0) :
    min (rootMultiplicity a p) (rootMultiplicity a q) ≤ rootMultiplicity a (p + q) :=
  by
  rw [le_root_multiplicity_iff hzero]
  have hdivp : (X - C a) ^ root_multiplicity a p ∣ p := pow_root_multiplicity_dvd p a
  have hdivq : (X - C a) ^ root_multiplicity a q ∣ q := pow_root_multiplicity_dvd q a
  exact min_pow_dvd_add hdivp hdivq
#align polynomial.root_multiplicity_add Polynomial.root_multiplicity_add

variable [IsDomain R] {p q : R[X]}

section Roots

open Multiset

theorem prime_X_sub_C (r : R) : Prime (X - c r) :=
  ⟨X_sub_C_ne_zero r, not_is_unit_X_sub_C r, fun _ _ =>
    by
    simp_rw [dvd_iff_is_root, is_root.def, eval_mul, mul_eq_zero]
    exact id⟩
#align polynomial.prime_X_sub_C Polynomial.prime_X_sub_C

theorem prime_X : Prime (x : R[X]) :=
  by
  convert prime_X_sub_C (0 : R)
  simp
#align polynomial.prime_X Polynomial.prime_X

theorem Monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Prime p :=
  have : p = X - c (-p.coeff 0) := by simpa [hm.leading_coeff] using eq_X_add_C_of_degree_eq_one hp1
  this.symm ▸ prime_X_sub_C _
#align polynomial.monic.prime_of_degree_eq_one Polynomial.Monic.prime_of_degree_eq_one

theorem irreducible_X_sub_C (r : R) : Irreducible (X - c r) :=
  (prime_X_sub_C r).Irreducible
#align polynomial.irreducible_X_sub_C Polynomial.irreducible_X_sub_C

theorem irreducible_X : Irreducible (x : R[X]) :=
  Prime.irreducible prime_X
#align polynomial.irreducible_X Polynomial.irreducible_X

theorem Monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Irreducible p :=
  (hm.prime_of_degree_eq_one hp1).Irreducible
#align polynomial.monic.irreducible_of_degree_eq_one Polynomial.Monic.irreducible_of_degree_eq_one

theorem eq_of_monic_of_associated (hp : p.Monic) (hq : q.Monic) (hpq : Associated p q) : p = q :=
  by
  obtain ⟨u, hu⟩ := hpq
  unfold monic at hp hq
  rw [eq_C_of_degree_le_zero (degree_coe_units _).le] at hu
  rw [← hu, leading_coeff_mul, hp, one_mul, leading_coeff_C] at hq
  rwa [hq, C_1, mul_one] at hu
  all_goals infer_instance
#align polynomial.eq_of_monic_of_associated Polynomial.eq_of_monic_of_associated

theorem root_multiplicity_mul {p q : R[X]} {x : R} (hpq : p * q ≠ 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q :=
  by
  have hp : p ≠ 0 := left_ne_zero_of_mul hpq
  have hq : q ≠ 0 := right_ne_zero_of_mul hpq
  rw [root_multiplicity_eq_multiplicity (p * q), dif_neg hpq, root_multiplicity_eq_multiplicity p,
    dif_neg hp, root_multiplicity_eq_multiplicity q, dif_neg hq,
    multiplicity.mul' (prime_X_sub_C x)]
#align polynomial.root_multiplicity_mul Polynomial.root_multiplicity_mul

theorem root_multiplicity_X_sub_C_self {x : R} : rootMultiplicity x (X - c x) = 1 := by
  rw [root_multiplicity_eq_multiplicity, dif_neg (X_sub_C_ne_zero x),
    multiplicity.get_multiplicity_self]
#align polynomial.root_multiplicity_X_sub_C_self Polynomial.root_multiplicity_X_sub_C_self

theorem root_multiplicity_X_sub_C {x y : R} :
    rootMultiplicity x (X - c y) = if x = y then 1 else 0 :=
  by
  split_ifs with hxy
  · rw [hxy]
    exact root_multiplicity_X_sub_C_self
  exact root_multiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))
#align polynomial.root_multiplicity_X_sub_C Polynomial.root_multiplicity_X_sub_C

/-- The multiplicity of `a` as root of `(X - a) ^ n` is `n`. -/
theorem root_multiplicity_X_sub_C_pow (a : R) (n : ℕ) : rootMultiplicity a ((X - c a) ^ n) = n :=
  by
  induction' n with n hn
  · refine' root_multiplicity_eq_zero _
    simp only [eval_one, is_root.def, not_false_iff, one_ne_zero, pow_zero]
  have hzero := pow_ne_zero n.succ (X_sub_C_ne_zero a)
  rw [pow_succ (X - C a) n] at hzero⊢
  simp only [root_multiplicity_mul hzero, root_multiplicity_X_sub_C_self, hn, Nat.one_add]
#align polynomial.root_multiplicity_X_sub_C_pow Polynomial.root_multiplicity_X_sub_C_pow

theorem exists_multiset_roots :
    ∀ {p : R[X]} (hp : p ≠ 0),
      ∃ s : Multiset R, (s.card : WithBot ℕ) ≤ degree p ∧ ∀ a, s.count a = rootMultiplicity a p
  | p => fun hp =>
    haveI := Classical.propDecidable (∃ x, is_root p x)
    if h : ∃ x, is_root p x then
      let ⟨x, hx⟩ := h
      have hpd : 0 < degree p := degree_pos_of_root hp hx
      have hd0 : p /ₘ (X - C x) ≠ 0 := fun h => by
        rw [← mul_div_by_monic_eq_iff_is_root.2 hx, h, mul_zero] at hp <;> exact hp rfl
      have wf : degree (p /ₘ _) < degree p :=
        degree_div_by_monic_lt _ (monic_X_sub_C x) hp ((degree_X_sub_C x).symm ▸ by decide)
      let ⟨t, htd, htr⟩ := @exists_multiset_roots (p /ₘ (X - C x)) hd0
      have hdeg : degree (X - C x) ≤ degree p :=
        by
        rw [degree_X_sub_C, degree_eq_nat_degree hp]
        rw [degree_eq_nat_degree hp] at hpd
        exact WithBot.coe_le_coe.2 (WithBot.coe_lt_coe.1 hpd)
      have hdiv0 : p /ₘ (X - C x) ≠ 0 :=
        mt (div_by_monic_eq_zero_iff (monic_X_sub_C x)).1 <| not_lt.2 hdeg
      ⟨x ::ₘ t,
        calc
          (card (x ::ₘ t) : WithBot ℕ) = t.card + 1 := by exact_mod_cast card_cons _ _
          _ ≤ degree p := by
            rw [← degree_add_div_by_monic (monic_X_sub_C x) hdeg, degree_X_sub_C, add_comm] <;>
              exact add_le_add (le_refl (1 : WithBot ℕ)) htd
          ,
        by
        intro a
        conv_rhs => rw [← mul_div_by_monic_eq_iff_is_root.mpr hx]
        rw [root_multiplicity_mul (mul_ne_zero (X_sub_C_ne_zero x) hdiv0),
          root_multiplicity_X_sub_C, ← htr a]
        split_ifs with ha
        · rw [ha, count_cons_self, Nat.succ_eq_add_one, add_comm]
        · rw [count_cons_of_ne ha, zero_add]⟩
    else
      ⟨0, (degree_eq_nat_degree hp).symm ▸ WithBot.coe_le_coe.2 (Nat.zero_le _),
        by
        intro a
        rw [count_zero, root_multiplicity_eq_zero (not_exists.mp h a)]⟩
#align polynomial.exists_multiset_roots Polynomial.exists_multiset_roots

/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
noncomputable def roots (p : R[X]) : Multiset R :=
  if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)
#align polynomial.roots Polynomial.roots

@[simp]
theorem roots_zero : (0 : R[X]).roots = 0 :=
  dif_pos rfl
#align polynomial.roots_zero Polynomial.roots_zero

theorem card_roots (hp0 : p ≠ 0) : ((roots p).card : WithBot ℕ) ≤ degree p :=
  by
  unfold roots
  rw [dif_neg hp0]
  exact (Classical.choose_spec (exists_multiset_roots hp0)).1
#align polynomial.card_roots Polynomial.card_roots

theorem card_roots' (p : R[X]) : p.roots.card ≤ natDegree p :=
  by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact WithBot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq <| degree_eq_nat_degree hp0))
#align polynomial.card_roots' Polynomial.card_roots'

theorem card_roots_sub_C {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    ((p - c a).roots.card : WithBot ℕ) ≤ degree p :=
  calc
    ((p - c a).roots.card : WithBot ℕ) ≤ degree (p - c a) :=
      card_roots <| (mt sub_eq_zero.1) fun h => not_le_of_gt hp0 <| h.symm ▸ degree_C_le
    _ = degree p := by rw [sub_eq_add_neg, ← C_neg] <;> exact degree_add_C hp0
    
#align polynomial.card_roots_sub_C Polynomial.card_roots_sub_C

theorem card_roots_sub_C' {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    (p - c a).roots.card ≤ natDegree p :=
  WithBot.coe_le_coe.1
    (le_trans (card_roots_sub_C hp0)
      (le_of_eq <| degree_eq_nat_degree fun h => by simp_all [lt_irrefl]))
#align polynomial.card_roots_sub_C' Polynomial.card_roots_sub_C'

@[simp]
theorem count_roots (p : R[X]) : p.roots.count a = rootMultiplicity a p :=
  by
  by_cases hp : p = 0
  · simp [hp]
  rw [roots, dif_neg hp]
  exact (Classical.choose_spec (exists_multiset_roots hp)).2 a
#align polynomial.count_roots Polynomial.count_roots

@[simp]
theorem mem_roots' : a ∈ p.roots ↔ p ≠ 0 ∧ IsRoot p a := by
  rw [← count_pos, count_roots p, root_multiplicity_pos']
#align polynomial.mem_roots' Polynomial.mem_roots'

theorem mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ IsRoot p a :=
  mem_roots'.trans <| and_iff_right hp
#align polynomial.mem_roots Polynomial.mem_roots

theorem ne_zero_of_mem_roots (h : a ∈ p.roots) : p ≠ 0 :=
  (mem_roots'.1 h).1
#align polynomial.ne_zero_of_mem_roots Polynomial.ne_zero_of_mem_roots

theorem is_root_of_mem_roots (h : a ∈ p.roots) : IsRoot p a :=
  (mem_roots'.1 h).2
#align polynomial.is_root_of_mem_roots Polynomial.is_root_of_mem_roots

theorem card_le_degree_of_subset_roots {p : R[X]} {Z : Finset R} (h : Z.val ⊆ p.roots) :
    Z.card ≤ p.natDegree :=
  (Multiset.card_le_of_le (Finset.val_le_iff_val_subset.2 h)).trans (Polynomial.card_roots' p)
#align polynomial.card_le_degree_of_subset_roots Polynomial.card_le_degree_of_subset_roots

theorem finite_set_of_is_root {p : R[X]} (hp : p ≠ 0) : Set.Finite { x | IsRoot p x } := by
  simpa only [← Finset.set_of_mem, mem_to_finset, mem_roots hp] using
    p.roots.to_finset.finite_to_set
#align polynomial.finite_set_of_is_root Polynomial.finite_set_of_is_root

theorem eq_zero_of_infinite_is_root (p : R[X]) (h : Set.Infinite { x | IsRoot p x }) : p = 0 :=
  not_imp_comm.mp finite_set_of_is_root h
#align polynomial.eq_zero_of_infinite_is_root Polynomial.eq_zero_of_infinite_is_root

theorem exists_max_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x ≤ x₀ :=
  Set.exists_upper_bound_image _ _ <| finite_set_of_is_root hp
#align polynomial.exists_max_root Polynomial.exists_max_root

theorem exists_min_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x₀ ≤ x :=
  Set.exists_lower_bound_image _ _ <| finite_set_of_is_root hp
#align polynomial.exists_min_root Polynomial.exists_min_root

theorem eq_of_infinite_eval_eq (p q : R[X]) (h : Set.Infinite { x | eval x p = eval x q }) :
    p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_infinite_is_root
  simpa only [is_root, eval_sub, sub_eq_zero]
#align polynomial.eq_of_infinite_eval_eq Polynomial.eq_of_infinite_eval_eq

theorem roots_mul {p q : R[X]} (hpq : p * q ≠ 0) : (p * q).roots = p.roots + q.roots :=
  Multiset.ext.mpr fun r => by
    rw [count_add, count_roots, count_roots, count_roots, root_multiplicity_mul hpq]
#align polynomial.roots_mul Polynomial.roots_mul

theorem roots.le_of_dvd (h : q ≠ 0) : p ∣ q → roots p ≤ roots q :=
  by
  rintro ⟨k, rfl⟩
  exact multiset.le_iff_exists_add.mpr ⟨k.roots, roots_mul h⟩
#align polynomial.roots.le_of_dvd Polynomial.roots.le_of_dvd

theorem mem_roots_sub_C' {p : R[X]} {a x : R} : x ∈ (p - c a).roots ↔ p ≠ c a ∧ p.eval x = a := by
  rw [mem_roots', is_root.def, sub_ne_zero, eval_sub, sub_eq_zero, eval_C]
#align polynomial.mem_roots_sub_C' Polynomial.mem_roots_sub_C'

theorem mem_roots_sub_C {p : R[X]} {a x : R} (hp0 : 0 < degree p) :
    x ∈ (p - c a).roots ↔ p.eval x = a :=
  mem_roots_sub_C'.trans <| and_iff_right fun hp => hp0.not_le <| hp.symm ▸ degree_C_le
#align polynomial.mem_roots_sub_C Polynomial.mem_roots_sub_C

@[simp]
theorem roots_X_sub_C (r : R) : roots (X - c r) = {r} :=
  by
  ext s
  rw [count_roots, root_multiplicity_X_sub_C, count_singleton]
#align polynomial.roots_X_sub_C Polynomial.roots_X_sub_C

@[simp]
theorem roots_X : roots (x : R[X]) = {0} := by rw [← roots_X_sub_C, C_0, sub_zero]
#align polynomial.roots_X Polynomial.roots_X

@[simp]
theorem roots_C (x : R) : (c x).roots = 0 :=
  if H : x = 0 then by rw [H, C_0, roots_zero]
  else
    Multiset.ext.mpr fun r => by
      rw [count_roots, count_zero, root_multiplicity_eq_zero (not_is_root_C _ _ H)]
#align polynomial.roots_C Polynomial.roots_C

@[simp]
theorem roots_one : (1 : R[X]).roots = ∅ :=
  roots_C 1
#align polynomial.roots_one Polynomial.roots_one

@[simp]
theorem roots_C_mul (p : R[X]) (ha : a ≠ 0) : (c a * p).roots = p.roots := by
  by_cases hp : p = 0 <;>
    simp only [roots_mul, *, Ne.def, mul_eq_zero, C_eq_zero, or_self_iff, not_false_iff, roots_C,
      zero_add, mul_zero]
#align polynomial.roots_C_mul Polynomial.roots_C_mul

@[simp]
theorem roots_smul_nonzero (p : R[X]) (ha : a ≠ 0) : (a • p).roots = p.roots := by
  rw [smul_eq_C_mul, roots_C_mul _ ha]
#align polynomial.roots_smul_nonzero Polynomial.roots_smul_nonzero

theorem roots_list_prod (L : List R[X]) :
    (0 : R[X]) ∉ L → L.Prod.roots = (L : Multiset R[X]).bind roots :=
  (List.recOn L fun _ => roots_one) fun hd tl ih H =>
    by
    rw [List.mem_cons, not_or] at H
    rw [List.prod_cons, roots_mul (mul_ne_zero (Ne.symm H.1) <| List.prod_ne_zero H.2), ←
      Multiset.cons_coe, Multiset.cons_bind, ih H.2]
#align polynomial.roots_list_prod Polynomial.roots_list_prod

theorem roots_multiset_prod (m : Multiset R[X]) : (0 : R[X]) ∉ m → m.Prod.roots = m.bind roots :=
  by
  rcases m with ⟨L⟩
  simpa only [Multiset.coe_prod, quot_mk_to_coe''] using roots_list_prod L
#align polynomial.roots_multiset_prod Polynomial.roots_multiset_prod

theorem roots_prod {ι : Type _} (f : ι → R[X]) (s : Finset ι) :
    s.Prod f ≠ 0 → (s.Prod f).roots = s.val.bind fun i => roots (f i) :=
  by
  rcases s with ⟨m, hm⟩
  simpa [Multiset.prod_eq_zero_iff, bind_map] using roots_multiset_prod (m.map f)
#align polynomial.roots_prod Polynomial.roots_prod

@[simp]
theorem roots_pow (p : R[X]) (n : ℕ) : (p ^ n).roots = n • p.roots :=
  by
  induction' n with n ihn
  · rw [pow_zero, roots_one, zero_smul, empty_eq_zero]
  · rcases eq_or_ne p 0 with (rfl | hp)
    · rw [zero_pow n.succ_pos, roots_zero, smul_zero]
    ·
      rw [pow_succ', roots_mul (mul_ne_zero (pow_ne_zero _ hp) hp), ihn, Nat.succ_eq_add_one,
        add_smul, one_smul]
#align polynomial.roots_pow Polynomial.roots_pow

theorem roots_X_pow (n : ℕ) : (X ^ n : R[X]).roots = n • {0} := by rw [roots_pow, roots_X]
#align polynomial.roots_X_pow Polynomial.roots_X_pow

theorem roots_C_mul_X_pow (ha : a ≠ 0) (n : ℕ) : (c a * X ^ n).roots = n • {0} := by
  rw [roots_C_mul _ ha, roots_X_pow]
#align polynomial.roots_C_mul_X_pow Polynomial.roots_C_mul_X_pow

@[simp]
theorem roots_monomial (ha : a ≠ 0) (n : ℕ) : (monomial n a).roots = n • {0} := by
  rw [← C_mul_X_pow_eq_monomial, roots_C_mul_X_pow ha]
#align polynomial.roots_monomial Polynomial.roots_monomial

theorem roots_prod_X_sub_C (s : Finset R) : (s.Prod fun a => X - c a).roots = s.val :=
  (roots_prod (fun a => X - c a) s (prod_ne_zero_iff.mpr fun a _ => X_sub_C_ne_zero a)).trans
    (by simp_rw [roots_X_sub_C, Multiset.bind_singleton, Multiset.map_id'])
#align polynomial.roots_prod_X_sub_C Polynomial.roots_prod_X_sub_C

@[simp]
theorem roots_multiset_prod_X_sub_C (s : Multiset R) : (s.map fun a => X - c a).Prod.roots = s :=
  by
  rw [roots_multiset_prod, Multiset.bind_map]
  · simp_rw [roots_X_sub_C, Multiset.bind_singleton, Multiset.map_id']
  · rw [Multiset.mem_map]
    rintro ⟨a, -, h⟩
    exact X_sub_C_ne_zero a h
#align polynomial.roots_multiset_prod_X_sub_C Polynomial.roots_multiset_prod_X_sub_C

@[simp]
theorem nat_degree_multiset_prod_X_sub_C_eq_card (s : Multiset R) :
    (s.map fun a => X - c a).Prod.natDegree = s.card :=
  by
  rw [nat_degree_multiset_prod_of_monic, Multiset.map_map]
  · convert Multiset.sum_repeat 1 _
    · convert Multiset.map_const _ 1
      ext
      apply nat_degree_X_sub_C
    · simp
  · intro f hf
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hf
    exact monic_X_sub_C a
#align
  polynomial.nat_degree_multiset_prod_X_sub_C_eq_card Polynomial.nat_degree_multiset_prod_X_sub_C_eq_card

theorem card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
    (roots ((x : R[X]) ^ n - c a)).card ≤ n :=
  WithBot.coe_le_coe.1 <|
    calc
      ((roots ((x : R[X]) ^ n - c a)).card : WithBot ℕ) ≤ degree ((x : R[X]) ^ n - c a) :=
        card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a
      
#align polynomial.card_roots_X_pow_sub_C Polynomial.card_roots_X_pow_sub_C

section NthRoots

/-- `nth_roots n a` noncomputably returns the solutions to `x ^ n = a`-/
def nthRoots (n : ℕ) (a : R) : Multiset R :=
  roots ((x : R[X]) ^ n - c a)
#align polynomial.nth_roots Polynomial.nthRoots

@[simp]
theorem mem_nth_roots {n : ℕ} (hn : 0 < n) {a x : R} : x ∈ nthRoots n a ↔ x ^ n = a := by
  rw [nth_roots, mem_roots (X_pow_sub_C_ne_zero hn a), is_root.def, eval_sub, eval_C, eval_pow,
    eval_X, sub_eq_zero]
#align polynomial.mem_nth_roots Polynomial.mem_nth_roots

@[simp]
theorem nth_roots_zero (r : R) : nthRoots 0 r = 0 := by
  simp only [empty_eq_zero, pow_zero, nth_roots, ← C_1, ← C_sub, roots_C]
#align polynomial.nth_roots_zero Polynomial.nth_roots_zero

theorem card_nth_roots (n : ℕ) (a : R) : (nthRoots n a).card ≤ n :=
  if hn : n = 0 then
    if h : (x : R[X]) ^ n - c a = 0 then by
      simp only [Nat.zero_le, nth_roots, roots, h, dif_pos rfl, empty_eq_zero, card_zero]
    else
      WithBot.coe_le_coe.1
        (le_trans (card_roots h)
          (by
            rw [hn, pow_zero, ← C_1, ← RingHom.map_sub]
            exact degree_C_le))
  else by
    rw [← WithBot.coe_le_coe, ← degree_X_pow_sub_C (Nat.pos_of_ne_zero hn) a] <;>
      exact card_roots (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) a)
#align polynomial.card_nth_roots Polynomial.card_nth_roots

@[simp]
theorem nth_roots_two_eq_zero_iff {r : R} : nthRoots 2 r = 0 ↔ ¬IsSquare r := by
  simp_rw [isSquare_iff_exists_sq, eq_zero_iff_forall_not_mem, mem_nth_roots (by norm_num : 0 < 2),
    ← not_exists, eq_comm]
#align polynomial.nth_roots_two_eq_zero_iff Polynomial.nth_roots_two_eq_zero_iff

/-- The multiset `nth_roots ↑n (1 : R)` as a finset. -/
def nthRootsFinset (n : ℕ) (R : Type _) [CommRing R] [IsDomain R] : Finset R :=
  Multiset.toFinset (nthRoots n (1 : R))
#align polynomial.nth_roots_finset Polynomial.nthRootsFinset

@[simp]
theorem mem_nth_roots_finset {n : ℕ} (h : 0 < n) {x : R} :
    x ∈ nthRootsFinset n R ↔ x ^ (n : ℕ) = 1 := by
  rw [nth_roots_finset, mem_to_finset, mem_nth_roots h]
#align polynomial.mem_nth_roots_finset Polynomial.mem_nth_roots_finset

@[simp]
theorem nth_roots_finset_zero : nthRootsFinset 0 R = ∅ := by simp [nth_roots_finset]
#align polynomial.nth_roots_finset_zero Polynomial.nth_roots_finset_zero

end NthRoots

theorem Monic.comp (hp : p.Monic) (hq : q.Monic) (h : q.natDegree ≠ 0) : (p.comp q).Monic := by
  rw [monic.def, leading_coeff_comp h, monic.def.1 hp, monic.def.1 hq, one_pow, one_mul]
#align polynomial.monic.comp Polynomial.Monic.comp

theorem Monic.comp_X_add_C (hp : p.Monic) (r : R) : (p.comp (X + c r)).Monic :=
  by
  refine' hp.comp (monic_X_add_C _) fun ha => _
  rw [nat_degree_X_add_C] at ha
  exact one_ne_zero ha
#align polynomial.monic.comp_X_add_C Polynomial.Monic.comp_X_add_C

theorem Monic.comp_X_sub_C (hp : p.Monic) (r : R) : (p.comp (X - c r)).Monic := by
  simpa using hp.comp_X_add_C (-r)
#align polynomial.monic.comp_X_sub_C Polynomial.Monic.comp_X_sub_C

theorem units_coeff_zero_smul (c : R[X]ˣ) (p : R[X]) : (c : R[X]).coeff 0 • p = c * p := by
  rw [← Polynomial.C_mul', ← Polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]
#align polynomial.units_coeff_zero_smul Polynomial.units_coeff_zero_smul

@[simp]
theorem nat_degree_coe_units (u : R[X]ˣ) : natDegree (u : R[X]) = 0 :=
  nat_degree_eq_of_degree_eq_some (degree_coe_units u)
#align polynomial.nat_degree_coe_units Polynomial.nat_degree_coe_units

theorem comp_eq_zero_iff : p.comp q = 0 ↔ p = 0 ∨ p.eval (q.coeff 0) = 0 ∧ q = c (q.coeff 0) :=
  by
  constructor
  · intro h
    have key : p.nat_degree = 0 ∨ q.nat_degree = 0 := by
      rw [← mul_eq_zero, ← nat_degree_comp, h, nat_degree_zero]
    replace key := Or.imp eq_C_of_nat_degree_eq_zero eq_C_of_nat_degree_eq_zero key
    cases key
    · rw [key, C_comp] at h
      exact Or.inl (key.trans h)
    · rw [key, comp_C, C_eq_zero] at h
      exact Or.inr ⟨h, key⟩
  ·
    exact fun h =>
      Or.ndrec (fun h => by rw [h, zero_comp]) (fun h => by rw [h.2, comp_C, h.1, C_0]) h
#align polynomial.comp_eq_zero_iff Polynomial.comp_eq_zero_iff

theorem zero_of_eval_zero [Infinite R] (p : R[X]) (h : ∀ x, p.eval x = 0) : p = 0 := by
  classical by_contra hp <;>
      exact
        Fintype.false
          ⟨p.roots.to_finset, fun x => multiset.mem_to_finset.mpr ((mem_roots hp).mpr (h _))⟩
#align polynomial.zero_of_eval_zero Polynomial.zero_of_eval_zero

theorem funext [Infinite R] {p q : R[X]} (ext : ∀ r : R, p.eval r = q.eval r) : p = q :=
  by
  rw [← sub_eq_zero]
  apply zero_of_eval_zero
  intro x
  rw [eval_sub, sub_eq_zero, ext]
#align polynomial.funext Polynomial.funext

variable [CommRing T]

/-- The set of distinct roots of `p` in `E`.

If you have a non-separable polynomial, use `polynomial.roots` for the multiset
where multiple roots have the appropriate multiplicity. -/
def rootSet (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Set S :=
  (p.map (algebraMap T S)).roots.toFinset
#align polynomial.root_set Polynomial.rootSet

theorem root_set_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] :
    p.rootSet S = (p.map (algebraMap T S)).roots.toFinset :=
  rfl
#align polynomial.root_set_def Polynomial.root_set_def

@[simp]
theorem root_set_C [CommRing S] [IsDomain S] [Algebra T S] (a : T) : (c a).rootSet S = ∅ := by
  rw [root_set_def, map_C, roots_C, Multiset.to_finset_zero, Finset.coe_empty]
#align polynomial.root_set_C Polynomial.root_set_C

@[simp]
theorem root_set_zero (S) [CommRing S] [IsDomain S] [Algebra T S] : (0 : T[X]).rootSet S = ∅ := by
  rw [← C_0, root_set_C]
#align polynomial.root_set_zero Polynomial.root_set_zero

instance rootSetFintype (p : T[X]) (S : Type _) [CommRing S] [IsDomain S] [Algebra T S] :
    Fintype (p.rootSet S) :=
  FinsetCoe.fintype _
#align polynomial.root_set_fintype Polynomial.rootSetFintype

theorem root_set_finite (p : T[X]) (S : Type _) [CommRing S] [IsDomain S] [Algebra T S] :
    (p.rootSet S).Finite :=
  Set.to_finite _
#align polynomial.root_set_finite Polynomial.root_set_finite

/-- The set of roots of all polynomials of bounded degree and having coefficients in a finite set
is finite. -/
theorem bUnion_roots_finite {R S : Type _} [Semiring R] [CommRing S] [IsDomain S] (m : R →+* S)
    (d : ℕ) {U : Set R} (h : U.Finite) :
    (⋃ (f : R[X]) (hf : f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ U),
        ((f.map m).roots.toFinset : Set S)).Finite :=
  (Set.Finite.bUnion
      (by
        -- We prove that the set of polynomials under consideration is finite because its
        -- image by the injective map `π` is finite
        let π : R[X] → Fin (d + 1) → R := fun f i => f.coeff i
        refine' ((Set.Finite.pi fun e => h).Subset <| _).of_finite_image (_ : Set.InjOn π _)
        · exact Set.image_subset_iff.2 fun f hf i _ => hf.2 i
        · refine' fun x hx y hy hxy => (ext_iff_nat_degree_le hx.1 hy.1).2 fun i hi => _
          exact id congr_fun hxy ⟨i, Nat.lt_succ_of_le hi⟩))
    fun i hi => Finset.finite_to_set _
#align polynomial.bUnion_roots_finite Polynomial.bUnion_roots_finite

theorem mem_root_set' {p : T[X]} {S : Type _} [CommRing S] [IsDomain S] [Algebra T S] {a : S} :
    a ∈ p.rootSet S ↔ p.map (algebraMap T S) ≠ 0 ∧ aeval a p = 0 := by
  rw [root_set, Finset.mem_coe, mem_to_finset, mem_roots', is_root.def, ← eval₂_eq_eval_map,
    aeval_def]
#align polynomial.mem_root_set' Polynomial.mem_root_set'

theorem mem_root_set {p : T[X]} {S : Type _} [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] {a : S} : a ∈ p.rootSet S ↔ p ≠ 0 ∧ aeval a p = 0 := by
  rw [mem_root_set',
    (map_injective _ (NoZeroSMulDivisors.algebra_map_injective T S)).ne_iff'
      (Polynomial.map_zero _)]
#align polynomial.mem_root_set Polynomial.mem_root_set

theorem mem_root_set_of_ne {p : T[X]} {S : Type _} [CommRing S] [IsDomain S] [Algebra T S]
    [NoZeroSMulDivisors T S] (hp : p ≠ 0) {a : S} : a ∈ p.rootSet S ↔ aeval a p = 0 :=
  mem_root_set.trans <| and_iff_right hp
#align polynomial.mem_root_set_of_ne Polynomial.mem_root_set_of_ne

theorem root_set_maps_to' {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S] [CommRing S']
    [IsDomain S'] [Algebra T S'] (hp : p.map (algebraMap T S') = 0 → p.map (algebraMap T S) = 0)
    (f : S →ₐ[T] S') : (p.rootSet S).MapsTo f (p.rootSet S') := fun x hx =>
  by
  rw [mem_root_set'] at hx⊢
  rw [aeval_alg_hom, AlgHom.comp_apply, hx.2, _root_.map_zero]
  exact ⟨mt hp hx.1, rfl⟩
#align polynomial.root_set_maps_to' Polynomial.root_set_maps_to'

theorem ne_zero_of_mem_root_set {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    (h : a ∈ p.rootSet S) : p ≠ 0 := fun hf => by rwa [hf, root_set_zero] at h
#align polynomial.ne_zero_of_mem_root_set Polynomial.ne_zero_of_mem_root_set

theorem aeval_eq_zero_of_mem_root_set {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    (hx : a ∈ p.rootSet S) : aeval a p = 0 :=
  (mem_root_set'.1 hx).2
#align polynomial.aeval_eq_zero_of_mem_root_set Polynomial.aeval_eq_zero_of_mem_root_set

theorem root_set_maps_to {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S] [CommRing S']
    [IsDomain S'] [Algebra T S'] [NoZeroSMulDivisors T S'] (f : S →ₐ[T] S') :
    (p.rootSet S).MapsTo f (p.rootSet S') :=
  by
  refine' root_set_maps_to' (fun h₀ => _) f
  obtain rfl : p = 0 :=
    map_injective _ (NoZeroSMulDivisors.algebra_map_injective T S') (by rwa [Polynomial.map_zero])
  exact Polynomial.map_zero _
#align polynomial.root_set_maps_to Polynomial.root_set_maps_to

end Roots

theorem coeff_coe_units_zero_ne_zero (u : R[X]ˣ) : coeff (u : R[X]) 0 ≠ 0 :=
  by
  conv in 0 => rw [← nat_degree_coe_units u]
  rw [← leading_coeff, Ne.def, leading_coeff_eq_zero]
  exact Units.ne_zero _
#align polynomial.coeff_coe_units_zero_ne_zero Polynomial.coeff_coe_units_zero_ne_zero

theorem degree_eq_degree_of_associated (h : Associated p q) : degree p = degree q :=
  by
  let ⟨u, hu⟩ := h
  simp [hu.symm]
#align polynomial.degree_eq_degree_of_associated Polynomial.degree_eq_degree_of_associated

theorem degree_eq_one_of_irreducible_of_root (hi : Irreducible p) {x : R} (hx : IsRoot p x) :
    degree p = 1 :=
  let ⟨g, hg⟩ := dvd_iff_is_root.2 hx
  have : IsUnit (X - c x) ∨ IsUnit g := hi.is_unit_or_is_unit hg
  this.elim
    (fun h => by
      have h₁ : degree (X - c x) = 1 := degree_X_sub_C x
      have h₂ : degree (X - c x) = 0 := degree_eq_zero_of_is_unit h
      rw [h₁] at h₂ <;> exact absurd h₂ (by decide))
    fun hgu => by rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_is_unit hgu, add_zero]
#align
  polynomial.degree_eq_one_of_irreducible_of_root Polynomial.degree_eq_one_of_irreducible_of_root

/-- Division by a monic polynomial doesn't change the leading coefficient. -/
theorem leading_coeff_div_by_monic_of_monic {R : Type u} [CommRing R] {p q : R[X]}
    (hmonic : q.Monic) (hdegree : q.degree ≤ p.degree) : (p /ₘ q).leadingCoeff = p.leadingCoeff :=
  by
  nontriviality
  have h : q.leading_coeff * (p /ₘ q).leadingCoeff ≠ 0 := by
    simpa [div_by_monic_eq_zero_iff hmonic, hmonic.leading_coeff,
      Nat.WithBot.one_le_iff_zero_lt] using hdegree
  nth_rw_rhs 1 [← mod_by_monic_add_div p hmonic]
  rw [leading_coeff_add_of_degree_lt, leading_coeff_monic_mul hmonic]
  rw [degree_mul' h, degree_add_div_by_monic hmonic hdegree]
  exact (degree_mod_by_monic_lt p hmonic).trans_le hdegree
#align polynomial.leading_coeff_div_by_monic_of_monic Polynomial.leading_coeff_div_by_monic_of_monic

theorem leading_coeff_div_by_monic_X_sub_C (p : R[X]) (hp : degree p ≠ 0) (a : R) :
    leadingCoeff (p /ₘ (X - c a)) = leadingCoeff p :=
  by
  nontriviality
  cases' hp.lt_or_lt with hd hd
  · rw [degree_eq_bot.mp <| (Nat.WithBot.lt_zero_iff _).mp hd, zero_div_by_monic]
  refine' leading_coeff_div_by_monic_of_monic (monic_X_sub_C a) _
  rwa [degree_X_sub_C, Nat.WithBot.one_le_iff_zero_lt]
#align polynomial.leading_coeff_div_by_monic_X_sub_C Polynomial.leading_coeff_div_by_monic_X_sub_C

theorem eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le {R} [CommRing R] {p q : R[X]}
    (hp : p.Monic) (hdiv : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) : q = c q.leadingCoeff * p :=
  by
  obtain ⟨r, hr⟩ := hdiv
  obtain rfl | hq := eq_or_ne q 0; · simp
  have rzero : r ≠ 0 := fun h => by simpa [h, hq] using hr
  rw [hr, nat_degree_mul'] at hdeg; swap
  · rw [hp.leading_coeff, one_mul, leading_coeff_ne_zero]
    exact rzero
  rw [mul_comm, @eq_C_of_nat_degree_eq_zero _ _ r] at hr
  · convert hr
    convert leading_coeff_C _ using 1
    rw [hr, leading_coeff_mul_monic hp]
  · exact (add_right_inj _).1 (le_antisymm hdeg <| Nat.le.intro rfl)
#align
  polynomial.eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le Polynomial.eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le

theorem eq_of_monic_of_dvd_of_nat_degree_le {R} [CommRing R] {p q : R[X]} (hp : p.Monic)
    (hq : q.Monic) (hdiv : p ∣ q) (hdeg : q.natDegree ≤ p.natDegree) : q = p :=
  by
  convert eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le hp hdiv hdeg
  rw [hq.leading_coeff, C_1, one_mul]
#align polynomial.eq_of_monic_of_dvd_of_nat_degree_le Polynomial.eq_of_monic_of_dvd_of_nat_degree_le

theorem is_coprime_X_sub_C_of_is_unit_sub {R} [CommRing R] {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (X - c a) (X - c b) :=
  ⟨-c h.Unit⁻¹.val, c h.Unit⁻¹.val,
    by
    rw [neg_mul_comm, ← left_distrib, neg_add_eq_sub, sub_sub_sub_cancel_left, ← C_sub, ← C_mul]
    convert C_1
    exact h.coe_inv_mul⟩
#align polynomial.is_coprime_X_sub_C_of_is_unit_sub Polynomial.is_coprime_X_sub_C_of_is_unit_sub

theorem pairwise_coprime_X_sub_C {K} [Field K] {I : Type v} {s : I → K} (H : Function.Injective s) :
    Pairwise (IsCoprime on fun i : I => X - c (s i)) := fun i j hij =>
  is_coprime_X_sub_C_of_is_unit_sub (sub_ne_zero_of_ne <| H.Ne hij).IsUnit
#align polynomial.pairwise_coprime_X_sub_C Polynomial.pairwise_coprime_X_sub_C

theorem monic_prod_multiset_X_sub_C : Monic (p.roots.map fun a => X - c a).Prod :=
  monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a
#align polynomial.monic_prod_multiset_X_sub_C Polynomial.monic_prod_multiset_X_sub_C

theorem prod_multiset_root_eq_finset_root :
    (p.roots.map fun a => X - c a).Prod =
      p.roots.toFinset.Prod fun a => (X - c a) ^ rootMultiplicity a p :=
  by simp only [count_roots, Finset.prod_multiset_map_count]
#align polynomial.prod_multiset_root_eq_finset_root Polynomial.prod_multiset_root_eq_finset_root

/-- The product `∏ (X - a)` for `a` inside the multiset `p.roots` divides `p`. -/
theorem prod_multiset_X_sub_C_dvd (p : R[X]) : (p.roots.map fun a => X - c a).Prod ∣ p :=
  by
  rw [← map_dvd_map _ (IsFractionRing.injective R <| FractionRing R) monic_prod_multiset_X_sub_C]
  rw [prod_multiset_root_eq_finset_root, Polynomial.map_prod]
  refine' Finset.prod_dvd_of_coprime (fun a _ b _ h => _) fun a _ => _
  · simp_rw [Polynomial.map_pow, Polynomial.map_sub, map_C, map_X]
    exact (pairwise_coprime_X_sub_C (IsFractionRing.injective R <| FractionRing R) h).pow
  · exact Polynomial.map_dvd _ (pow_root_multiplicity_dvd p a)
#align polynomial.prod_multiset_X_sub_C_dvd Polynomial.prod_multiset_X_sub_C_dvd

/-- A Galois connection. -/
theorem Multiset.prod_X_sub_C_dvd_iff_le_roots {p : R[X]} (hp : p ≠ 0) (s : Multiset R) :
    (s.map fun a => X - c a).Prod ∣ p ↔ s ≤ p.roots :=
  ⟨fun h =>
    Multiset.le_iff_count.2 fun r =>
      by
      rw [count_roots, le_root_multiplicity_iff hp, ← Multiset.prod_repeat, ←
        Multiset.map_repeat fun a => X - C a, ← Multiset.filter_eq]
      exact (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| s.filter_le _).trans h,
    fun h =>
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map h).trans p.prod_multiset_X_sub_C_dvd⟩
#align multiset.prod_X_sub_C_dvd_iff_le_roots Multiset.prod_X_sub_C_dvd_iff_le_roots

theorem exists_prod_multiset_X_sub_C_mul (p : R[X]) :
    ∃ q,
      (p.roots.map fun a => X - c a).Prod * q = p ∧
        p.roots.card + q.natDegree = p.natDegree ∧ q.roots = 0 :=
  by
  obtain ⟨q, he⟩ := p.prod_multiset_X_sub_C_dvd
  use q, he.symm
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero] at he
    subst he
    simp
  constructor
  · conv_rhs => rw [he]
    rw [monic_prod_multiset_X_sub_C.nat_degree_mul' hq, nat_degree_multiset_prod_X_sub_C_eq_card]
  · replace he := congr_arg roots he.symm
    rw [roots_mul, roots_multiset_prod_X_sub_C] at he
    exacts[add_right_eq_self.1 he, mul_ne_zero monic_prod_multiset_X_sub_C.ne_zero hq]
#align polynomial.exists_prod_multiset_X_sub_C_mul Polynomial.exists_prod_multiset_X_sub_C_mul

/-- A polynomial `p` that has as many roots as its degree
can be written `p = p.leading_coeff * ∏(X - a)`, for `a` in `p.roots`. -/
theorem C_leading_coeff_mul_prod_multiset_X_sub_C (hroots : p.roots.card = p.natDegree) :
    c p.leadingCoeff * (p.roots.map fun a => X - c a).Prod = p :=
  (eq_leading_coeff_mul_of_monic_of_dvd_of_nat_degree_le monic_prod_multiset_X_sub_C
      p.prod_multiset_X_sub_C_dvd
      ((nat_degree_multiset_prod_X_sub_C_eq_card _).trans hroots).ge).symm
#align
  polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C Polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C

/-- A monic polynomial `p` that has as many roots as its degree
can be written `p = ∏(X - a)`, for `a` in `p.roots`. -/
theorem prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp : p.Monic)
    (hroots : p.roots.card = p.natDegree) : (p.roots.map fun a => X - c a).Prod = p :=
  by
  convert C_leading_coeff_mul_prod_multiset_X_sub_C hroots
  rw [hp.leading_coeff, C_1, one_mul]
#align
  polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq

end CommRing

section

variable {A B : Type _} [CommRing A] [CommRing B]

theorem le_root_multiplicity_map {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0) (a : A) :
    rootMultiplicity a p ≤ rootMultiplicity (f a) (p.map f) :=
  by
  rw [le_root_multiplicity_iff hmap]
  refine' trans _ ((map_ring_hom f).map_dvd (pow_root_multiplicity_dvd p a))
  rw [map_pow, map_sub, coe_map_ring_hom, map_X, map_C]
#align polynomial.le_root_multiplicity_map Polynomial.le_root_multiplicity_map

theorem eq_root_multiplicity_map {p : A[X]} {f : A →+* B} (hf : Function.Injective f) (a : A) :
    rootMultiplicity a p = rootMultiplicity (f a) (p.map f) :=
  by
  by_cases hp0 : p = 0; · simp only [hp0, root_multiplicity_zero, Polynomial.map_zero]
  apply le_antisymm (le_root_multiplicity_map ((Polynomial.map_ne_zero_iff hf).mpr hp0) a)
  rw [le_root_multiplicity_iff hp0, ← map_dvd_map f hf ((monic_X_sub_C a).pow _),
    Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  apply pow_root_multiplicity_dvd
#align polynomial.eq_root_multiplicity_map Polynomial.eq_root_multiplicity_map

theorem count_map_roots [IsDomain A] {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0) (b : B) :
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) :=
  by
  rw [le_root_multiplicity_iff hmap, ← Multiset.prod_repeat, ← Multiset.map_repeat fun a => X - C a]
  rw [← Multiset.filter_eq]
  refine' (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| Multiset.filter_le _ _).trans _
  convert Polynomial.map_dvd _ p.prod_multiset_X_sub_C_dvd
  simp only [Polynomial.map_multiset_prod, Multiset.map_map]
  congr ; ext1
  simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
#align polynomial.count_map_roots Polynomial.count_map_roots

theorem count_map_roots_of_injective [IsDomain A] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) (b : B) : (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) :=
  by
  by_cases hp0 : p = 0
  ·
    simp only [hp0, roots_zero, Multiset.map_zero, Multiset.count_zero, Polynomial.map_zero,
      root_multiplicity_zero]
  · exact count_map_roots ((Polynomial.map_ne_zero_iff hf).mpr hp0) b
#align polynomial.count_map_roots_of_injective Polynomial.count_map_roots_of_injective

theorem map_roots_le [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    p.roots.map f ≤ (p.map f).roots :=
  Multiset.le_iff_count.2 fun b => by
    rw [count_roots]
    apply count_map_roots h
#align polynomial.map_roots_le Polynomial.map_roots_le

theorem map_roots_le_of_injective [IsDomain A] [IsDomain B] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) : p.roots.map f ≤ (p.map f).roots :=
  by
  by_cases hp0 : p = 0; · simp only [hp0, roots_zero, Multiset.map_zero, Polynomial.map_zero]
  exact map_roots_le ((Polynomial.map_ne_zero_iff hf).mpr hp0)
#align polynomial.map_roots_le_of_injective Polynomial.map_roots_le_of_injective

theorem card_roots_le_map [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    p.roots.card ≤ (p.map f).roots.card :=
  by
  rw [← p.roots.card_map f]
  exact Multiset.card_le_of_le (map_roots_le h)
#align polynomial.card_roots_le_map Polynomial.card_roots_le_map

theorem card_roots_le_map_of_injective [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B}
    (hf : Function.Injective f) : p.roots.card ≤ (p.map f).roots.card :=
  by
  by_cases hp0 : p = 0; · simp only [hp0, roots_zero, Polynomial.map_zero, Multiset.card_zero]
  exact card_roots_le_map ((Polynomial.map_ne_zero_iff hf).mpr hp0)
#align polynomial.card_roots_le_map_of_injective Polynomial.card_roots_le_map_of_injective

theorem roots_map_of_injective_of_card_eq_nat_degree [IsDomain A] [IsDomain B] {p : A[X]}
    {f : A →+* B} (hf : Function.Injective f) (hroots : p.roots.card = p.natDegree) :
    p.roots.map f = (p.map f).roots :=
  by
  apply Multiset.eq_of_le_of_card_le (map_roots_le_of_injective p hf)
  simpa only [Multiset.card_map, hroots] using (card_roots' _).trans (nat_degree_map_le f p)
#align
  polynomial.roots_map_of_injective_of_card_eq_nat_degree Polynomial.roots_map_of_injective_of_card_eq_nat_degree

end

section

variable [Semiring R] [CommRing S] [IsDomain S] (φ : R →+* S)

theorem is_unit_of_is_unit_leading_coeff_of_is_unit_map {f : R[X]} (hf : IsUnit f.leadingCoeff)
    (H : IsUnit (map φ f)) : IsUnit f :=
  by
  have dz := degree_eq_zero_of_is_unit H
  rw [degree_map_eq_of_leading_coeff_ne_zero] at dz
  · rw [eq_C_of_degree_eq_zero dz]
    refine' IsUnit.map C _
    convert hf
    rw [(degree_eq_iff_nat_degree_eq _).1 dz]
    rintro rfl
    simpa using H
  · intro h
    have u : IsUnit (φ f.leading_coeff) := IsUnit.map φ hf
    rw [h] at u
    simpa using u
#align
  polynomial.is_unit_of_is_unit_leading_coeff_of_is_unit_map Polynomial.is_unit_of_is_unit_leading_coeff_of_is_unit_map

end

section

variable [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (φ : R →+* S)

/-- A polynomial over an integral domain `R` is irreducible if it is monic and
  irreducible after mapping into an integral domain `S`.

A special case of this lemma is that a polynomial over `ℤ` is irreducible if
  it is monic and irreducible over `ℤ/pℤ` for some prime `p`.
-/
theorem Monic.irreducible_of_irreducible_map (f : R[X]) (h_mon : Monic f)
    (h_irr : Irreducible (map φ f)) : Irreducible f :=
  by
  refine' ⟨h_irr.not_unit ∘ IsUnit.map (map_ring_hom φ), fun a b h => _⟩
  dsimp [monic] at h_mon
  have q := (leading_coeff_mul a b).symm
  rw [← h, h_mon] at q
  refine'
        (h_irr.is_unit_or_is_unit <| (congr_arg (map φ) h).trans (Polynomial.map_mul φ)).imp _ _ <;>
      apply is_unit_of_is_unit_leading_coeff_of_is_unit_map <;>
    apply isUnit_of_mul_eq_one
  · exact q;
  · rw [mul_comm]
    exact q
#align
  polynomial.monic.irreducible_of_irreducible_map Polynomial.Monic.irreducible_of_irreducible_map

end

end Polynomial

