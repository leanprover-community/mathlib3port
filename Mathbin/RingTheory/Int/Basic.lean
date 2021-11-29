import Mathbin.RingTheory.Coprime.Basic 
import Mathbin.RingTheory.UniqueFactorizationDomain

/-!
# Divisibility over ℕ and ℤ

This file collects results for the integers and natural numbers that use abstract algebra in
their proofs or cases of ℕ and ℤ being examples of structures in abstract algebra.

## Main statements

* `nat.prime_iff`: `nat.prime` coincides with the general definition of `prime`
* `nat.irreducible_iff_prime`: a non-unit natural number is only divisible by `1` iff it is prime
* `nat.factors_eq`: the multiset of elements of `nat.factors` is equal to the factors
   given by the `unique_factorization_monoid` instance
* ℤ is a `normalization_monoid`
* ℤ is a `gcd_monoid`

## Tags

prime, irreducible, natural numbers, integers, normalization monoid, gcd monoid,
greatest common divisor, prime factorization, prime factors, unique factorization,
unique factors
-/


theorem Nat.prime_iff {p : ℕ} : p.prime ↔ Prime p :=
  by 
    split  <;> intro h
    ·
      refine' ⟨h.ne_zero, ⟨_, fun a b => _⟩⟩
      ·
        rw [Nat.is_unit_iff]
        apply h.ne_one
      ·
        apply h.dvd_mul.1
    ·
      refine' ⟨_, fun m hm => _⟩
      ·
        cases p
        ·
          exfalso 
          apply h.ne_zero rfl 
        cases p
        ·
          exfalso 
          apply h.ne_one rfl 
        exact (add_le_add_right (zero_le p) 2 : _)
      ·
        cases' hm with n hn 
        cases' h.2.2 m n (hn ▸ dvd_rfl) with hpm hpn
        ·
          right 
          apply Nat.dvd_antisymm (Dvd.intro _ hn.symm) hpm
        ·
          left 
          cases n
          ·
            exfalso 
            rw [hn, mul_zero] at h 
            apply h.ne_zero rfl 
          apply Nat.eq_of_mul_eq_mul_rightₓ (Nat.succ_posₓ _)
          rw [←hn, one_mulₓ]
          apply Nat.dvd_antisymm hpn (Dvd.intro m _)
          rw [mul_commₓ, hn]

theorem Nat.irreducible_iff_prime {p : ℕ} : Irreducible p ↔ Prime p :=
  by 
    refine' ⟨fun h => _, Prime.irreducible⟩
    rw [←Nat.prime_iff]
    refine' ⟨_, fun m hm => _⟩
    ·
      cases p
      ·
        exfalso 
        apply h.ne_zero rfl 
      cases p
      ·
        exfalso 
        apply h.not_unit is_unit_one 
      exact (add_le_add_right (zero_le p) 2 : _)
    ·
      cases' hm with n hn 
      cases' h.is_unit_or_is_unit hn with um un
      ·
        left 
        rw [Nat.is_unit_iff.1 um]
      ·
        right 
        rw [hn, Nat.is_unit_iff.1 un, mul_oneₓ]

namespace Nat

instance : WfDvdMonoid ℕ :=
  ⟨by 
      apply RelHom.well_founded _ (WithTop.well_founded_lt Nat.lt_wf)
      refine' ⟨fun x => if x = 0 then ⊤ else x, _⟩
      intro a b h 
      cases a
      ·
        exfalso 
        revert h 
        simp [DvdNotUnit]
      cases b
      ·
        simp [succ_ne_zero, WithTop.coe_lt_top]
      cases' dvd_and_not_dvd_iff.2 h with h1 h2 
      simp only [succ_ne_zero, WithTop.coe_lt_coe, if_false]
      apply lt_of_le_of_neₓ (Nat.le_of_dvdₓ (Nat.succ_posₓ _) h1) fun con => h2 _ 
      rw [Con]⟩

instance : UniqueFactorizationMonoid ℕ :=
  ⟨fun _ => Nat.irreducible_iff_prime⟩

end Nat

/-- `ℕ` is a gcd_monoid. -/
instance : GcdMonoid ℕ :=
  { gcd := Nat.gcdₓ, lcm := Nat.lcmₓ, gcd_dvd_left := Nat.gcd_dvd_leftₓ, gcd_dvd_right := Nat.gcd_dvd_rightₓ,
    dvd_gcd := fun a b c => Nat.dvd_gcdₓ,
    gcd_mul_lcm :=
      fun a b =>
        by 
          rw [Nat.gcd_mul_lcmₓ],
    lcm_zero_left := Nat.lcm_zero_leftₓ, lcm_zero_right := Nat.lcm_zero_rightₓ }

instance : NormalizedGcdMonoid ℕ :=
  { (inferInstance : GcdMonoid ℕ), (inferInstance : NormalizationMonoid ℕ) with
    normalize_gcd := fun a b => normalize_eq _, normalize_lcm := fun a b => normalize_eq _ }

theorem gcd_eq_nat_gcd (m n : ℕ) : gcd m n = Nat.gcdₓ m n :=
  rfl

theorem lcm_eq_nat_lcm (m n : ℕ) : lcm m n = Nat.lcmₓ m n :=
  rfl

namespace Int

section NormalizationMonoid

instance : NormalizationMonoid ℤ :=
  { normUnit := fun a : ℤ => if 0 ≤ a then 1 else -1, norm_unit_zero := if_pos (le_reflₓ _),
    norm_unit_mul :=
      fun a b hna hnb =>
        by 
          cases' hna.lt_or_lt with ha ha <;>
            cases' hnb.lt_or_lt with hb hb <;> simp [mul_nonneg_iff, ha.le, ha.not_le, hb.le, hb.not_le],
    norm_unit_coe_units :=
      fun u =>
        (units_eq_one_or u).elim (fun eq => Eq.symm ▸ if_pos zero_le_one)
          fun eq =>
            Eq.symm ▸
              if_neg
                (not_le_of_gtₓ$
                  show (-1 : ℤ) < 0 by 
                    decide) }

theorem normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z :=
  show (z*«expr↑ » (ite _ _ _)) = z by 
    rw [if_pos h, Units.coe_one, mul_oneₓ]

theorem normalize_of_neg {z : ℤ} (h : z < 0) : normalize z = -z :=
  show (z*«expr↑ » (ite _ _ _)) = -z by 
    rw [if_neg (not_le_of_gtₓ h), Units.coe_neg, Units.coe_one, mul_neg_one]

theorem normalize_coe_nat (n : ℕ) : normalize (n : ℤ) = n :=
  normalize_of_nonneg (coe_nat_le_coe_nat_of_le$ Nat.zero_leₓ n)

theorem coe_nat_abs_eq_normalize (z : ℤ) : (z.nat_abs : ℤ) = normalize z :=
  by 
    byCases' 0 ≤ z
    ·
      simp [nat_abs_of_nonneg h, normalize_of_nonneg h]
    ·
      simp [of_nat_nat_abs_of_nonpos (le_of_not_geₓ h), normalize_of_neg (lt_of_not_geₓ h)]

theorem nonneg_of_normalize_eq_self {z : ℤ} (hz : normalize z = z) : 0 ≤ z :=
  calc 0 ≤ (z.nat_abs : ℤ) := coe_zero_le _ 
    _ = normalize z := coe_nat_abs_eq_normalize _ 
    _ = z := hz
    

theorem nonneg_iff_normalize_eq_self (z : ℤ) : normalize z = z ↔ 0 ≤ z :=
  ⟨nonneg_of_normalize_eq_self, normalize_of_nonneg⟩

theorem eq_of_associated_of_nonneg {a b : ℤ} (h : Associated a b) (ha : 0 ≤ a) (hb : 0 ≤ b) : a = b :=
  dvd_antisymm_of_normalize_eq (normalize_of_nonneg ha) (normalize_of_nonneg hb) h.dvd h.symm.dvd

end NormalizationMonoid

section GcdMonoid

instance : GcdMonoid ℤ :=
  { gcd := fun a b => Int.gcdₓ a b, lcm := fun a b => Int.lcm a b, gcd_dvd_left := fun a b => Int.gcd_dvd_left _ _,
    gcd_dvd_right := fun a b => Int.gcd_dvd_right _ _, dvd_gcd := fun a b c => dvd_gcd,
    gcd_mul_lcm :=
      fun a b =>
        by 
          rw [←Int.coe_nat_mul, gcd_mul_lcm, coe_nat_abs_eq_normalize]
          exact normalize_associated (a*b),
    lcm_zero_left := fun a => coe_nat_eq_zero.2$ Nat.lcm_zero_leftₓ _,
    lcm_zero_right := fun a => coe_nat_eq_zero.2$ Nat.lcm_zero_rightₓ _ }

instance : NormalizedGcdMonoid ℤ :=
  { Int.normalizationMonoid, (inferInstance : GcdMonoid ℤ) with normalize_gcd := fun a b => normalize_coe_nat _,
    normalize_lcm := fun a b => normalize_coe_nat _ }

theorem coe_gcd (i j : ℤ) : «expr↑ » (Int.gcdₓ i j) = GcdMonoid.gcd i j :=
  rfl

theorem coe_lcm (i j : ℤ) : «expr↑ » (Int.lcm i j) = GcdMonoid.lcm i j :=
  rfl

theorem nat_abs_gcd (i j : ℤ) : nat_abs (GcdMonoid.gcd i j) = Int.gcdₓ i j :=
  rfl

theorem nat_abs_lcm (i j : ℤ) : nat_abs (GcdMonoid.lcm i j) = Int.lcm i j :=
  rfl

end GcdMonoid

theorem exists_unit_of_abs (a : ℤ) : ∃ (u : ℤ)(h : IsUnit u), (Int.natAbs a : ℤ) = u*a :=
  by 
    cases' nat_abs_eq a with h
    ·
      use 1, is_unit_one 
      rw [←h, one_mulₓ]
    ·
      use -1, is_unit_one.neg 
      rw [←neg_eq_iff_neg_eq.mp (Eq.symm h)]
      simp only [neg_mul_eq_neg_mul_symm, one_mulₓ]

theorem gcd_eq_nat_abs {a b : ℤ} : Int.gcdₓ a b = Nat.gcdₓ a.nat_abs b.nat_abs :=
  rfl

theorem gcd_eq_one_iff_coprime {a b : ℤ} : Int.gcdₓ a b = 1 ↔ IsCoprime a b :=
  by 
    split 
    ·
      intro hg 
      obtain ⟨ua, hua, ha⟩ := exists_unit_of_abs a 
      obtain ⟨ub, hub, hb⟩ := exists_unit_of_abs b 
      use Nat.gcdA (Int.natAbs a) (Int.natAbs b)*ua, Nat.gcdB (Int.natAbs a) (Int.natAbs b)*ub 
      rw [mul_assocₓ, ←ha, mul_assocₓ, ←hb, mul_commₓ, mul_commₓ _ (Int.natAbs b : ℤ), ←Nat.gcd_eq_gcd_ab,
        ←gcd_eq_nat_abs, hg, Int.coe_nat_one]
    ·
      rintro ⟨r, s, h⟩
      byContra hg 
      obtain ⟨p, ⟨hp, ha, hb⟩⟩ := nat.prime.not_coprime_iff_dvd.mp hg 
      apply Nat.Prime.not_dvd_one hp 
      rw [←coe_nat_dvd, Int.coe_nat_one, ←h]
      exact dvd_add ((coe_nat_dvd_left.mpr ha).mul_left _) ((coe_nat_dvd_left.mpr hb).mul_left _)

theorem coprime_iff_nat_coprime {a b : ℤ} : IsCoprime a b ↔ Nat.Coprime a.nat_abs b.nat_abs :=
  by 
    rw [←gcd_eq_one_iff_coprime, Nat.coprime_iff_gcd_eq_oneₓ, gcd_eq_nat_abs]

-- error in RingTheory.Int.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sq_of_gcd_eq_one
{a b c : exprℤ()}
(h : «expr = »(int.gcd a b, 1))
(heq : «expr = »(«expr * »(a, b), «expr ^ »(c, 2))) : «expr∃ , »((a0 : exprℤ()), «expr ∨ »(«expr = »(a, «expr ^ »(a0, 2)), «expr = »(a, «expr- »(«expr ^ »(a0, 2))))) :=
begin
  have [ident h'] [":", expr is_unit (gcd_monoid.gcd a b)] [],
  { rw ["[", "<-", expr coe_gcd, ",", expr h, ",", expr int.coe_nat_one, "]"] [],
    exact [expr is_unit_one] },
  obtain ["⟨", ident d, ",", "⟨", ident u, ",", ident hu, "⟩", "⟩", ":=", expr exists_associated_pow_of_mul_eq_pow h' heq],
  use [expr d],
  rw ["<-", expr hu] [],
  cases [expr int.units_eq_one_or u] ["with", ident hu', ident hu']; { rw [expr hu'] [],
    simp [] [] [] [] [] [] }
end

theorem sq_of_coprime {a b c : ℤ} (h : IsCoprime a b) (heq : (a*b) = (c^2)) : ∃ a0 : ℤ, a = (a0^2) ∨ a = -(a0^2) :=
  sq_of_gcd_eq_one (gcd_eq_one_iff_coprime.mpr h) HEq

theorem nat_abs_euclidean_domain_gcd (a b : ℤ) : Int.natAbs (EuclideanDomain.gcd a b) = Int.gcdₓ a b :=
  by 
    apply Nat.dvd_antisymm <;> rw [←Int.coe_nat_dvd]
    ·
      rw [Int.nat_abs_dvd]
      exact Int.dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _)
    ·
      rw [Int.dvd_nat_abs]
      exact EuclideanDomain.dvd_gcd (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)

end Int

-- error in RingTheory.Int.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem irreducible_iff_nat_prime : ∀ a : exprℕ(), «expr ↔ »(irreducible a, nat.prime a)
| 0 := by simp [] [] [] ["[", expr nat.not_prime_zero, "]"] [] []
| 1 := by simp [] [] [] ["[", expr nat.prime, ",", expr one_lt_two, "]"] [] []
| «expr + »(n, 2) := have h₁ : «expr¬ »(«expr = »(«expr + »(n, 2), 1)), from exprdec_trivial(),
begin
  simp [] [] [] ["[", expr h₁, ",", expr nat.prime, ",", expr irreducible_iff, ",", expr («expr ≥ »), ",", expr nat.le_add_left 2 n, ",", expr («expr ∣ »), "]"] [] [],
  refine [expr forall_congr (assume a, «expr $ »(forall_congr, assume b, «expr $ »(forall_congr, assume hab, _)))],
  by_cases [expr «expr = »(a, 1)]; simp [] [] [] ["[", expr h, "]"] [] [],
  split,
  { assume [binders (hb)],
    simpa [] [] [] ["[", expr hb, "]"] [] ["using", expr hab.symm] },
  { assume [binders (ha)],
    subst [expr ha],
    have [] [":", expr «expr > »(«expr + »(n, 2), 0)] [],
    from [expr exprdec_trivial()],
    refine [expr nat.eq_of_mul_eq_mul_left this _],
    rw ["[", "<-", expr hab, ",", expr mul_one, "]"] [] }
end

theorem Nat.prime_iff_prime_int {p : ℕ} : p.prime ↔ _root_.prime (p : ℤ) :=
  ⟨fun hp =>
      ⟨Int.coe_nat_ne_zero_iff_pos.2 hp.pos, mt Int.is_unit_iff_nat_abs_eq.1 hp.ne_one,
        fun a b h =>
          by 
            rw [←Int.dvd_nat_abs, Int.coe_nat_dvd, Int.nat_abs_mul, hp.dvd_mul] at h <;>
              rwa [←Int.dvd_nat_abs, Int.coe_nat_dvd, ←Int.dvd_nat_abs, Int.coe_nat_dvd]⟩,
    fun hp =>
      Nat.prime_iff.2
        ⟨Int.coe_nat_ne_zero.1 hp.1,
          mt Nat.is_unit_iff.1$
            fun h =>
              by 
                simpa [h, not_prime_one] using hp,
          fun a b =>
            by 
              simpa only [Int.coe_nat_dvd, (Int.coe_nat_mul _ _).symm] using hp.2.2 a b⟩⟩

/-- Maps an associate class of integers consisting of `-n, n` to `n : ℕ` -/
def associatesIntEquivNat : Associates ℤ ≃ ℕ :=
  by 
    refine' ⟨fun z => z.out.nat_abs, fun n => Associates.mk n, _, _⟩
    ·
      refine'
        fun a =>
          Quotientₓ.induction_on' a$ fun a => Associates.mk_eq_mk_iff_associated.2$ Associated.symm$ ⟨norm_unit a, _⟩
      show normalize a = Int.natAbs (normalize a)
      rw [Int.coe_nat_abs_eq_normalize, normalize_idem]
    ·
      intro n 
      dsimp 
      rw [Associates.out_mk («expr↑ » n), ←Int.coe_nat_abs_eq_normalize, Int.nat_abs_of_nat, Int.nat_abs_of_nat]

theorem Int.Prime.dvd_mul {m n : ℤ} {p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ m*n) : p ∣ m.nat_abs ∨ p ∣ n.nat_abs :=
  by 
    apply (Nat.Prime.dvd_mul hp).mp 
    rw [←Int.nat_abs_mul]
    exact int.coe_nat_dvd_left.mp h

theorem Int.Prime.dvd_mul' {m n : ℤ} {p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ m*n) : (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n :=
  by 
    rw [Int.coe_nat_dvd_left, Int.coe_nat_dvd_left]
    exact Int.Prime.dvd_mul hp h

theorem Int.Prime.dvd_pow {n : ℤ} {k p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ (n^k)) : p ∣ n.nat_abs :=
  by 
    apply @Nat.Prime.dvd_of_dvd_pow _ _ k hp 
    rw [←Int.nat_abs_pow]
    exact int.coe_nat_dvd_left.mp h

theorem Int.Prime.dvd_pow' {n : ℤ} {k p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ (n^k)) : (p : ℤ) ∣ n :=
  by 
    rw [Int.coe_nat_dvd_left]
    exact Int.Prime.dvd_pow hp h

theorem prime_two_or_dvd_of_dvd_two_mul_pow_self_two {m : ℤ} {p : ℕ} (hp : Nat.Prime p) (h : (p : ℤ) ∣ 2*m^2) :
  p = 2 ∨ p ∣ Int.natAbs m :=
  by 
    cases' Int.Prime.dvd_mul hp h with hp2 hpp
    ·
      apply Or.intro_left 
      exact le_antisymmₓ (Nat.le_of_dvdₓ zero_lt_two hp2) (Nat.Prime.two_le hp)
    ·
      apply Or.intro_rightₓ 
      rw [sq, Int.nat_abs_mul] at hpp 
      exact (or_selfₓ _).mp ((Nat.Prime.dvd_mul hp).mp hpp)

open UniqueFactorizationMonoid

theorem Nat.factors_eq {n : ℕ} : normalized_factors n = n.factors :=
  by 
    cases n
    ·
      simp 
    rw [←Multiset.rel_eq, ←associated_eq_eq]
    apply factors_unique irreducible_of_normalized_factor _
    ·
      rw [Multiset.coe_prod, Nat.prod_factors (Nat.succ_posₓ _)]
      apply normalized_factors_prod (Nat.succ_ne_zero _)
    ·
      infer_instance
    ·
      intro x hx 
      rw [Nat.irreducible_iff_prime, ←Nat.prime_iff]
      exact Nat.prime_of_mem_factors hx

theorem Nat.factors_multiset_prod_of_irreducible {s : Multiset ℕ} (h : ∀ x : ℕ, x ∈ s → Irreducible x) :
  normalized_factors s.prod = s :=
  by 
    rw [←Multiset.rel_eq, ←associated_eq_eq]
    apply UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor h (normalized_factors_prod _)
    rw [Ne.def, Multiset.prod_eq_zero_iff]
    intro con 
    exact not_irreducible_zero (h 0 Con)

namespace multiplicity

theorem finite_int_iff_nat_abs_finite {a b : ℤ} : finite a b ↔ finite a.nat_abs b.nat_abs :=
  by 
    simp only [finite_def, ←Int.nat_abs_dvd_abs_iff, Int.nat_abs_pow]

theorem finite_int_iff {a b : ℤ} : finite a b ↔ a.nat_abs ≠ 1 ∧ b ≠ 0 :=
  by 
    rw [finite_int_iff_nat_abs_finite, finite_nat_iff, pos_iff_ne_zero, Int.nat_abs_ne_zero]

instance decidable_nat : DecidableRel fun a b : ℕ => (multiplicity a b).Dom :=
  fun a b => decidableOfIff _ finite_nat_iff.symm

instance decidable_int : DecidableRel fun a b : ℤ => (multiplicity a b).Dom :=
  fun a b => decidableOfIff _ finite_int_iff.symm

end multiplicity

theorem induction_on_primes {P : ℕ → Prop} (h₀ : P 0) (h₁ : P 1) (h : ∀ p a : ℕ, p.prime → P a → P (p*a)) (n : ℕ) :
  P n :=
  by 
    apply UniqueFactorizationMonoid.induction_on_prime 
    exact h₀
    ·
      intro n h 
      rw [Nat.is_unit_iff.1 h]
      exact h₁
    ·
      intro a p _ hp ha 
      exact h p a (Nat.prime_iff.2 hp) ha

theorem Int.associated_nat_abs (k : ℤ) : Associated k k.nat_abs :=
  associated_of_dvd_dvd (Int.coe_nat_dvd_right.mpr dvd_rfl) (Int.nat_abs_dvd.mpr dvd_rfl)

theorem Int.prime_iff_nat_abs_prime {k : ℤ} : Prime k ↔ Nat.Prime k.nat_abs :=
  (Int.associated_nat_abs k).prime_iff.trans Nat.prime_iff_prime_int.symm

theorem Int.associated_iff_nat_abs {a b : ℤ} : Associated a b ↔ a.nat_abs = b.nat_abs :=
  by 
    rw [←dvd_dvd_iff_associated, ←Int.nat_abs_dvd_abs_iff, ←Int.nat_abs_dvd_abs_iff, dvd_dvd_iff_associated]
    exact associated_iff_eq

theorem Int.associated_iff {a b : ℤ} : Associated a b ↔ a = b ∨ a = -b :=
  by 
    rw [Int.associated_iff_nat_abs]
    exact Int.nat_abs_eq_nat_abs_iff

namespace Int

theorem zmultiples_nat_abs (a : ℤ) : AddSubgroup.zmultiples (a.nat_abs : ℤ) = AddSubgroup.zmultiples a :=
  le_antisymmₓ (AddSubgroup.zmultiples_subset (mem_zmultiples_iff.mpr (dvd_nat_abs.mpr (dvd_refl a))))
    (AddSubgroup.zmultiples_subset (mem_zmultiples_iff.mpr (nat_abs_dvd.mpr (dvd_refl a))))

theorem span_nat_abs (a : ℤ) : Ideal.span ({a.nat_abs} : Set ℤ) = Ideal.span {a} :=
  by 
    rw [Ideal.span_singleton_eq_span_singleton]
    exact (associated_nat_abs _).symm

end Int

