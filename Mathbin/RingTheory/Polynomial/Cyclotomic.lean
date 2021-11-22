import Mathbin.Algebra.Polynomial.BigOperators 
import Mathbin.Analysis.Complex.RootsOfUnity 
import Mathbin.Data.Polynomial.Lifts 
import Mathbin.FieldTheory.Separable 
import Mathbin.FieldTheory.SplittingField 
import Mathbin.NumberTheory.ArithmeticFunction 
import Mathbin.RingTheory.RootsOfUnity

/-!
# Cyclotomic polynomials.

For `n : ℕ` and an integral domain `R`, we define a modified version of the `n`-th cyclotomic
polynomial with coefficients in `R`, denoted `cyclotomic' n R`, as `∏ (X - μ)`, where `μ` varies
over the primitive `n`th roots of unity. If there is a primitive `n`th root of unity in `R` then
this the standard definition. We then define the standard cyclotomic polynomial `cyclotomic n R`
with coefficients in any ring `R`.

## Main definition

* `cyclotomic n R` : the `n`-th cyclotomic polynomial with coefficients in `R`.

## Main results

* `int_coeff_of_cycl` : If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K`
comes from a polynomial with integer coefficients.
* `deg_of_cyclotomic` : The degree of `cyclotomic n` is `totient n`.
* `prod_cyclotomic_eq_X_pow_sub_one` : `X ^ n - 1 = ∏ (cyclotomic i)`, where `i` divides `n`.
* `cyclotomic_eq_prod_X_pow_sub_one_pow_moebius` : The Möbius inversion formula for
  `cyclotomic n R` over an abstract fraction field for `polynomial R`.
* `cyclotomic.irreducible` : `cyclotomic n ℤ` is irreducible.

## Implementation details

Our definition of `cyclotomic' n R` makes sense in any integral domain `R`, but the interesting
results hold if there is a primitive `n`-th root of unity in `R`. In particular, our definition is
not the standard one unless there is a primitive `n`th root of unity in `R`. For example,
`cyclotomic' 3 ℤ = 1`, since there are no primitive cube roots of unity in `ℤ`. The main example is
`R = ℂ`, we decided to work in general since the difficulties are essentially the same.
To get the standard cyclotomic polynomials, we use `int_coeff_of_cycl`, with `R = ℂ`, to get a
polynomial with integer coefficients and then we map it to `polynomial R`, for any ring `R`.
To prove `cyclotomic.irreducible`, the irreducibility of `cyclotomic n ℤ`, we show in
`cyclotomic_eq_minpoly` that `cyclotomic n ℤ` is the minimal polynomial of any `n`-th primitive root
of unity `μ : K`, where `K` is a field of characteristic `0`.
-/


open_locale Classical BigOperators

noncomputable theory

universe u

namespace Polynomial

section Cyclotomic'

section IsDomain

variable{R : Type _}[CommRingₓ R][IsDomain R]

/-- The modified `n`-th cyclotomic polynomial with coefficients in `R`, it is the usual cyclotomic
polynomial if there is a primitive `n`-th root of unity in `R`. -/
def cyclotomic' (n : ℕ) (R : Type _) [CommRingₓ R] [IsDomain R] : Polynomial R :=
  ∏μ in primitiveRoots n R, X - C μ

/-- The zeroth modified cyclotomic polyomial is `1`. -/
@[simp]
theorem cyclotomic'_zero (R : Type _) [CommRingₓ R] [IsDomain R] : cyclotomic' 0 R = 1 :=
  by 
    simp only [cyclotomic', Finset.prod_empty, IsPrimitiveRoot.primitive_roots_zero]

/-- The first modified cyclotomic polyomial is `X - 1`. -/
@[simp]
theorem cyclotomic'_one (R : Type _) [CommRingₓ R] [IsDomain R] : cyclotomic' 1 R = X - 1 :=
  by 
    simp only [cyclotomic', Finset.prod_singleton, RingHom.map_one, IsPrimitiveRoot.primitive_roots_one]

/-- The second modified cyclotomic polyomial is `X + 1` if the characteristic of `R` is not `2`. -/
@[simp]
theorem cyclotomic'_two (R : Type _) [CommRingₓ R] [IsDomain R] (p : ℕ) [CharP R p] (hp : p ≠ 2) :
  cyclotomic' 2 R = X+1 :=
  by 
    rw [cyclotomic']
    have prim_root_two : primitiveRoots 2 R = {(-1 : R)}
    ·
      apply Finset.eq_singleton_iff_unique_mem.2
      split 
      ·
        simp only [IsPrimitiveRoot.neg_one p hp, Nat.succ_pos', mem_primitive_roots]
      ·
        intro x hx 
        rw [mem_primitive_roots zero_lt_two] at hx 
        exact IsPrimitiveRoot.eq_neg_one_of_two_right hx 
    simp only [prim_root_two, Finset.prod_singleton, RingHom.map_neg, RingHom.map_one, sub_neg_eq_add]

/-- `cyclotomic' n R` is monic. -/
theorem cyclotomic'.monic (n : ℕ) (R : Type _) [CommRingₓ R] [IsDomain R] : (cyclotomic' n R).Monic :=
  monic_prod_of_monic _ _$ fun z hz => monic_X_sub_C _

/-- `cyclotomic' n R` is different from `0`. -/
theorem cyclotomic'_ne_zero (n : ℕ) (R : Type _) [CommRingₓ R] [IsDomain R] : cyclotomic' n R ≠ 0 :=
  (cyclotomic'.monic n R).ne_zero

/-- The natural degree of `cyclotomic' n R` is `totient n` if there is a primitive root of
unity in `R`. -/
theorem nat_degree_cyclotomic' {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
  (cyclotomic' n R).natDegree = Nat.totient n :=
  by 
    cases' Nat.eq_zero_or_posₓ n with hzero hpos
    ·
      simp only [hzero, cyclotomic'_zero, Nat.totient_zero, nat_degree_one]
    rw [cyclotomic']
    rw [nat_degree_prod (primitiveRoots n R) fun z : R => X - C z]
    simp only [IsPrimitiveRoot.card_primitive_roots h hpos, mul_oneₓ, nat_degree_X_sub_C, Nat.cast_id, Finset.sum_const,
      nsmul_eq_mul]
    intro z hz 
    exact X_sub_C_ne_zero z

/-- The degree of `cyclotomic' n R` is `totient n` if there is a primitive root of unity in `R`. -/
theorem degree_cyclotomic' {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) : (cyclotomic' n R).degree = Nat.totient n :=
  by 
    simp only [degree_eq_nat_degree (cyclotomic'_ne_zero n R), nat_degree_cyclotomic' h]

/-- The roots of `cyclotomic' n R` are the primitive `n`-th roots of unity. -/
theorem roots_of_cyclotomic (n : ℕ) (R : Type _) [CommRingₓ R] [IsDomain R] :
  (cyclotomic' n R).roots = (primitiveRoots n R).val :=
  by 
    rw [cyclotomic']
    exact roots_prod_X_sub_C (primitiveRoots n R)

end IsDomain

section Field

variable{K : Type _}[Field K]

/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - 1 = ∏ (X - μ)`, where `μ`
varies over the `n`-th roots of unity. -/
theorem X_pow_sub_one_eq_prod {ζ : K} {n : ℕ} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
  (X^n) - 1 = ∏ζ in nth_roots_finset n K, X - C ζ :=
  by 
    rw [nth_roots_finset, ←Multiset.to_finset_eq (IsPrimitiveRoot.nth_roots_nodup h)]
    simp only [Finset.prod_mk, RingHom.map_one]
    rw [nth_roots]
    have hmonic : ((X^n) - C (1 : K)).Monic := monic_X_pow_sub_C (1 : K) (ne_of_ltₓ hpos).symm 
    symm 
    apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic 
    rw [@nat_degree_X_pow_sub_C K _ _ n 1, ←nth_roots]
    exact IsPrimitiveRoot.card_nth_roots h

/-- `cyclotomic' n K` splits. -/
theorem cyclotomic'_splits (n : ℕ) : splits (RingHom.id K) (cyclotomic' n K) :=
  by 
    apply splits_prod (RingHom.id K)
    intro z hz 
    simp only [splits_X_sub_C (RingHom.id K)]

/-- If there is a primitive `n`-th root of unity in `K`, then `X ^ n - 1`splits. -/
theorem X_pow_sub_one_splits {ζ : K} {n : ℕ} (h : IsPrimitiveRoot ζ n) : splits (RingHom.id K) ((X^n) - C (1 : K)) :=
  by 
    byCases' hzero : n = 0
    ·
      simp only [hzero, RingHom.map_one, splits_zero, pow_zeroₓ, sub_self]
    rw [splits_iff_card_roots, ←nth_roots, IsPrimitiveRoot.card_nth_roots h, nat_degree_X_pow_sub_C]

/-- If there is a primitive `n`-th root of unity in `K`, then
`∏ i in nat.divisors n, cyclotomic' i K = X ^ n - 1`. -/
theorem prod_cyclotomic'_eq_X_pow_sub_one {ζ : K} {n : ℕ} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
  (∏i in Nat.divisors n, cyclotomic' i K) = (X^n) - 1 :=
  by 
    rw [X_pow_sub_one_eq_prod hpos h]
    have rwcyc : ∀ i _ : i ∈ Nat.divisors n, cyclotomic' i K = ∏μ in primitiveRoots i K, X - C μ
    ·
      intro i hi 
      simp only [cyclotomic']
    convLHS => applyCongr skip simp [rwcyc, H]
    rw [←Finset.prod_bUnion]
    ·
      simp only [IsPrimitiveRoot.nth_roots_one_eq_bUnion_primitive_roots hpos h]
    intro x hx y hy hdiff 
    rw [Finset.mem_coe] at hx hy 
    exact IsPrimitiveRoot.disjoint (Nat.pos_of_mem_divisors hx) (Nat.pos_of_mem_divisors hy) hdiff

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic' n K = (X ^ k - 1) /ₘ (∏ i in nat.proper_divisors k, cyclotomic' i K)`. -/
theorem cyclotomic'_eq_X_pow_sub_one_div {ζ : K} {n : ℕ} (hpos : 0 < n) (h : IsPrimitiveRoot ζ n) :
  cyclotomic' n K = ((X^n) - 1) /ₘ ∏i in Nat.properDivisors n, cyclotomic' i K :=
  by 
    rw [←prod_cyclotomic'_eq_X_pow_sub_one hpos h, Nat.divisors_eq_proper_divisors_insert_self_of_pos hpos,
      Finset.prod_insert Nat.properDivisors.not_self_mem]
    have prod_monic : (∏i in Nat.properDivisors n, cyclotomic' i K).Monic
    ·
      apply monic_prod_of_monic 
      intro i hi 
      exact cyclotomic'.monic i K 
    rw [(div_mod_by_monic_unique (cyclotomic' n K) 0 prod_monic _).1]
    simp only [degree_zero, zero_addₓ]
    refine'
      ⟨by 
          rw [mul_commₓ],
        _⟩
    rw [bot_lt_iff_ne_bot]
    intro h 
    exact monic.ne_zero prod_monic (degree_eq_bot.1 h)

/-- If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K` comes from a
monic polynomial with integer coefficients. -/
theorem int_coeff_of_cyclotomic' {ζ : K} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
  ∃ P : Polynomial ℤ, map (Int.castRingHom K) P = cyclotomic' n K ∧ P.degree = (cyclotomic' n K).degree ∧ P.monic :=
  by 
    refine' lifts_and_degree_eq_and_monic _ (cyclotomic'.monic n K)
    induction' n using Nat.strong_induction_onₓ with k hk generalizing ζ h 
    cases' Nat.eq_zero_or_posₓ k with hzero hpos
    ·
      use 1
      simp only [hzero, cyclotomic'_zero, Set.mem_univ, Subsemiring.coe_top, eq_self_iff_true, coe_map_ring_hom,
        map_one, and_selfₓ]
    byCases' hone : k = 1
    ·
      use X - 1
      simp only [hone, cyclotomic'_one K, Set.mem_univ, Pnat.one_coe, Subsemiring.coe_top, eq_self_iff_true, map_X,
        coe_map_ring_hom, map_one, and_selfₓ, map_sub]
    let B : Polynomial K := ∏i in Nat.properDivisors k, cyclotomic' i K 
    have Bmo : B.monic
    ·
      apply monic_prod_of_monic 
      intro i hi 
      exact cyclotomic'.monic i K 
    have Bint : B ∈ lifts (Int.castRingHom K)
    ·
      refine' Subsemiring.prod_mem (lifts (Int.castRingHom K)) _ 
      intro x hx 
      have xsmall := (Nat.mem_proper_divisors.1 hx).2
      obtain ⟨d, hd⟩ := (Nat.mem_proper_divisors.1 hx).1
      rw [mul_commₓ] at hd 
      exact hk x xsmall (IsPrimitiveRoot.pow hpos h hd)
    replace Bint := lifts_and_degree_eq_and_monic Bint Bmo 
    obtain ⟨B₁, hB₁, hB₁deg, hB₁mo⟩ := Bint 
    let Q₁ : Polynomial ℤ := ((X^k) - 1) /ₘ B₁ 
    have huniq : (0+B*cyclotomic' k K) = (X^k) - 1 ∧ (0 : Polynomial K).degree < B.degree
    ·
      split 
      ·
        rw [zero_addₓ, mul_commₓ, ←prod_cyclotomic'_eq_X_pow_sub_one hpos h,
          Nat.divisors_eq_proper_divisors_insert_self_of_pos hpos]
        simp only [true_andₓ, Finset.prod_insert, not_ltₓ, Nat.mem_proper_divisors, dvd_refl]
      rw [degree_zero, bot_lt_iff_ne_bot]
      intro habs 
      exact (monic.ne_zero Bmo) (degree_eq_bot.1 habs)
    replace huniq := div_mod_by_monic_unique (cyclotomic' k K) (0 : Polynomial K) Bmo huniq 
    simp only [lifts, RingHom.mem_srange]
    use Q₁ 
    rw [coe_map_ring_hom, map_div_by_monic (Int.castRingHom K) hB₁mo, hB₁, ←huniq.1]
    simp 

/-- If `K` is of characteristic `0` and there is a primitive `n`-th root of unity in `K`,
then `cyclotomic n K` comes from a unique polynomial with integer coefficients. -/
theorem unique_int_coeff_of_cycl [CharZero K] {ζ : K} {n : ℕ+} (h : IsPrimitiveRoot ζ n) :
  ∃!P : Polynomial ℤ, map (Int.castRingHom K) P = cyclotomic' n K :=
  by 
    obtain ⟨P, hP⟩ := int_coeff_of_cyclotomic' h 
    refine' ⟨P, hP.1, fun Q hQ => _⟩
    apply map_injective (Int.castRingHom K) Int.cast_injective 
    rw [hP.1, hQ]

end Field

end Cyclotomic'

section Cyclotomic

/-- The `n`-th cyclotomic polynomial with coefficients in `R`. -/
def cyclotomic (n : ℕ) (R : Type _) [Ringₓ R] : Polynomial R :=
  if h : n = 0 then 1 else map (Int.castRingHom R) (int_coeff_of_cyclotomic' (Complex.is_primitive_root_exp n h)).some

theorem int_cyclotomic_rw {n : ℕ} (h : n ≠ 0) :
  cyclotomic n ℤ = (int_coeff_of_cyclotomic' (Complex.is_primitive_root_exp n h)).some :=
  by 
    simp only [cyclotomic, h, dif_neg, not_false_iff]
    ext i 
    simp only [coeff_map, Int.cast_id, RingHom.eq_int_cast]

/-- `cyclotomic n R` comes from `cyclotomic n ℤ`. -/
theorem map_cyclotomic_int (n : ℕ) (R : Type _) [Ringₓ R] : map (Int.castRingHom R) (cyclotomic n ℤ) = cyclotomic n R :=
  by 
    byCases' hzero : n = 0
    ·
      simp only [hzero, cyclotomic, dif_pos, map_one]
    simp only [cyclotomic, int_cyclotomic_rw, hzero, Ne.def, dif_neg, not_false_iff]

theorem int_cyclotomic_spec (n : ℕ) :
  map (Int.castRingHom ℂ) (cyclotomic n ℤ) = cyclotomic' n ℂ ∧
    (cyclotomic n ℤ).degree = (cyclotomic' n ℂ).degree ∧ (cyclotomic n ℤ).Monic :=
  by 
    byCases' hzero : n = 0
    ·
      simp only [hzero, cyclotomic, degree_one, monic_one, cyclotomic'_zero, dif_pos, eq_self_iff_true, map_one,
        and_selfₓ]
    rw [int_cyclotomic_rw hzero]
    exact (int_coeff_of_cyclotomic' (Complex.is_primitive_root_exp n hzero)).some_spec

theorem int_cyclotomic_unique {n : ℕ} {P : Polynomial ℤ} (h : map (Int.castRingHom ℂ) P = cyclotomic' n ℂ) :
  P = cyclotomic n ℤ :=
  by 
    apply map_injective (Int.castRingHom ℂ) Int.cast_injective 
    rw [h, (int_cyclotomic_spec n).1]

/-- The definition of `cyclotomic n R` commutes with any ring homomorphism. -/
@[simp]
theorem map_cyclotomic (n : ℕ) {R S : Type _} [Ringₓ R] [Ringₓ S] (f : R →+* S) :
  map f (cyclotomic n R) = cyclotomic n S :=
  by 
    rw [←map_cyclotomic_int n R, ←map_cyclotomic_int n S]
    ext i 
    simp only [coeff_map, RingHom.eq_int_cast, RingHom.map_int_cast]

/-- The zeroth cyclotomic polyomial is `1`. -/
@[simp]
theorem cyclotomic_zero (R : Type _) [Ringₓ R] : cyclotomic 0 R = 1 :=
  by 
    simp only [cyclotomic, dif_pos]

/-- The first cyclotomic polyomial is `X - 1`. -/
@[simp]
theorem cyclotomic_one (R : Type _) [Ringₓ R] : cyclotomic 1 R = X - 1 :=
  by 
    have hspec : map (Int.castRingHom ℂ) (X - 1) = cyclotomic' 1 ℂ
    ·
      simp only [cyclotomic'_one, Pnat.one_coe, map_X, map_one, map_sub]
    symm 
    rw [←map_cyclotomic_int, ←int_cyclotomic_unique hspec]
    simp only [map_X, map_one, map_sub]

/-- The second cyclotomic polyomial is `X + 1`. -/
@[simp]
theorem cyclotomic_two (R : Type _) [Ringₓ R] : cyclotomic 2 R = X+1 :=
  by 
    have hspec : map (Int.castRingHom ℂ) (X+1) = cyclotomic' 2 ℂ
    ·
      simp only [cyclotomic'_two ℂ 0 two_ne_zero.symm, map_add, map_X, map_one]
    symm 
    rw [←map_cyclotomic_int, ←int_cyclotomic_unique hspec]
    simp only [map_add, map_X, map_one]

/-- `cyclotomic n` is monic. -/
theorem cyclotomic.monic (n : ℕ) (R : Type _) [Ringₓ R] : (cyclotomic n R).Monic :=
  by 
    rw [←map_cyclotomic_int]
    apply monic_map 
    exact (int_cyclotomic_spec n).2.2

/-- `cyclotomic n R` is different from `0`. -/
theorem cyclotomic_ne_zero (n : ℕ) (R : Type _) [Ringₓ R] [Nontrivial R] : cyclotomic n R ≠ 0 :=
  monic.ne_zero (cyclotomic.monic n R)

/-- The degree of `cyclotomic n` is `totient n`. -/
theorem degree_cyclotomic (n : ℕ) (R : Type _) [Ringₓ R] [Nontrivial R] : (cyclotomic n R).degree = Nat.totient n :=
  by 
    rw [←map_cyclotomic_int]
    rw [degree_map_eq_of_leading_coeff_ne_zero (Int.castRingHom R) _]
    ·
      cases' n with k
      ·
        simp only [cyclotomic, degree_one, dif_pos, Nat.totient_zero, WithTop.coe_zero]
      rw [←degree_cyclotomic' (Complex.is_primitive_root_exp k.succ (Nat.succ_ne_zero k))]
      exact (int_cyclotomic_spec k.succ).2.1
    simp only [(int_cyclotomic_spec n).right.right, RingHom.eq_int_cast, monic.leading_coeff, Int.cast_one, Ne.def,
      not_false_iff, one_ne_zero]

/-- The natural degree of `cyclotomic n` is `totient n`. -/
theorem nat_degree_cyclotomic (n : ℕ) (R : Type _) [Ringₓ R] [Nontrivial R] :
  (cyclotomic n R).natDegree = Nat.totient n :=
  by 
    have hdeg := degree_cyclotomic n R 
    rw [degree_eq_nat_degree (cyclotomic_ne_zero n R)] at hdeg 
    exactModCast hdeg

/-- The degree of `cyclotomic n R` is positive. -/
theorem degree_cyclotomic_pos (n : ℕ) (R : Type _) (hpos : 0 < n) [Ringₓ R] [Nontrivial R] :
  0 < (cyclotomic n R).degree :=
  by 
    rw [degree_cyclotomic n R]
    exactModCast Nat.totient_pos hpos

/-- `∏ i in nat.divisors n, cyclotomic i R = X ^ n - 1`. -/
theorem prod_cyclotomic_eq_X_pow_sub_one {n : ℕ} (hpos : 0 < n) (R : Type _) [CommRingₓ R] :
  (∏i in Nat.divisors n, cyclotomic i R) = (X^n) - 1 :=
  by 
    have integer : (∏i in Nat.divisors n, cyclotomic i ℤ) = (X^n) - 1
    ·
      apply map_injective (Int.castRingHom ℂ) Int.cast_injective 
      rw [map_prod (Int.castRingHom ℂ) fun i => cyclotomic i ℤ]
      simp only [int_cyclotomic_spec, map_pow, Nat.cast_id, map_X, map_one, map_sub]
      exact prod_cyclotomic'_eq_X_pow_sub_one hpos (Complex.is_primitive_root_exp n (ne_of_ltₓ hpos).symm)
    have coerc : (X^n) - 1 = map (Int.castRingHom R) ((X^n) - 1)
    ·
      simp only [map_pow, map_X, map_one, map_sub]
    have h : ∀ i _ : i ∈ n.divisors, cyclotomic i R = map (Int.castRingHom R) (cyclotomic i ℤ)
    ·
      intro i hi 
      exact (map_cyclotomic_int i R).symm 
    rw [Finset.prod_congr (refl n.divisors) h, coerc, ←map_prod (Int.castRingHom R) fun i => cyclotomic i ℤ, integer]

section ArithmeticFunction

open Nat.ArithmeticFunction

open_locale ArithmeticFunction

/-- `cyclotomic n R` can be expressed as a product in a fraction field of `polynomial R`
  using Möbius inversion. -/
theorem cyclotomic_eq_prod_X_pow_sub_one_pow_moebius {n : ℕ} (hpos : 0 < n) (R : Type _) [CommRingₓ R] [Nontrivial R]
  {K : Type _} [Field K] [Algebra (Polynomial R) K] [IsFractionRing (Polynomial R) K] :
  algebraMap _ K (cyclotomic n R) =
    ∏i in n.divisors_antidiagonal, algebraMap (Polynomial R) K ((X^i.snd) - 1)^μ i.fst :=
  by 
    have h : ∀ n : ℕ, 0 < n → (∏i in Nat.divisors n, algebraMap _ K (cyclotomic i R)) = algebraMap _ _ ((X^n) - 1)
    ·
      intro n hn 
      rw [←prod_cyclotomic_eq_X_pow_sub_one hn R, RingHom.map_prod]
    rw [(prod_eq_iff_prod_pow_moebius_eq_of_nonzero (fun n hn => _) fun n hn => _).1 h n hpos] <;>
      rw [Ne.def, IsFractionRing.to_map_eq_zero_iff]
    ·
      apply cyclotomic_ne_zero
    ·
      apply monic.ne_zero 
      apply monic_X_pow_sub_C _ (ne_of_gtₓ hn)

end ArithmeticFunction

/-- We have
`cyclotomic n R = (X ^ k - 1) /ₘ (∏ i in nat.proper_divisors k, cyclotomic i K)`. -/
theorem cyclotomic_eq_X_pow_sub_one_div {R : Type _} [CommRingₓ R] {n : ℕ} (hpos : 0 < n) :
  cyclotomic n R = ((X^n) - 1) /ₘ ∏i in Nat.properDivisors n, cyclotomic i R :=
  by 
    nontriviality R 
    rw [←prod_cyclotomic_eq_X_pow_sub_one hpos, Nat.divisors_eq_proper_divisors_insert_self_of_pos hpos,
      Finset.prod_insert Nat.properDivisors.not_self_mem]
    have prod_monic : (∏i in Nat.properDivisors n, cyclotomic i R).Monic
    ·
      apply monic_prod_of_monic 
      intro i hi 
      exact cyclotomic.monic i R 
    rw [(div_mod_by_monic_unique (cyclotomic n R) 0 prod_monic _).1]
    simp only [degree_zero, zero_addₓ]
    split 
    ·
      rw [mul_commₓ]
    rw [bot_lt_iff_ne_bot]
    intro h 
    exact monic.ne_zero prod_monic (degree_eq_bot.1 h)

/-- If `m` is a proper divisor of `n`, then `X ^ m - 1` divides
`∏ i in nat.proper_divisors n, cyclotomic i R`. -/
theorem X_pow_sub_one_dvd_prod_cyclotomic (R : Type _) [CommRingₓ R] {n m : ℕ} (hpos : 0 < n) (hm : m ∣ n)
  (hdiff : m ≠ n) : (X^m) - 1 ∣ ∏i in Nat.properDivisors n, cyclotomic i R :=
  by 
    replace hm :=
      Nat.mem_proper_divisors.2
        ⟨hm, lt_of_le_of_neₓ (Nat.divisor_le (Nat.mem_divisors.2 ⟨hm, (ne_of_ltₓ hpos).symm⟩)) hdiff⟩
    rw
      [←Finset.sdiff_union_of_subset
        (Nat.divisors_subset_proper_divisors (ne_of_ltₓ hpos).symm (Nat.mem_proper_divisors.1 hm).1
          (ne_of_ltₓ (Nat.mem_proper_divisors.1 hm).2)),
      Finset.prod_union Finset.sdiff_disjoint, prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_mem_proper_divisors hm)]
    exact
      ⟨∏x : ℕ in n.proper_divisors \ m.divisors, cyclotomic x R,
        by 
          rw [mul_commₓ]⟩

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic n K = ∏ μ in primitive_roots n R, (X - C μ)`. In particular,
`cyclotomic n K = cyclotomic' n K` -/
theorem cyclotomic_eq_prod_X_sub_primitive_roots {K : Type _} [Field K] {ζ : K} {n : ℕ} (hz : IsPrimitiveRoot ζ n) :
  cyclotomic n K = ∏μ in primitiveRoots n K, X - C μ :=
  by 
    rw [←cyclotomic']
    induction' n using Nat.strong_induction_onₓ with k hk generalizing ζ hz 
    obtain hzero | hpos := k.eq_zero_or_pos
    ·
      simp only [hzero, cyclotomic'_zero, cyclotomic_zero]
    have h : ∀ i _ : i ∈ k.proper_divisors, cyclotomic i K = cyclotomic' i K
    ·
      intro i hi 
      obtain ⟨d, hd⟩ := (Nat.mem_proper_divisors.1 hi).1
      rw [mul_commₓ] at hd 
      exact hk i (Nat.mem_proper_divisors.1 hi).2 (IsPrimitiveRoot.pow hpos hz hd)
    rw [@cyclotomic_eq_X_pow_sub_one_div _ _ _ hpos, cyclotomic'_eq_X_pow_sub_one_div hpos hz,
      Finset.prod_congr (refl k.proper_divisors) h]

/-- Any `n`-th primitive root of unity is a root of `cyclotomic n ℤ`.-/
theorem is_root_cyclotomic {n : ℕ} {K : Type _} [Field K] (hpos : 0 < n) {μ : K} (h : IsPrimitiveRoot μ n) :
  is_root (cyclotomic n K) μ :=
  by 
    rw [←mem_roots (cyclotomic_ne_zero n K), cyclotomic_eq_prod_X_sub_primitive_roots h, roots_prod_X_sub_C,
      ←Finset.mem_def]
    rwa [←mem_primitive_roots hpos] at h

theorem eq_cyclotomic_iff {R : Type _} [CommRingₓ R] {n : ℕ} (hpos : 0 < n) (P : Polynomial R) :
  P = cyclotomic n R ↔ (P*∏i in Nat.properDivisors n, Polynomial.cyclotomic i R) = (X^n) - 1 :=
  by 
    nontriviality R 
    refine' ⟨fun hcycl => _, fun hP => _⟩
    ·
      rw [hcycl, ←Finset.prod_insert (@Nat.properDivisors.not_self_mem n),
        ←Nat.divisors_eq_proper_divisors_insert_self_of_pos hpos]
      exact prod_cyclotomic_eq_X_pow_sub_one hpos R
    ·
      have prod_monic : (∏i in Nat.properDivisors n, cyclotomic i R).Monic
      ·
        apply monic_prod_of_monic 
        intro i hi 
        exact cyclotomic.monic i R 
      rw [@cyclotomic_eq_X_pow_sub_one_div R _ _ hpos, (div_mod_by_monic_unique P 0 prod_monic _).1]
      refine'
        ⟨by 
            rwa [zero_addₓ, mul_commₓ],
          _⟩
      rw [degree_zero, bot_lt_iff_ne_bot]
      intro h 
      exact monic.ne_zero prod_monic (degree_eq_bot.1 h)

/-- If `p` is prime, then `cyclotomic p R = geom_sum X p`. -/
theorem cyclotomic_eq_geom_sum {R : Type _} [CommRingₓ R] {p : ℕ} (hp : Nat.Prime p) : cyclotomic p R = geomSum X p :=
  by 
    refine' ((eq_cyclotomic_iff hp.pos _).mpr _).symm 
    simp only [Nat.Prime.proper_divisors hp, geom_sum_mul, Finset.prod_singleton, cyclotomic_one]

/-- If `p ^ k` is prime power, then `cyclotomic (p ^ (n + 1)) R = geom_sum (X ^ p ^ n) p`. -/
theorem cyclotomic_prime_pow_eq_geom_sum {R : Type _} [CommRingₓ R] {p n : ℕ} (hp : Nat.Prime p) :
  cyclotomic (p^n+1) R = geomSum (X^p^n) p :=
  by 
    have  :
      ∀ m,
        cyclotomic (p^m+1) R = geomSum (X^p^m) p ↔
          (geomSum (X^p^m) p*∏x : ℕ in Finset.range (m+1), cyclotomic (p^x) R) = (X^p^m+1) - 1
    ·
      intro m 
      have  := eq_cyclotomic_iff (pow_pos hp.pos (m+1)) _ 
      rw [eq_comm] at this 
      rw [this, Nat.prod_proper_divisors_prime_pow hp]
    induction' n with n_n n_ih
    ·
      simp [cyclotomic_eq_geom_sum hp]
    rw [((eq_cyclotomic_iff (pow_pos hp.pos (n_n.succ+1)) _).mpr _).symm]
    rw [Nat.prod_proper_divisors_prime_pow hp, Finset.prod_range_succ, n_ih]
    rw [this] at n_ih 
    rw [mul_commₓ _ (geomSum _ _), n_ih, geom_sum_mul, sub_left_inj, ←pow_mulₓ, pow_addₓ, pow_oneₓ]

/-- The constant term of `cyclotomic n R` is `1` if `2 ≤ n`. -/
theorem cyclotomic_coeff_zero (R : Type _) [CommRingₓ R] {n : ℕ} (hn : 2 ≤ n) : (cyclotomic n R).coeff 0 = 1 :=
  by 
    induction' n using Nat.strong_induction_onₓ with n hi 
    have hprod : (∏i in Nat.properDivisors n, (Polynomial.cyclotomic i R).coeff 0) = -1
    ·
      rw [←Finset.insert_erase (Nat.one_mem_proper_divisors_iff_one_lt.2 (lt_of_lt_of_leₓ one_lt_two hn)),
        Finset.prod_insert (Finset.not_mem_erase 1 _), cyclotomic_one R]
      have hleq : ∀ j _ : j ∈ n.proper_divisors.erase 1, 2 ≤ j
      ·
        intro j hj 
        apply Nat.succ_le_of_ltₓ 
        exact
          (Ne.le_iff_lt (Finset.mem_erase.1 hj).1.symm).mp
            (Nat.succ_le_of_ltₓ (Nat.pos_of_mem_proper_divisors (Finset.mem_erase.1 hj).2))
      have hcongr : ∀ j _ : j ∈ n.proper_divisors.erase 1, (cyclotomic j R).coeff 0 = 1
      ·
        intro j hj 
        exact hi j (Nat.mem_proper_divisors.1 (Finset.mem_erase.1 hj).2).2 (hleq j hj)
      have hrw : (∏x : ℕ in n.proper_divisors.erase 1, (cyclotomic x R).coeff 0) = 1
      ·
        rw [Finset.prod_congr (refl (n.proper_divisors.erase 1)) hcongr]
        simp only [Finset.prod_const_one]
      simp only [hrw, mul_oneₓ, zero_sub, coeff_one_zero, coeff_X_zero, coeff_sub]
    have heq : ((X^n) - 1).coeff 0 = -(cyclotomic n R).coeff 0
    ·
      rw [←prod_cyclotomic_eq_X_pow_sub_one (lt_of_lt_of_leₓ zero_lt_two hn),
        Nat.divisors_eq_proper_divisors_insert_self_of_pos (lt_of_lt_of_leₓ zero_lt_two hn),
        Finset.prod_insert Nat.properDivisors.not_self_mem, mul_coeff_zero, coeff_zero_prod, hprod,
        mul_neg_eq_neg_mul_symm, mul_oneₓ]
    have hzero : ((X^n) - 1).coeff 0 = (-1 : R)
    ·
      rw [coeff_zero_eq_eval_zero _]
      simp only [zero_pow (lt_of_lt_of_leₓ zero_lt_two hn), eval_X, eval_one, zero_sub, eval_pow, eval_sub]
    rw [hzero] at heq 
    exact neg_inj.mp (Eq.symm HEq)

/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, where `p` is a prime, then `a` and `p` are
coprime. -/
theorem coprime_of_root_cyclotomic {n : ℕ} (hpos : 0 < n) {p : ℕ} [hprime : Fact p.prime] {a : ℕ}
  (hroot : is_root (cyclotomic n (Zmod p)) (Nat.castRingHom (Zmod p) a)) : a.coprime p :=
  by 
    apply Nat.Coprime.symm 
    rw [hprime.1.coprime_iff_not_dvd]
    intro h 
    replace h := (Zmod.nat_coe_zmod_eq_zero_iff_dvd a p).2 h 
    rw [is_root.def, RingHom.eq_nat_cast, h, ←coeff_zero_eq_eval_zero] at hroot 
    byCases' hone : n = 1
    ·
      simp only [hone, cyclotomic_one, zero_sub, coeff_one_zero, coeff_X_zero, neg_eq_zero, one_ne_zero, coeff_sub] at
        hroot 
      exact hroot 
    rw
      [cyclotomic_coeff_zero (Zmod p)
        (Nat.succ_le_of_ltₓ (lt_of_le_of_neₓ (Nat.succ_le_of_ltₓ hpos) (Ne.symm hone)))] at
      hroot 
    exact one_ne_zero hroot

end Cyclotomic

section Order

/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, then the multiplicative order of `a` modulo
`p` divides `n`. -/
theorem order_of_root_cyclotomic_dvd {n : ℕ} (hpos : 0 < n) {p : ℕ} [Fact p.prime] {a : ℕ}
  (hroot : is_root (cyclotomic n (Zmod p)) (Nat.castRingHom (Zmod p) a)) :
  orderOf (Zmod.unitOfCoprime a (coprime_of_root_cyclotomic hpos hroot)) ∣ n :=
  by 
    apply order_of_dvd_of_pow_eq_one 
    suffices hpow : eval (Nat.castRingHom (Zmod p) a) ((X^n) - 1 : Polynomial (Zmod p)) = 0
    ·
      simp only [eval_X, eval_one, eval_pow, eval_sub, RingHom.eq_nat_cast] at hpow 
      apply Units.coe_eq_one.1
      simp only [sub_eq_zero.mp hpow, Zmod.coe_unit_of_coprime, Units.coe_pow]
    rw [is_root.def] at hroot 
    rw [←prod_cyclotomic_eq_X_pow_sub_one hpos (Zmod p), Nat.divisors_eq_proper_divisors_insert_self_of_pos hpos,
      Finset.prod_insert Nat.properDivisors.not_self_mem, eval_mul, hroot, zero_mul]

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, where `p` is a prime that does not divide
`n`, then the multiplicative order of `a` modulo `p` is exactly `n`. -/
theorem order_of_root_cyclotomic_eq
{n : exprℕ()}
(hpos : «expr < »(0, n))
{p : exprℕ()}
[fact p.prime]
{a : exprℕ()}
(hn : «expr¬ »(«expr ∣ »(p, n)))
(hroot : is_root (cyclotomic n (zmod p)) (nat.cast_ring_hom (zmod p) a)) : «expr = »(order_of (zmod.unit_of_coprime a (coprime_of_root_cyclotomic hpos hroot)), n) :=
begin
  set [] [ident m] [] [":="] [expr order_of (zmod.unit_of_coprime a (coprime_of_root_cyclotomic hpos hroot))] [],
  have [ident ha] [] [":=", expr coprime_of_root_cyclotomic hpos hroot],
  have [ident hdivcycl] [":", expr «expr ∣ »(map (int.cast_ring_hom (zmod p)) «expr - »(X, a), cyclotomic n (zmod p))] [],
  { replace [ident hrootdiv] [] [":=", expr dvd_iff_is_root.2 hroot],
    simp [] [] ["only"] ["[", expr C_eq_nat_cast, ",", expr ring_hom.eq_nat_cast, "]"] [] ["at", ident hrootdiv],
    simp [] [] ["only"] ["[", expr hrootdiv, ",", expr map_nat_cast, ",", expr map_X, ",", expr map_sub, "]"] [] [] },
  by_contra [ident hdiff],
  have [ident hdiv] [":", expr «expr ∣ »(map (int.cast_ring_hom (zmod p)) «expr - »(X, a), «expr∏ in , »((i), nat.proper_divisors n, cyclotomic i (zmod p)))] [],
  { suffices [ident hdivm] [":", expr «expr ∣ »(map (int.cast_ring_hom (zmod p)) «expr - »(X, a), «expr - »(«expr ^ »(X, m), 1))],
    { exact [expr hdivm.trans (X_pow_sub_one_dvd_prod_cyclotomic (zmod p) hpos (order_of_root_cyclotomic_dvd hpos hroot) hdiff)] },
    rw ["[", expr map_sub, ",", expr map_X, ",", expr map_nat_cast, ",", "<-", expr C_eq_nat_cast, ",", expr dvd_iff_is_root, ",", expr is_root.def, ",", expr eval_sub, ",", expr eval_pow, ",", expr eval_one, ",", expr eval_X, ",", expr sub_eq_zero, ",", "<-", expr zmod.coe_unit_of_coprime a ha, ",", "<-", expr units.coe_pow, ",", expr units.coe_eq_one, "]"] [],
    exact [expr pow_order_of_eq_one (zmod.unit_of_coprime a ha)] },
  have [ident habs] [":", expr «expr ∣ »(«expr ^ »(map (int.cast_ring_hom (zmod p)) «expr - »(X, a), 2), «expr - »(«expr ^ »(X, n), 1))] [],
  { obtain ["⟨", ident P, ",", ident hP, "⟩", ":=", expr hdivcycl],
    obtain ["⟨", ident Q, ",", ident hQ, "⟩", ":=", expr hdiv],
    rw ["[", "<-", expr prod_cyclotomic_eq_X_pow_sub_one hpos, ",", expr nat.divisors_eq_proper_divisors_insert_self_of_pos hpos, ",", expr finset.prod_insert nat.proper_divisors.not_self_mem, ",", expr hP, ",", expr hQ, "]"] [],
    exact [expr ⟨«expr * »(P, Q), by ring []⟩] },
  have [ident hnzero] [":", expr «expr ≠ »(«expr↑ »(n), (0 : zmod p))] [],
  { intro [ident ha],
    exact [expr hn (int.coe_nat_dvd.1 ((zmod.int_coe_zmod_eq_zero_iff_dvd n p).1 ha))] },
  rw ["[", expr sq, "]"] ["at", ident habs],
  replace [ident habs] [] [":=", expr squarefree_X_pow_sub_C (1 : zmod p) hnzero one_ne_zero (map (int.cast_ring_hom (zmod p)) «expr - »(X, a)) habs],
  simp [] [] ["only"] ["[", expr map_nat_cast, ",", expr map_X, ",", expr map_sub, "]"] [] ["at", ident habs],
  replace [ident habs] [] [":=", expr degree_eq_zero_of_is_unit habs],
  rw ["[", "<-", expr C_eq_nat_cast, ",", expr degree_X_sub_C, "]"] ["at", ident habs],
  exact [expr one_ne_zero habs]
end

end Order

section minpoly

open IsPrimitiveRoot Complex

/-- The minimal polynomial of a primitive `n`-th root of unity `μ` divides `cyclotomic n ℤ`. -/
theorem _root_.minpoly_dvd_cyclotomic {n : ℕ} {K : Type _} [Field K] {μ : K} (h : IsPrimitiveRoot μ n) (hpos : 0 < n)
  [CharZero K] : minpoly ℤ μ ∣ cyclotomic n ℤ :=
  by 
    apply minpoly.gcd_domain_dvd ℚ (IsIntegral h hpos) (cyclotomic.monic n ℤ).IsPrimitive 
    simpa [aeval_def, eval₂_eq_eval_map, is_root.def] using is_root_cyclotomic hpos h

/-- `cyclotomic n ℤ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
theorem cyclotomic_eq_minpoly {n : ℕ} {K : Type _} [Field K] {μ : K} (h : IsPrimitiveRoot μ n) (hpos : 0 < n)
  [CharZero K] : cyclotomic n ℤ = minpoly ℤ μ :=
  by 
    refine'
      eq_of_monic_of_dvd_of_nat_degree_le (minpoly.monic (IsIntegral h hpos)) (cyclotomic.monic n ℤ)
        (minpoly_dvd_cyclotomic h hpos) _ 
    simpa [nat_degree_cyclotomic n ℤ] using totient_le_degree_minpoly h hpos

/-- `cyclotomic n ℤ` is irreducible. -/
theorem cyclotomic.irreducible {n : ℕ} (hpos : 0 < n) : Irreducible (cyclotomic n ℤ) :=
  by 
    rw [cyclotomic_eq_minpoly (is_primitive_root_exp n hpos.ne') hpos]
    apply minpoly.irreducible 
    exact (is_primitive_root_exp n hpos.ne').IsIntegral hpos

end minpoly

section EvalOne

open Finset Nat

@[simp]
theorem eval_one_cyclotomic_prime {R : Type _} [CommRingₓ R] {n : ℕ} [hn : Fact (Nat.Prime n)] :
  eval 1 (cyclotomic n R) = n :=
  by 
    simp only [cyclotomic_eq_geom_sum hn.out, geom_sum_def, eval_X, one_pow, sum_const, eval_pow, eval_finset_sum,
      card_range, smul_one_eq_coe]

@[simp]
theorem eval₂_one_cyclotomic_prime {R S : Type _} [CommRingₓ R] [Semiringₓ S] (f : R →+* S) {n : ℕ} [Fact n.prime] :
  eval₂ f 1 (cyclotomic n R) = n :=
  by 
    simp 

@[simp]
theorem eval_one_cyclotomic_prime_pow {R : Type _} [CommRingₓ R] {n : ℕ} (k : ℕ) [hn : Fact n.prime] :
  eval 1 (cyclotomic (n^k+1) R) = n :=
  by 
    simp only [cyclotomic_prime_pow_eq_geom_sum hn.out, geom_sum_def, eval_X, one_pow, sum_const, eval_pow,
      eval_finset_sum, card_range, smul_one_eq_coe]

@[simp]
theorem eval₂_one_cyclotomic_prime_pow {R S : Type _} [CommRingₓ R] [Semiringₓ S] (f : R →+* S) {n : ℕ} (k : ℕ)
  [Fact n.prime] : eval₂ f 1 (cyclotomic (n^k+1) R) = n :=
  by 
    simp 

end EvalOne

end Polynomial

