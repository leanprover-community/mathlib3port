import Mathbin.Algebra.Polynomial.BigOperators 
import Mathbin.Analysis.Complex.RootsOfUnity 
import Mathbin.Data.Polynomial.Lifts 
import Mathbin.FieldTheory.Separable 
import Mathbin.FieldTheory.SplittingField 
import Mathbin.NumberTheory.ArithmeticFunction 
import Mathbin.RingTheory.RootsOfUnity 
import Mathbin.FieldTheory.Ratfunc

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

variable {R : Type _} [CommRingₓ R] [IsDomain R]

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

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The second modified cyclotomic polyomial is `X + 1` if the characteristic of `R` is not `2`. -/
@[simp]
theorem cyclotomic'_two
(R : Type*)
[comm_ring R]
[is_domain R]
(p : exprℕ())
[char_p R p]
(hp : «expr ≠ »(p, 2)) : «expr = »(cyclotomic' 2 R, «expr + »(X, 1)) :=
begin
  rw ["[", expr cyclotomic', "]"] [],
  have [ident prim_root_two] [":", expr «expr = »(primitive_roots 2 R, {(«expr- »(1) : R)})] [],
  { apply [expr finset.eq_singleton_iff_unique_mem.2],
    split,
    { simp [] [] ["only"] ["[", expr is_primitive_root.neg_one p hp, ",", expr nat.succ_pos', ",", expr mem_primitive_roots, "]"] [] [] },
    { intros [ident x, ident hx],
      rw ["[", expr mem_primitive_roots zero_lt_two, "]"] ["at", ident hx],
      exact [expr is_primitive_root.eq_neg_one_of_two_right hx] } },
  simp [] [] ["only"] ["[", expr prim_root_two, ",", expr finset.prod_singleton, ",", expr ring_hom.map_neg, ",", expr ring_hom.map_one, ",", expr sub_neg_eq_add, "]"] [] []
end

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

variable {K : Type _} [Field K]

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - 1 = ∏ (X - μ)`, where `μ`
varies over the `n`-th roots of unity. -/
theorem X_pow_sub_one_eq_prod
{ζ : K}
{n : exprℕ()}
(hpos : «expr < »(0, n))
(h : is_primitive_root ζ n) : «expr = »(«expr - »(«expr ^ »(X, n), 1), «expr∏ in , »((ζ), nth_roots_finset n K, «expr - »(X, C ζ))) :=
begin
  rw ["[", expr nth_roots_finset, ",", "<-", expr multiset.to_finset_eq (is_primitive_root.nth_roots_nodup h), "]"] [],
  simp [] [] ["only"] ["[", expr finset.prod_mk, ",", expr ring_hom.map_one, "]"] [] [],
  rw ["[", expr nth_roots, "]"] [],
  have [ident hmonic] [":", expr «expr - »(«expr ^ »(X, n), C (1 : K)).monic] [":=", expr monic_X_pow_sub_C (1 : K) (ne_of_lt hpos).symm],
  symmetry,
  apply [expr prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic],
  rw ["[", expr @nat_degree_X_pow_sub_C K _ _ n 1, ",", "<-", expr nth_roots, "]"] [],
  exact [expr is_primitive_root.card_nth_roots h]
end

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

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If there is a primitive `n`-th root of unity in `K`, then
`∏ i in nat.divisors n, cyclotomic' i K = X ^ n - 1`. -/
theorem prod_cyclotomic'_eq_X_pow_sub_one
{ζ : K}
{n : exprℕ()}
(hpos : «expr < »(0, n))
(h : is_primitive_root ζ n) : «expr = »(«expr∏ in , »((i), nat.divisors n, cyclotomic' i K), «expr - »(«expr ^ »(X, n), 1)) :=
begin
  rw ["[", expr X_pow_sub_one_eq_prod hpos h, "]"] [],
  have [ident rwcyc] [":", expr ∀
   i «expr ∈ » nat.divisors n, «expr = »(cyclotomic' i K, «expr∏ in , »((μ), primitive_roots i K, «expr - »(X, C μ)))] [],
  { intros [ident i, ident hi],
    simp [] [] ["only"] ["[", expr cyclotomic', "]"] [] [] },
  conv_lhs [] [] { apply_congr [],
    skip,
    simp [] ["[", expr rwcyc, ",", expr H, "]"] [] },
  rw ["<-", expr finset.prod_bUnion] [],
  { simp [] [] ["only"] ["[", expr is_primitive_root.nth_roots_one_eq_bUnion_primitive_roots hpos h, "]"] [] [] },
  intros [ident x, ident hx, ident y, ident hy, ident hdiff],
  rw [expr finset.mem_coe] ["at", ident hx, ident hy],
  exact [expr is_primitive_root.disjoint (nat.pos_of_mem_divisors hx) (nat.pos_of_mem_divisors hy) hdiff]
end

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic' n K = (X ^ k - 1) /ₘ (∏ i in nat.proper_divisors k, cyclotomic' i K)`. -/
theorem cyclotomic'_eq_X_pow_sub_one_div
{ζ : K}
{n : exprℕ()}
(hpos : «expr < »(0, n))
(h : is_primitive_root ζ n) : «expr = »(cyclotomic' n K, «expr /ₘ »(«expr - »(«expr ^ »(X, n), 1), «expr∏ in , »((i), nat.proper_divisors n, cyclotomic' i K))) :=
begin
  rw ["[", "<-", expr prod_cyclotomic'_eq_X_pow_sub_one hpos h, ",", expr nat.divisors_eq_proper_divisors_insert_self_of_pos hpos, ",", expr finset.prod_insert nat.proper_divisors.not_self_mem, "]"] [],
  have [ident prod_monic] [":", expr «expr∏ in , »((i), nat.proper_divisors n, cyclotomic' i K).monic] [],
  { apply [expr monic_prod_of_monic],
    intros [ident i, ident hi],
    exact [expr cyclotomic'.monic i K] },
  rw [expr (div_mod_by_monic_unique (cyclotomic' n K) 0 prod_monic _).1] [],
  simp [] [] ["only"] ["[", expr degree_zero, ",", expr zero_add, "]"] [] [],
  refine [expr ⟨by rw [expr mul_comm] [], _⟩],
  rw ["[", expr bot_lt_iff_ne_bot, "]"] [],
  intro [ident h],
  exact [expr monic.ne_zero prod_monic (degree_eq_bot.1 h)]
end

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K` comes from a
monic polynomial with integer coefficients. -/
theorem int_coeff_of_cyclotomic'
{ζ : K}
{n : exprℕ()}
(h : is_primitive_root ζ n) : «expr∃ , »((P : polynomial exprℤ()), «expr ∧ »(«expr = »(map (int.cast_ring_hom K) P, cyclotomic' n K), «expr ∧ »(«expr = »(P.degree, (cyclotomic' n K).degree), P.monic))) :=
begin
  refine [expr lifts_and_degree_eq_and_monic _ (cyclotomic'.monic n K)],
  induction [expr n] ["using", ident nat.strong_induction_on] ["with", ident k, ident hk] ["generalizing", ident ζ, ident h],
  cases [expr nat.eq_zero_or_pos k] ["with", ident hzero, ident hpos],
  { use [expr 1],
    simp [] [] ["only"] ["[", expr hzero, ",", expr cyclotomic'_zero, ",", expr set.mem_univ, ",", expr subsemiring.coe_top, ",", expr eq_self_iff_true, ",", expr coe_map_ring_hom, ",", expr map_one, ",", expr and_self, "]"] [] [] },
  by_cases [expr hone, ":", expr «expr = »(k, 1)],
  { use [expr «expr - »(X, 1)],
    simp [] [] ["only"] ["[", expr hone, ",", expr cyclotomic'_one K, ",", expr set.mem_univ, ",", expr pnat.one_coe, ",", expr subsemiring.coe_top, ",", expr eq_self_iff_true, ",", expr map_X, ",", expr coe_map_ring_hom, ",", expr map_one, ",", expr and_self, ",", expr map_sub, "]"] [] [] },
  let [ident B] [":", expr polynomial K] [":=", expr «expr∏ in , »((i), nat.proper_divisors k, cyclotomic' i K)],
  have [ident Bmo] [":", expr B.monic] [],
  { apply [expr monic_prod_of_monic],
    intros [ident i, ident hi],
    exact [expr cyclotomic'.monic i K] },
  have [ident Bint] [":", expr «expr ∈ »(B, lifts (int.cast_ring_hom K))] [],
  { refine [expr subsemiring.prod_mem (lifts (int.cast_ring_hom K)) _],
    intros [ident x, ident hx],
    have [ident xsmall] [] [":=", expr (nat.mem_proper_divisors.1 hx).2],
    obtain ["⟨", ident d, ",", ident hd, "⟩", ":=", expr (nat.mem_proper_divisors.1 hx).1],
    rw ["[", expr mul_comm, "]"] ["at", ident hd],
    exact [expr hk x xsmall (is_primitive_root.pow hpos h hd)] },
  replace [ident Bint] [] [":=", expr lifts_and_degree_eq_and_monic Bint Bmo],
  obtain ["⟨", ident B₁, ",", ident hB₁, ",", ident hB₁deg, ",", ident hB₁mo, "⟩", ":=", expr Bint],
  let [ident Q₁] [":", expr polynomial exprℤ()] [":=", expr «expr /ₘ »(«expr - »(«expr ^ »(X, k), 1), B₁)],
  have [ident huniq] [":", expr «expr ∧ »(«expr = »(«expr + »(0, «expr * »(B, cyclotomic' k K)), «expr - »(«expr ^ »(X, k), 1)), «expr < »((0 : polynomial K).degree, B.degree))] [],
  { split,
    { rw ["[", expr zero_add, ",", expr mul_comm, ",", "<-", expr prod_cyclotomic'_eq_X_pow_sub_one hpos h, ",", expr nat.divisors_eq_proper_divisors_insert_self_of_pos hpos, "]"] [],
      simp [] [] ["only"] ["[", expr true_and, ",", expr finset.prod_insert, ",", expr not_lt, ",", expr nat.mem_proper_divisors, ",", expr dvd_refl, "]"] [] [] },
    rw ["[", expr degree_zero, ",", expr bot_lt_iff_ne_bot, "]"] [],
    intro [ident habs],
    exact [expr monic.ne_zero Bmo (degree_eq_bot.1 habs)] },
  replace [ident huniq] [] [":=", expr div_mod_by_monic_unique (cyclotomic' k K) (0 : polynomial K) Bmo huniq],
  simp [] [] ["only"] ["[", expr lifts, ",", expr ring_hom.mem_srange, "]"] [] [],
  use [expr Q₁],
  rw ["[", expr coe_map_ring_hom, ",", expr map_div_by_monic (int.cast_ring_hom K) hB₁mo, ",", expr hB₁, ",", "<-", expr huniq.1, "]"] [],
  simp [] [] [] [] [] []
end

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

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The first cyclotomic polyomial is `X - 1`. -/
@[simp]
theorem cyclotomic_one (R : Type*) [ring R] : «expr = »(cyclotomic 1 R, «expr - »(X, 1)) :=
begin
  have [ident hspec] [":", expr «expr = »(map (int.cast_ring_hom exprℂ()) «expr - »(X, 1), cyclotomic' 1 exprℂ())] [],
  { simp [] [] ["only"] ["[", expr cyclotomic'_one, ",", expr pnat.one_coe, ",", expr map_X, ",", expr map_one, ",", expr map_sub, "]"] [] [] },
  symmetry,
  rw ["[", "<-", expr map_cyclotomic_int, ",", "<-", expr int_cyclotomic_unique hspec, "]"] [],
  simp [] [] ["only"] ["[", expr map_X, ",", expr map_one, ",", expr map_sub, "]"] [] []
end

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The second cyclotomic polyomial is `X + 1`. -/
@[simp]
theorem cyclotomic_two (R : Type*) [ring R] : «expr = »(cyclotomic 2 R, «expr + »(X, 1)) :=
begin
  have [ident hspec] [":", expr «expr = »(map (int.cast_ring_hom exprℂ()) «expr + »(X, 1), cyclotomic' 2 exprℂ())] [],
  { simp [] [] ["only"] ["[", expr cyclotomic'_two exprℂ() 0 two_ne_zero.symm, ",", expr map_add, ",", expr map_X, ",", expr map_one, "]"] [] [] },
  symmetry,
  rw ["[", "<-", expr map_cyclotomic_int, ",", "<-", expr int_cyclotomic_unique hspec, "]"] [],
  simp [] [] ["only"] ["[", expr map_add, ",", expr map_X, ",", expr map_one, "]"] [] []
end

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

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The natural degree of `cyclotomic n` is `totient n`. -/
theorem nat_degree_cyclotomic
(n : exprℕ())
(R : Type*)
[ring R]
[nontrivial R] : «expr = »((cyclotomic n R).nat_degree, nat.totient n) :=
begin
  have [ident hdeg] [] [":=", expr degree_cyclotomic n R],
  rw [expr degree_eq_nat_degree (cyclotomic_ne_zero n R)] ["at", ident hdeg],
  exact_mod_cast [expr hdeg]
end

/-- The degree of `cyclotomic n R` is positive. -/
theorem degree_cyclotomic_pos (n : ℕ) (R : Type _) (hpos : 0 < n) [Ringₓ R] [Nontrivial R] :
  0 < (cyclotomic n R).degree :=
  by 
    rw [degree_cyclotomic n R]
    exactModCast Nat.totient_pos hpos

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `∏ i in nat.divisors n, cyclotomic i R = X ^ n - 1`. -/
theorem prod_cyclotomic_eq_X_pow_sub_one
{n : exprℕ()}
(hpos : «expr < »(0, n))
(R : Type*)
[comm_ring R] : «expr = »(«expr∏ in , »((i), nat.divisors n, cyclotomic i R), «expr - »(«expr ^ »(X, n), 1)) :=
begin
  have [ident integer] [":", expr «expr = »(«expr∏ in , »((i), nat.divisors n, cyclotomic i exprℤ()), «expr - »(«expr ^ »(X, n), 1))] [],
  { apply [expr map_injective (int.cast_ring_hom exprℂ()) int.cast_injective],
    rw [expr map_prod (int.cast_ring_hom exprℂ()) (λ i, cyclotomic i exprℤ())] [],
    simp [] [] ["only"] ["[", expr int_cyclotomic_spec, ",", expr map_pow, ",", expr nat.cast_id, ",", expr map_X, ",", expr map_one, ",", expr map_sub, "]"] [] [],
    exact [expr prod_cyclotomic'_eq_X_pow_sub_one hpos (complex.is_primitive_root_exp n (ne_of_lt hpos).symm)] },
  have [ident coerc] [":", expr «expr = »(«expr - »(«expr ^ »(X, n), 1), map (int.cast_ring_hom R) «expr - »(«expr ^ »(X, n), 1))] [],
  { simp [] [] ["only"] ["[", expr map_pow, ",", expr map_X, ",", expr map_one, ",", expr map_sub, "]"] [] [] },
  have [ident h] [":", expr ∀
   i «expr ∈ » n.divisors, «expr = »(cyclotomic i R, map (int.cast_ring_hom R) (cyclotomic i exprℤ()))] [],
  { intros [ident i, ident hi],
    exact [expr (map_cyclotomic_int i R).symm] },
  rw ["[", expr finset.prod_congr (refl n.divisors) h, ",", expr coerc, ",", "<-", expr map_prod (int.cast_ring_hom R) (λ
    i, cyclotomic i exprℤ()), ",", expr integer, "]"] []
end

section ArithmeticFunction

open Nat.ArithmeticFunction

open_locale ArithmeticFunction

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `cyclotomic n R` can be expressed as a product in a fraction field of `polynomial R`
  using Möbius inversion. -/
theorem cyclotomic_eq_prod_X_pow_sub_one_pow_moebius
{n : exprℕ()}
(R : Type*)
[comm_ring R]
[is_domain R] : «expr = »(algebra_map _ (ratfunc R) (cyclotomic n R), «expr∏ in , »((i), n.divisors_antidiagonal, «expr ^ »(algebra_map (polynomial R) _ «expr - »(«expr ^ »(X, i.snd), 1), exprμ() i.fst))) :=
begin
  rcases [expr n.eq_zero_or_pos, "with", ident rfl, "|", ident hpos],
  { simp [] [] [] [] [] [] },
  have [ident h] [":", expr ∀
   n : exprℕ(), «expr < »(0, n) → «expr = »(«expr∏ in , »((i), nat.divisors n, algebra_map _ (ratfunc R) (cyclotomic i R)), algebra_map _ _ «expr - »(«expr ^ »(X, n), 1))] [],
  { intros [ident n, ident hn],
    rw ["[", "<-", expr prod_cyclotomic_eq_X_pow_sub_one hn R, ",", expr ring_hom.map_prod, "]"] [] },
  rw [expr (prod_eq_iff_prod_pow_moebius_eq_of_nonzero (λ
     n hn, _) (λ n hn, _)).1 h n hpos] []; rw ["[", expr ne.def, ",", expr is_fraction_ring.to_map_eq_zero_iff, "]"] [],
  { apply [expr cyclotomic_ne_zero] },
  { apply [expr monic.ne_zero],
    apply [expr monic_X_pow_sub_C _ (ne_of_gt hn)] }
end

end ArithmeticFunction

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- We have
`cyclotomic n R = (X ^ k - 1) /ₘ (∏ i in nat.proper_divisors k, cyclotomic i K)`. -/
theorem cyclotomic_eq_X_pow_sub_one_div
{R : Type*}
[comm_ring R]
{n : exprℕ()}
(hpos : «expr < »(0, n)) : «expr = »(cyclotomic n R, «expr /ₘ »(«expr - »(«expr ^ »(X, n), 1), «expr∏ in , »((i), nat.proper_divisors n, cyclotomic i R))) :=
begin
  nontriviality [expr R] [],
  rw ["[", "<-", expr prod_cyclotomic_eq_X_pow_sub_one hpos, ",", expr nat.divisors_eq_proper_divisors_insert_self_of_pos hpos, ",", expr finset.prod_insert nat.proper_divisors.not_self_mem, "]"] [],
  have [ident prod_monic] [":", expr «expr∏ in , »((i), nat.proper_divisors n, cyclotomic i R).monic] [],
  { apply [expr monic_prod_of_monic],
    intros [ident i, ident hi],
    exact [expr cyclotomic.monic i R] },
  rw [expr (div_mod_by_monic_unique (cyclotomic n R) 0 prod_monic _).1] [],
  simp [] [] ["only"] ["[", expr degree_zero, ",", expr zero_add, "]"] [] [],
  split,
  { rw [expr mul_comm] [] },
  rw ["[", expr bot_lt_iff_ne_bot, "]"] [],
  intro [ident h],
  exact [expr monic.ne_zero prod_monic (degree_eq_bot.1 h)]
end

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

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic n K = ∏ μ in primitive_roots n R, (X - C μ)`. In particular,
`cyclotomic n K = cyclotomic' n K` -/
theorem cyclotomic_eq_prod_X_sub_primitive_roots
{K : Type*}
[field K]
{ζ : K}
{n : exprℕ()}
(hz : is_primitive_root ζ n) : «expr = »(cyclotomic n K, «expr∏ in , »((μ), primitive_roots n K, «expr - »(X, C μ))) :=
begin
  rw ["<-", expr cyclotomic'] [],
  induction [expr n] ["using", ident nat.strong_induction_on] ["with", ident k, ident hk] ["generalizing", ident ζ, ident hz],
  obtain [ident hzero, "|", ident hpos, ":=", expr k.eq_zero_or_pos],
  { simp [] [] ["only"] ["[", expr hzero, ",", expr cyclotomic'_zero, ",", expr cyclotomic_zero, "]"] [] [] },
  have [ident h] [":", expr ∀ i «expr ∈ » k.proper_divisors, «expr = »(cyclotomic i K, cyclotomic' i K)] [],
  { intros [ident i, ident hi],
    obtain ["⟨", ident d, ",", ident hd, "⟩", ":=", expr (nat.mem_proper_divisors.1 hi).1],
    rw [expr mul_comm] ["at", ident hd],
    exact [expr hk i (nat.mem_proper_divisors.1 hi).2 (is_primitive_root.pow hpos hz hd)] },
  rw ["[", expr @cyclotomic_eq_X_pow_sub_one_div _ _ _ hpos, ",", expr cyclotomic'_eq_X_pow_sub_one_div hpos hz, ",", expr finset.prod_congr (refl k.proper_divisors) h, "]"] []
end

/-- Any `n`-th primitive root of unity is a root of `cyclotomic n ℤ`.-/
theorem is_root_cyclotomic {n : ℕ} {K : Type _} [Field K] (hpos : 0 < n) {μ : K} (h : IsPrimitiveRoot μ n) :
  is_root (cyclotomic n K) μ :=
  by 
    rw [←mem_roots (cyclotomic_ne_zero n K), cyclotomic_eq_prod_X_sub_primitive_roots h, roots_prod_X_sub_C,
      ←Finset.mem_def]
    rwa [←mem_primitive_roots hpos] at h

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_cyclotomic_iff
{R : Type*}
[comm_ring R]
{n : exprℕ()}
(hpos : «expr < »(0, n))
(P : polynomial R) : «expr ↔ »(«expr = »(P, cyclotomic n R), «expr = »(«expr * »(P, «expr∏ in , »((i), nat.proper_divisors n, polynomial.cyclotomic i R)), «expr - »(«expr ^ »(X, n), 1))) :=
begin
  nontriviality [expr R] [],
  refine [expr ⟨λ hcycl, _, λ hP, _⟩],
  { rw ["[", expr hcycl, ",", "<-", expr finset.prod_insert (@nat.proper_divisors.not_self_mem n), ",", "<-", expr nat.divisors_eq_proper_divisors_insert_self_of_pos hpos, "]"] [],
    exact [expr prod_cyclotomic_eq_X_pow_sub_one hpos R] },
  { have [ident prod_monic] [":", expr «expr∏ in , »((i), nat.proper_divisors n, cyclotomic i R).monic] [],
    { apply [expr monic_prod_of_monic],
      intros [ident i, ident hi],
      exact [expr cyclotomic.monic i R] },
    rw ["[", expr @cyclotomic_eq_X_pow_sub_one_div R _ _ hpos, ",", expr (div_mod_by_monic_unique P 0 prod_monic _).1, "]"] [],
    refine [expr ⟨by rwa ["[", expr zero_add, ",", expr mul_comm, "]"] [], _⟩],
    rw ["[", expr degree_zero, ",", expr bot_lt_iff_ne_bot, "]"] [],
    intro [ident h],
    exact [expr monic.ne_zero prod_monic (degree_eq_bot.1 h)] }
end

/-- If `p` is prime, then `cyclotomic p R = geom_sum X p`. -/
theorem cyclotomic_eq_geom_sum {R : Type _} [CommRingₓ R] {p : ℕ} (hp : Nat.Prime p) : cyclotomic p R = geomSum X p :=
  by 
    refine' ((eq_cyclotomic_iff hp.pos _).mpr _).symm 
    simp only [Nat.Prime.proper_divisors hp, geom_sum_mul, Finset.prod_singleton, cyclotomic_one]

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `p ^ k` is prime power, then `cyclotomic (p ^ (n + 1)) R = geom_sum (X ^ p ^ n) p`. -/
theorem cyclotomic_prime_pow_eq_geom_sum
{R : Type*}
[comm_ring R]
{p n : exprℕ()}
(hp : nat.prime p) : «expr = »(cyclotomic «expr ^ »(p, «expr + »(n, 1)) R, geom_sum «expr ^ »(X, «expr ^ »(p, n)) p) :=
begin
  have [] [":", expr ∀
   m, «expr ↔ »(«expr = »(cyclotomic «expr ^ »(p, «expr + »(m, 1)) R, geom_sum «expr ^ »(X, «expr ^ »(p, m)) p), «expr = »(«expr * »(geom_sum «expr ^ »(X, «expr ^ »(p, m)) p, «expr∏ in , »((x : exprℕ()), finset.range «expr + »(m, 1), cyclotomic «expr ^ »(p, x) R)), «expr - »(«expr ^ »(X, «expr ^ »(p, «expr + »(m, 1))), 1)))] [],
  { intro [ident m],
    have [] [] [":=", expr eq_cyclotomic_iff (pow_pos hp.pos «expr + »(m, 1)) _],
    rw [expr eq_comm] ["at", ident this],
    rw ["[", expr this, ",", expr nat.prod_proper_divisors_prime_pow hp, "]"] [] },
  induction [expr n] [] ["with", ident n_n, ident n_ih] [],
  { simp [] [] [] ["[", expr cyclotomic_eq_geom_sum hp, "]"] [] [] },
  rw [expr ((eq_cyclotomic_iff (pow_pos hp.pos «expr + »(n_n.succ, 1)) _).mpr _).symm] [],
  rw ["[", expr nat.prod_proper_divisors_prime_pow hp, ",", expr finset.prod_range_succ, ",", expr n_ih, "]"] [],
  rw [expr this] ["at", ident n_ih],
  rw ["[", expr mul_comm _ (geom_sum _ _), ",", expr n_ih, ",", expr geom_sum_mul, ",", expr sub_left_inj, ",", "<-", expr pow_mul, ",", expr pow_add, ",", expr pow_one, "]"] []
end

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The constant term of `cyclotomic n R` is `1` if `2 ≤ n`. -/
theorem cyclotomic_coeff_zero
(R : Type*)
[comm_ring R]
{n : exprℕ()}
(hn : «expr ≤ »(2, n)) : «expr = »((cyclotomic n R).coeff 0, 1) :=
begin
  induction [expr n] ["using", ident nat.strong_induction_on] ["with", ident n, ident hi] [],
  have [ident hprod] [":", expr «expr = »(«expr∏ in , »((i), nat.proper_divisors n, (polynomial.cyclotomic i R).coeff 0), «expr- »(1))] [],
  { rw ["[", "<-", expr finset.insert_erase (nat.one_mem_proper_divisors_iff_one_lt.2 (lt_of_lt_of_le one_lt_two hn)), ",", expr finset.prod_insert (finset.not_mem_erase 1 _), ",", expr cyclotomic_one R, "]"] [],
    have [ident hleq] [":", expr ∀ j «expr ∈ » n.proper_divisors.erase 1, «expr ≤ »(2, j)] [],
    { intros [ident j, ident hj],
      apply [expr nat.succ_le_of_lt],
      exact [expr (ne.le_iff_lt (finset.mem_erase.1 hj).1.symm).mp (nat.succ_le_of_lt (nat.pos_of_mem_proper_divisors (finset.mem_erase.1 hj).2))] },
    have [ident hcongr] [":", expr ∀ j «expr ∈ » n.proper_divisors.erase 1, «expr = »((cyclotomic j R).coeff 0, 1)] [],
    { intros [ident j, ident hj],
      exact [expr hi j (nat.mem_proper_divisors.1 (finset.mem_erase.1 hj).2).2 (hleq j hj)] },
    have [ident hrw] [":", expr «expr = »(«expr∏ in , »((x : exprℕ()), n.proper_divisors.erase 1, (cyclotomic x R).coeff 0), 1)] [],
    { rw [expr finset.prod_congr (refl (n.proper_divisors.erase 1)) hcongr] [],
      simp [] [] ["only"] ["[", expr finset.prod_const_one, "]"] [] [] },
    simp [] [] ["only"] ["[", expr hrw, ",", expr mul_one, ",", expr zero_sub, ",", expr coeff_one_zero, ",", expr coeff_X_zero, ",", expr coeff_sub, "]"] [] [] },
  have [ident heq] [":", expr «expr = »(«expr - »(«expr ^ »(X, n), 1).coeff 0, «expr- »((cyclotomic n R).coeff 0))] [],
  { rw ["[", "<-", expr prod_cyclotomic_eq_X_pow_sub_one (lt_of_lt_of_le zero_lt_two hn), ",", expr nat.divisors_eq_proper_divisors_insert_self_of_pos (lt_of_lt_of_le zero_lt_two hn), ",", expr finset.prod_insert nat.proper_divisors.not_self_mem, ",", expr mul_coeff_zero, ",", expr coeff_zero_prod, ",", expr hprod, ",", expr mul_neg_eq_neg_mul_symm, ",", expr mul_one, "]"] [] },
  have [ident hzero] [":", expr «expr = »(«expr - »(«expr ^ »(X, n), 1).coeff 0, («expr- »(1) : R))] [],
  { rw [expr coeff_zero_eq_eval_zero _] [],
    simp [] [] ["only"] ["[", expr zero_pow (lt_of_lt_of_le zero_lt_two hn), ",", expr eval_X, ",", expr eval_one, ",", expr zero_sub, ",", expr eval_pow, ",", expr eval_sub, "]"] [] [] },
  rw [expr hzero] ["at", ident heq],
  exact [expr neg_inj.mp (eq.symm heq)]
end

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

-- error in RingTheory.Polynomial.Cyclotomic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
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
  replace [ident habs] [] [":=", expr (separable_X_pow_sub_C (1 : zmod p) hnzero one_ne_zero).squarefree (map (int.cast_ring_hom (zmod p)) «expr - »(X, a)) habs],
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

