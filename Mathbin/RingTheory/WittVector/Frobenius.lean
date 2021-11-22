import Mathbin.Data.Nat.Multiplicity 
import Mathbin.RingTheory.WittVector.Basic 
import Mathbin.RingTheory.WittVector.IsPoly

/-!
## The Frobenius operator

If `R` has characteristic `p`, then there is a ring endomorphism `frobenius R p`
that raises `r : R` to the power `p`.
By applying `witt_vector.map` to `frobenius R p`, we obtain a ring endomorphism `𝕎 R →+* 𝕎 R`.
It turns out that this endomorphism can be described by polynomials over `ℤ`
that do not depend on `R` or the fact that it has characteristic `p`.
In this way, we obtain a Frobenius endomorphism `witt_vector.frobenius_fun : 𝕎 R → 𝕎 R`
for every commutative ring `R`.

Unfortunately, the aforementioned polynomials can not be obtained using the machinery
of `witt_structure_int` that was developed in `structure_polynomial.lean`.
We therefore have to define the polynomials by hand, and check that they have the required property.

In case `R` has characteristic `p`, we show in `frobenius_fun_eq_map_frobenius`
that `witt_vector.frobenius_fun` is equal to `witt_vector.map (frobenius R p)`.

### Main definitions and results

* `frobenius_poly`: the polynomials that describe the coefficients of `frobenius_fun`;
* `frobenius_fun`: the Frobenius endomorphism on Witt vectors;
* `frobenius_fun_is_poly`: the tautological assertion that Frobenius is a polynomial function;
* `frobenius_fun_eq_map_frobenius`: the fact that in characteristic `p`, Frobenius is equal to
  `witt_vector.map (frobenius R p)`.

TODO: Show that `witt_vector.frobenius_fun` is a ring homomorphism,
and bundle it into `witt_vector.frobenius`.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

variable{p : ℕ}{R S : Type _}[hp : Fact p.prime][CommRingₓ R][CommRingₓ S]

local notation "𝕎" => WittVector p

noncomputable theory

open MvPolynomial Finset

open_locale BigOperators

variable(p)

include hp

/-- The rational polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`.
These polynomials actually have integral coefficients,
see `frobenius_poly` and `map_frobenius_poly`. -/
def frobenius_poly_rat (n : ℕ) : MvPolynomial ℕ ℚ :=
  bind₁ (wittPolynomial p ℚ ∘ fun n => n+1) (xInTermsOfW p ℚ n)

theorem bind₁_frobenius_poly_rat_witt_polynomial (n : ℕ) :
  bind₁ (frobenius_poly_rat p) (wittPolynomial p ℚ n) = wittPolynomial p ℚ (n+1) :=
  by 
    delta' frobenius_poly_rat 
    rw [←bind₁_bind₁, bind₁_X_in_terms_of_W_witt_polynomial, bind₁_X_right]

/-- An auxiliary definition, to avoid an excessive amount of finiteness proofs
for `multiplicity p n`. -/
private def pnat_multiplicity (n : ℕ+) : ℕ :=
  (multiplicity p n).get$ multiplicity.finite_nat_iff.mpr$ ⟨ne_of_gtₓ hp.1.one_lt, n.2⟩

local notation "v" => pnat_multiplicity

/-- An auxiliary polynomial over the integers, that satisfies
`p * (frobenius_poly_aux p n) + X n ^ p = frobenius_poly p n`.
This makes it easy to show that `frobenius_poly p n` is congruent to `X n ^ p`
modulo `p`. -/
noncomputable def frobenius_poly_aux : ℕ → MvPolynomial ℕ ℤ
| n =>
  X (n+1) -
    ∑i : Finₓ n,
      have  := i.is_lt
      ∑j in range (p^n - i),
        (((X
                  i^p)^(p^n - i) -
                j+1)*frobenius_poly_aux
                i^j+1)*C
            («expr↑ »
              (((p^n - i).choose (j+1) /
                  (p^n - i - v p ⟨j+1, Nat.succ_posₓ j⟩))*«expr↑ » p^j - v p ⟨j+1, Nat.succ_posₓ j⟩ :
              ℕ))

theorem frobenius_poly_aux_eq (n : ℕ) :
  frobenius_poly_aux p n =
    X (n+1) -
      ∑i in range n,
        ∑j in range (p^n - i),
          (((X
                    i^p)^(p^n - i) -
                  j+1)*frobenius_poly_aux p
                  i^j+1)*C
              («expr↑ »
                (((p^n - i).choose (j+1) /
                    (p^n - i - v p ⟨j+1, Nat.succ_posₓ j⟩))*«expr↑ » p^j - v p ⟨j+1, Nat.succ_posₓ j⟩ :
                ℕ)) :=
  by 
    rw [frobenius_poly_aux, ←Finₓ.sum_univ_eq_sum_range]

/-- The polynomials that give the coefficients of `frobenius x`,
in terms of the coefficients of `x`. -/
def frobenius_poly (n : ℕ) : MvPolynomial ℕ ℤ :=
  (X n^p)+C («expr↑ » p)*frobenius_poly_aux p n

/-- A key divisibility fact for the proof of `witt_vector.map_frobenius_poly`. -/
theorem map_frobenius_poly.key₁ (n j : ℕ) (hj : j < (p^n)) : (p^n - v p ⟨j+1, j.succ_pos⟩) ∣ (p^n).choose (j+1) :=
  by 
    apply multiplicity.pow_dvd_of_le_multiplicity 
    have aux : (multiplicity p ((p^n).choose (j+1))).Dom
    ·
      rw [←multiplicity.finite_iff_dom, multiplicity.finite_nat_iff]
      exact ⟨hp.1.ne_one, Nat.choose_pos hj⟩
    rw [←Enat.coe_get aux, Enat.coe_le_coe, tsub_le_iff_left, ←Enat.coe_le_coe, Nat.cast_add, pnat_multiplicity,
      Enat.coe_get, Enat.coe_get, add_commₓ]
    exact (hp.1.multiplicity_choose_prime_pow hj j.succ_pos).Ge

/-- A key numerical identity needed for the proof of `witt_vector.map_frobenius_poly`. -/
theorem map_frobenius_poly.key₂ {n i j : ℕ} (hi : i < n) (hj : j < (p^n - i)) :
  ((j - v p ⟨j+1, j.succ_pos⟩)+n) = (i+j)+n - i - v p ⟨j+1, j.succ_pos⟩ :=
  by 
    generalize h : v p ⟨j+1, j.succ_pos⟩ = m 
    suffices  : m ≤ n - i ∧ m ≤ j
    ·
      rw [tsub_add_eq_add_tsub this.2, add_commₓ i j, add_tsub_assoc_of_le (this.1.trans (Nat.sub_leₓ n i)), add_assocₓ,
        tsub_right_comm, add_commₓ i,
        tsub_add_cancel_of_le (le_tsub_of_add_le_right ((le_tsub_iff_left hi.le).mp this.1))]
    split 
    ·
      rw [←h, ←Enat.coe_le_coe, pnat_multiplicity, Enat.coe_get, ←hp.1.multiplicity_choose_prime_pow hj j.succ_pos]
      apply le_add_left 
      rfl
    ·
      obtain ⟨c, hc⟩ : (p^m) ∣ j+1
      ·
        rw [←h]
        exact multiplicity.pow_multiplicity_dvd _ 
      obtain ⟨c, rfl⟩ : ∃ k : ℕ, c = k+1
      ·
        apply Nat.exists_eq_succ_of_ne_zero 
        rintro rfl 
        simpa only using hc 
      rw [mul_addₓ, mul_oneₓ] at hc 
      apply Nat.le_of_lt_succₓ 
      calc m < (p^m) := Nat.lt_pow_self hp.1.one_lt m _ ≤ j+1 :=
        by 
          rw [←tsub_eq_of_eq_add_rev hc]
          apply Nat.sub_leₓ

theorem map_frobenius_poly (n : ℕ) :
  MvPolynomial.map (Int.castRingHom ℚ) (frobenius_poly p n) = frobenius_poly_rat p n :=
  by 
    rw [frobenius_poly, RingHom.map_add, RingHom.map_mul, RingHom.map_pow, map_C, map_X, RingHom.eq_int_cast,
      Int.cast_coe_nat, frobenius_poly_rat]
    apply Nat.strong_induction_onₓ n 
    clear n 
    intro n IH 
    rw [X_in_terms_of_W_eq]
    simp only [AlgHom.map_sum, AlgHom.map_sub, AlgHom.map_mul, AlgHom.map_pow, bind₁_C_right]
    have h1 : ((«expr↑ » p^n)*⅟ («expr↑ » p : ℚ)^n) = 1 :=
      by 
        rw [←mul_powₓ, mul_inv_of_self, one_pow]
    rw [bind₁_X_right, Function.comp_app, witt_polynomial_eq_sum_C_mul_X_pow, sum_range_succ, sum_range_succ, tsub_self,
      add_tsub_cancel_left, pow_zeroₓ, pow_oneₓ, pow_oneₓ, sub_mul, add_mulₓ, add_mulₓ, mul_right_commₓ,
      mul_right_commₓ (C («expr↑ » p^n+1)), ←C_mul, ←C_mul, pow_succₓ, mul_assocₓ («expr↑ » p) («expr↑ » p^n), h1,
      mul_oneₓ, C_1, one_mulₓ, add_commₓ _ (X n^p), add_assocₓ, ←add_sub, add_right_injₓ, frobenius_poly_aux_eq,
      RingHom.map_sub, map_X, mul_sub, sub_eq_add_neg, add_commₓ _ (C («expr↑ » p)*X (n+1)), ←add_sub, add_right_injₓ,
      neg_eq_iff_neg_eq, neg_sub]
    simp only [RingHom.map_sum, mul_sum, sum_mul, ←sum_sub_distrib]
    apply sum_congr rfl 
    intro i hi 
    rw [mem_range] at hi 
    rw [←IH i hi]
    clear IH 
    rw [add_commₓ (X i^p), add_pow, sum_range_succ', pow_zeroₓ, tsub_zero, Nat.choose_zero_right, one_mulₓ,
      Nat.cast_one, mul_oneₓ, mul_addₓ, add_mulₓ, Nat.succ_subₓ (le_of_ltₓ hi), Nat.succ_eq_add_one (n - i), pow_succₓ,
      pow_mulₓ, add_sub_cancel, mul_sum, sum_mul]
    apply sum_congr rfl 
    intro j hj 
    rw [mem_range] at hj 
    rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_pow, RingHom.map_pow, RingHom.map_pow, RingHom.map_pow,
      RingHom.map_pow, map_C, map_X, mul_powₓ]
    rw [mul_commₓ (C («expr↑ » p)^i), mul_commₓ _ ((X i^p)^_), mul_commₓ (C («expr↑ » p)^j+1),
      mul_commₓ (C («expr↑ » p))]
    simp only [mul_assocₓ]
    apply congr_argₓ 
    apply congr_argₓ 
    rw [←C_eq_coe_nat]
    simp only [←RingHom.map_pow, ←C_mul]
    rw [C_inj]
    simp only [inv_of_eq_inv, RingHom.eq_int_cast, inv_pow₀, Int.cast_coe_nat, Nat.cast_mul]
    rw [Rat.coe_nat_div _ _ (map_frobenius_poly.key₁ p (n - i) j hj)]
    simp only [Nat.cast_pow, pow_addₓ, pow_oneₓ]
    suffices  :
      ((((p^n - i).choose (j+1)*p^j - v p ⟨j+1, j.succ_pos⟩)*p)*p^n : ℚ) =
        (((p^j)*p)*(p^n - i).choose (j+1)*p^i)*p^n - i - v p ⟨j+1, j.succ_pos⟩
    ·
      have aux : ∀ k : ℕ, (p^k : ℚ) ≠ 0
      ·
        intro 
        apply pow_ne_zero 
        exactModCast hp.1.ne_zero 
      simpa [aux, -one_div] with field_simps using this.symm 
    rw [mul_commₓ _ (p : ℚ), mul_assocₓ, mul_assocₓ, ←pow_addₓ, map_frobenius_poly.key₂ p hi hj]
    ringExp

theorem frobenius_poly_zmod (n : ℕ) : MvPolynomial.map (Int.castRingHom (Zmod p)) (frobenius_poly p n) = (X n^p) :=
  by 
    rw [frobenius_poly, RingHom.map_add, RingHom.map_pow, RingHom.map_mul, map_X, map_C]
    simp only [Int.cast_coe_nat, add_zeroₓ, RingHom.eq_int_cast, Zmod.nat_cast_self, zero_mul, C_0]

@[simp]
theorem bind₁_frobenius_poly_witt_polynomial (n : ℕ) :
  bind₁ (frobenius_poly p) (wittPolynomial p ℤ n) = wittPolynomial p ℤ (n+1) :=
  by 
    apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective 
    simp only [map_bind₁, map_frobenius_poly, bind₁_frobenius_poly_rat_witt_polynomial, map_witt_polynomial]

variable{p}

/-- `frobenius_fun` is the function underlying the ring endomorphism
`frobenius : 𝕎 R →+* frobenius 𝕎 R`. -/
def frobenius_fun (x : 𝕎 R) : 𝕎 R :=
  mk p$ fun n => MvPolynomial.aeval x.coeff (frobenius_poly p n)

theorem coeff_frobenius_fun (x : 𝕎 R) (n : ℕ) :
  coeff (frobenius_fun x) n = MvPolynomial.aeval x.coeff (frobenius_poly p n) :=
  by 
    rw [frobenius_fun, coeff_mk]

variable(p)

/-- `frobenius_fun` is tautologically a polynomial function.

See also `frobenius_is_poly`. -/
@[isPoly]
theorem frobenius_fun_is_poly : is_poly p fun R _Rcr => @frobenius_fun p R _ _Rcr :=
  ⟨⟨frobenius_poly p,
      by 
        introsI 
        funext n 
        apply coeff_frobenius_fun⟩⟩

variable{p}

@[ghost_simps]
theorem ghost_component_frobenius_fun (n : ℕ) (x : 𝕎 R) :
  ghost_component n (frobenius_fun x) = ghost_component (n+1) x :=
  by 
    simp only [ghost_component_apply, frobenius_fun, coeff_mk, ←bind₁_frobenius_poly_witt_polynomial, aeval_bind₁]

/--
If `R` has characteristic `p`, then there is a ring endomorphism
that raises `r : R` to the power `p`.
By applying `witt_vector.map` to this endomorphism,
we obtain a ring endomorphism `frobenius R p : 𝕎 R →+* 𝕎 R`.

The underlying function of this morphism is `witt_vector.frobenius_fun`.
-/
def frobenius : 𝕎 R →+* 𝕎 R :=
  { toFun := frobenius_fun,
    map_zero' :=
      by 
        refine'
          is_poly.ext ((frobenius_fun_is_poly p).comp WittVector.zero_is_poly)
            (WittVector.zero_is_poly.comp (frobenius_fun_is_poly p)) _ _ 0
        ghostSimp,
    map_one' :=
      by 
        refine'
          is_poly.ext ((frobenius_fun_is_poly p).comp WittVector.one_is_poly)
            (WittVector.one_is_poly.comp (frobenius_fun_is_poly p)) _ _ 0
        ghostSimp,
    map_add' :=
      by 
        ghostCalc _ _ <;> ghostSimp,
    map_mul' :=
      by 
        ghostCalc _ _ <;> ghostSimp }

theorem coeff_frobenius (x : 𝕎 R) (n : ℕ) : coeff (frobenius x) n = MvPolynomial.aeval x.coeff (frobenius_poly p n) :=
  coeff_frobenius_fun _ _

@[ghost_simps]
theorem ghost_component_frobenius (n : ℕ) (x : 𝕎 R) : ghost_component n (frobenius x) = ghost_component (n+1) x :=
  ghost_component_frobenius_fun _ _

variable(p)

/-- `frobenius` is tautologically a polynomial function. -/
@[isPoly]
theorem frobenius_is_poly : is_poly p fun R _Rcr => @frobenius p R _ _Rcr :=
  frobenius_fun_is_poly _

section CharP

variable[CharP R p]

@[simp]
theorem coeff_frobenius_char_p (x : 𝕎 R) (n : ℕ) : coeff (frobenius x) n = (x.coeff n^p) :=
  by 
    rw [coeff_frobenius]
    calc
      aeval (fun k => x.coeff k) (frobenius_poly p n) =
        aeval (fun k => x.coeff k) (MvPolynomial.map (Int.castRingHom (Zmod p)) (frobenius_poly p n)) :=
      _ _ = aeval (fun k => x.coeff k) (X n^p : MvPolynomial ℕ (Zmod p)) := _ _ = (x.coeff n^p) := _
    ·
      convRHS => rw [aeval_eq_eval₂_hom, eval₂_hom_map_hom]
      apply eval₂_hom_congr (RingHom.ext_int _ _) rfl rfl
    ·
      rw [frobenius_poly_zmod]
    ·
      rw [AlgHom.map_pow, aeval_X]

theorem frobenius_eq_map_frobenius : @frobenius p R _ _ = map (_root_.frobenius R p) :=
  by 
    ext x n 
    simp only [coeff_frobenius_char_p, map_coeff, frobenius_def]

@[simp]
theorem frobenius_zmodp (x : 𝕎 (Zmod p)) : frobenius x = x :=
  by 
    simp only [ext_iff, coeff_frobenius_char_p, Zmod.pow_card, eq_self_iff_true, forall_const]

end CharP

end WittVector

