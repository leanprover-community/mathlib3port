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

-- error in RingTheory.WittVector.Frobenius: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A key divisibility fact for the proof of `witt_vector.map_frobenius_poly`. -/
theorem map_frobenius_poly.key₁
(n j : exprℕ())
(hj : «expr < »(j, «expr ^ »(p, n))) : «expr ∣ »(«expr ^ »(p, «expr - »(n, exprv() p ⟨«expr + »(j, 1), j.succ_pos⟩)), «expr ^ »(p, n).choose «expr + »(j, 1)) :=
begin
  apply [expr multiplicity.pow_dvd_of_le_multiplicity],
  have [ident aux] [":", expr (multiplicity p («expr ^ »(p, n).choose «expr + »(j, 1))).dom] [],
  { rw ["[", "<-", expr multiplicity.finite_iff_dom, ",", expr multiplicity.finite_nat_iff, "]"] [],
    exact [expr ⟨hp.1.ne_one, nat.choose_pos hj⟩] },
  rw ["[", "<-", expr enat.coe_get aux, ",", expr enat.coe_le_coe, ",", expr tsub_le_iff_left, ",", "<-", expr enat.coe_le_coe, ",", expr nat.cast_add, ",", expr pnat_multiplicity, ",", expr enat.coe_get, ",", expr enat.coe_get, ",", expr add_comm, "]"] [],
  exact [expr (hp.1.multiplicity_choose_prime_pow hj j.succ_pos).ge]
end

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

-- error in RingTheory.WittVector.Frobenius: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_frobenius_poly
(n : exprℕ()) : «expr = »(mv_polynomial.map (int.cast_ring_hom exprℚ()) (frobenius_poly p n), frobenius_poly_rat p n) :=
begin
  rw ["[", expr frobenius_poly, ",", expr ring_hom.map_add, ",", expr ring_hom.map_mul, ",", expr ring_hom.map_pow, ",", expr map_C, ",", expr map_X, ",", expr ring_hom.eq_int_cast, ",", expr int.cast_coe_nat, ",", expr frobenius_poly_rat, "]"] [],
  apply [expr nat.strong_induction_on n],
  clear [ident n],
  intros [ident n, ident IH],
  rw ["[", expr X_in_terms_of_W_eq, "]"] [],
  simp [] [] ["only"] ["[", expr alg_hom.map_sum, ",", expr alg_hom.map_sub, ",", expr alg_hom.map_mul, ",", expr alg_hom.map_pow, ",", expr bind₁_C_right, "]"] [] [],
  have [ident h1] [":", expr «expr = »(«expr * »(«expr ^ »(«expr↑ »(p), n), «expr ^ »(«expr⅟»() («expr↑ »(p) : exprℚ()), n)), 1)] [":=", expr by rw ["[", "<-", expr mul_pow, ",", expr mul_inv_of_self, ",", expr one_pow, "]"] []],
  rw ["[", expr bind₁_X_right, ",", expr function.comp_app, ",", expr witt_polynomial_eq_sum_C_mul_X_pow, ",", expr sum_range_succ, ",", expr sum_range_succ, ",", expr tsub_self, ",", expr add_tsub_cancel_left, ",", expr pow_zero, ",", expr pow_one, ",", expr pow_one, ",", expr sub_mul, ",", expr add_mul, ",", expr add_mul, ",", expr mul_right_comm, ",", expr mul_right_comm (C «expr ^ »(«expr↑ »(p), «expr + »(n, 1))), ",", "<-", expr C_mul, ",", "<-", expr C_mul, ",", expr pow_succ, ",", expr mul_assoc «expr↑ »(p) «expr ^ »(«expr↑ »(p), n), ",", expr h1, ",", expr mul_one, ",", expr C_1, ",", expr one_mul, ",", expr add_comm _ «expr ^ »(X n, p), ",", expr add_assoc, ",", "<-", expr add_sub, ",", expr add_right_inj, ",", expr frobenius_poly_aux_eq, ",", expr ring_hom.map_sub, ",", expr map_X, ",", expr mul_sub, ",", expr sub_eq_add_neg, ",", expr add_comm _ «expr * »(C «expr↑ »(p), X «expr + »(n, 1)), ",", "<-", expr add_sub, ",", expr add_right_inj, ",", expr neg_eq_iff_neg_eq, ",", expr neg_sub, "]"] [],
  simp [] [] ["only"] ["[", expr ring_hom.map_sum, ",", expr mul_sum, ",", expr sum_mul, ",", "<-", expr sum_sub_distrib, "]"] [] [],
  apply [expr sum_congr rfl],
  intros [ident i, ident hi],
  rw [expr mem_range] ["at", ident hi],
  rw ["[", "<-", expr IH i hi, "]"] [],
  clear [ident IH],
  rw ["[", expr add_comm «expr ^ »(X i, p), ",", expr add_pow, ",", expr sum_range_succ', ",", expr pow_zero, ",", expr tsub_zero, ",", expr nat.choose_zero_right, ",", expr one_mul, ",", expr nat.cast_one, ",", expr mul_one, ",", expr mul_add, ",", expr add_mul, ",", expr nat.succ_sub (le_of_lt hi), ",", expr nat.succ_eq_add_one «expr - »(n, i), ",", expr pow_succ, ",", expr pow_mul, ",", expr add_sub_cancel, ",", expr mul_sum, ",", expr sum_mul, "]"] [],
  apply [expr sum_congr rfl],
  intros [ident j, ident hj],
  rw [expr mem_range] ["at", ident hj],
  rw ["[", expr ring_hom.map_mul, ",", expr ring_hom.map_mul, ",", expr ring_hom.map_pow, ",", expr ring_hom.map_pow, ",", expr ring_hom.map_pow, ",", expr ring_hom.map_pow, ",", expr ring_hom.map_pow, ",", expr map_C, ",", expr map_X, ",", expr mul_pow, "]"] [],
  rw ["[", expr mul_comm «expr ^ »(C «expr↑ »(p), i), ",", expr mul_comm _ «expr ^ »(«expr ^ »(X i, p), _), ",", expr mul_comm «expr ^ »(C «expr↑ »(p), «expr + »(j, 1)), ",", expr mul_comm (C «expr↑ »(p)), "]"] [],
  simp [] [] ["only"] ["[", expr mul_assoc, "]"] [] [],
  apply [expr congr_arg],
  apply [expr congr_arg],
  rw ["[", "<-", expr C_eq_coe_nat, "]"] [],
  simp [] [] ["only"] ["[", "<-", expr ring_hom.map_pow, ",", "<-", expr C_mul, "]"] [] [],
  rw [expr C_inj] [],
  simp [] [] ["only"] ["[", expr inv_of_eq_inv, ",", expr ring_hom.eq_int_cast, ",", expr inv_pow₀, ",", expr int.cast_coe_nat, ",", expr nat.cast_mul, "]"] [] [],
  rw ["[", expr rat.coe_nat_div _ _ (map_frobenius_poly.key₁ p «expr - »(n, i) j hj), "]"] [],
  simp [] [] ["only"] ["[", expr nat.cast_pow, ",", expr pow_add, ",", expr pow_one, "]"] [] [],
  suffices [] [":", expr «expr = »((«expr * »(«expr * »(«expr * »(«expr ^ »(p, «expr - »(n, i)).choose «expr + »(j, 1), «expr ^ »(p, «expr - »(j, exprv() p ⟨«expr + »(j, 1), j.succ_pos⟩))), p), «expr ^ »(p, n)) : exprℚ()), «expr * »(«expr * »(«expr * »(«expr ^ »(p, j), p), «expr * »(«expr ^ »(p, «expr - »(n, i)).choose «expr + »(j, 1), «expr ^ »(p, i))), «expr ^ »(p, «expr - »(«expr - »(n, i), exprv() p ⟨«expr + »(j, 1), j.succ_pos⟩))))],
  { have [ident aux] [":", expr ∀ k : exprℕ(), «expr ≠ »((«expr ^ »(p, k) : exprℚ()), 0)] [],
    { intro [],
      apply [expr pow_ne_zero],
      exact_mod_cast [expr hp.1.ne_zero] },
    simpa [] [] [] ["[", expr aux, ",", "-", ident one_div, "]"] ["with", ident field_simps] ["using", expr this.symm] },
  rw ["[", expr mul_comm _ (p : exprℚ()), ",", expr mul_assoc, ",", expr mul_assoc, ",", "<-", expr pow_add, ",", expr map_frobenius_poly.key₂ p hi hj, "]"] [],
  ring_exp [] []
end

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
        intros 
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

