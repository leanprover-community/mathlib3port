import Mathbin.RingTheory.WittVector.Basic 
import Mathbin.RingTheory.WittVector.IsPoly

/-!
## The Verschiebung operator

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

open MvPolynomial

variable {p : ℕ} {R S : Type _} [hp : Fact p.prime] [CommRingₓ R] [CommRingₓ S]

local notation "𝕎" => WittVector p

noncomputable theory

/--
`verschiebung_fun x` shifts the coefficients of `x` up by one,
by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verchiebung_fun x).coeff (i + 1)`.

`verschiebung_fun` is the underlying function of the additive monoid hom `witt_vector.verschiebung`.
-/
def verschiebung_fun (x : 𝕎 R) : 𝕎 R :=
  mk p$ fun n => if n = 0 then 0 else x.coeff (n - 1)

theorem verschiebung_fun_coeff (x : 𝕎 R) (n : ℕ) :
  (verschiebung_fun x).coeff n = if n = 0 then 0 else x.coeff (n - 1) :=
  by 
    rw [verschiebung_fun, coeff_mk]

theorem verschiebung_fun_coeff_zero (x : 𝕎 R) : (verschiebung_fun x).coeff 0 = 0 :=
  by 
    rw [verschiebung_fun_coeff, if_pos rfl]

@[simp]
theorem verschiebung_fun_coeff_succ (x : 𝕎 R) (n : ℕ) : (verschiebung_fun x).coeff n.succ = x.coeff n :=
  rfl

include hp

@[ghost_simps]
theorem ghost_component_zero_verschiebung_fun (x : 𝕎 R) : ghost_component 0 (verschiebung_fun x) = 0 :=
  by 
    rw [ghost_component_apply, aeval_witt_polynomial, Finset.range_one, Finset.sum_singleton,
      verschiebung_fun_coeff_zero, pow_zeroₓ, pow_zeroₓ, pow_oneₓ, one_mulₓ]

@[ghost_simps]
theorem ghost_component_verschiebung_fun (x : 𝕎 R) (n : ℕ) :
  ghost_component (n+1) (verschiebung_fun x) = p*ghost_component n x :=
  by 
    simp only [ghost_component_apply, aeval_witt_polynomial]
    rw [Finset.sum_range_succ', verschiebung_fun_coeff, if_pos rfl, zero_pow (pow_pos hp.1.Pos _), mul_zero, add_zeroₓ,
      Finset.mul_sum, Finset.sum_congr rfl]
    rintro i -
    simp only [pow_succₓ, mul_assocₓ, verschiebung_fun_coeff, if_neg (Nat.succ_ne_zero i), Nat.succ_sub_succ, tsub_zero]

omit hp

/--
The 0th Verschiebung polynomial is 0. For `n > 0`, the `n`th Verschiebung polynomial is the
variable `X (n-1)`.
-/
def verschiebung_poly (n : ℕ) : MvPolynomial ℕ ℤ :=
  if n = 0 then 0 else X (n - 1)

@[simp]
theorem verschiebung_poly_zero : verschiebung_poly 0 = 0 :=
  rfl

theorem aeval_verschiebung_poly' (x : 𝕎 R) (n : ℕ) :
  aeval x.coeff (verschiebung_poly n) = (verschiebung_fun x).coeff n :=
  by 
    cases n
    ·
      simp only [verschiebung_poly, verschiebung_fun_coeff_zero, if_pos rfl, AlgHom.map_zero]
    ·
      rw [verschiebung_poly, verschiebung_fun_coeff_succ, if_neg n.succ_ne_zero, aeval_X, Nat.succ_eq_add_one,
        add_tsub_cancel_right]

variable (p)

/--
`witt_vector.verschiebung` has polynomial structure given by `witt_vector.verschiebung_poly`.
-/
@[isPoly]
theorem verschiebung_fun_is_poly : is_poly p fun R _Rcr => @verschiebung_fun p R _Rcr :=
  by 
    use verschiebung_poly 
    simp only [aeval_verschiebung_poly', eq_self_iff_true, forall_3_true_iff]

variable {p}

include hp

/--
`verschiebung x` shifts the coefficients of `x` up by one, by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verchiebung x).coeff (i + 1)`.

This is a additive monoid hom with underlying function `verschiebung_fun`.
-/
noncomputable def verschiebung : 𝕎 R →+ 𝕎 R :=
  { toFun := verschiebung_fun,
    map_zero' :=
      by 
        ext ⟨⟩ <;> rw [verschiebung_fun_coeff] <;> simp only [if_true, eq_self_iff_true, zero_coeff, if_t_t],
    map_add' :=
      by 
        ghostCalc _ _ 
        rintro ⟨⟩ <;> ghostSimp }

omit hp

/-- `witt_vector.verschiebung` is a polynomial function. -/
@[isPoly]
theorem verschiebung_is_poly : is_poly p fun R _Rcr => @verschiebung p R hp _Rcr :=
  verschiebung_fun_is_poly p

include hp

/-- verschiebung is a natural transformation -/
@[simp]
theorem map_verschiebung (f : R →+* S) (x : 𝕎 R) : map f (verschiebung x) = verschiebung (map f x) :=
  by 
    ext ⟨-, -⟩
    exact f.map_zero 
    rfl

@[ghost_simps]
theorem ghost_component_zero_verschiebung (x : 𝕎 R) : ghost_component 0 (verschiebung x) = 0 :=
  ghost_component_zero_verschiebung_fun _

@[ghost_simps]
theorem ghost_component_verschiebung (x : 𝕎 R) (n : ℕ) :
  ghost_component (n+1) (verschiebung x) = p*ghost_component n x :=
  ghost_component_verschiebung_fun _ _

@[simp]
theorem verschiebung_coeff_zero (x : 𝕎 R) : (verschiebung x).coeff 0 = 0 :=
  rfl

theorem verschiebung_coeff_add_one (x : 𝕎 R) (n : ℕ) : (verschiebung x).coeff (n+1) = x.coeff n :=
  rfl

@[simp]
theorem verschiebung_coeff_succ (x : 𝕎 R) (n : ℕ) : (verschiebung x).coeff n.succ = x.coeff n :=
  rfl

theorem aeval_verschiebung_poly (x : 𝕎 R) (n : ℕ) : aeval x.coeff (verschiebung_poly n) = (verschiebung x).coeff n :=
  aeval_verschiebung_poly' x n

@[simp]
theorem bind₁_verschiebung_poly_witt_polynomial (n : ℕ) :
  bind₁ verschiebung_poly (wittPolynomial p ℤ n) = if n = 0 then 0 else p*wittPolynomial p ℤ (n - 1) :=
  by 
    apply MvPolynomial.funext 
    intro x 
    splitIfs with hn
    ·
      simp only [hn, verschiebung_poly_zero, witt_polynomial_zero, bind₁_X_right]
    ·
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn 
      rw [Nat.succ_eq_add_one, add_tsub_cancel_right, RingHom.map_mul, RingHom.map_nat_cast, hom_bind₁]
      calc _ = ghost_component (n+1) (verschiebung$ mk p x) := _ _ = _ := _
      ·
        apply eval₂_hom_congr (RingHom.ext_int _ _) _ rfl 
        simp only [←aeval_verschiebung_poly, coeff_mk]
        funext k 
        exact eval₂_hom_congr (RingHom.ext_int _ _) rfl rfl
      ·
        rw [ghost_component_verschiebung]
        congr 1 
        exact eval₂_hom_congr (RingHom.ext_int _ _) rfl rfl

end WittVector

