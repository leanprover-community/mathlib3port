import Mathbin.Data.Polynomial.Basic 
import Mathbin.Data.Finset.NatAntidiagonal 
import Mathbin.Data.Nat.Choose.Sum

/-!
# Theory of univariate polynomials

The theorems include formulas for computing coefficients, such as
`coeff_add`, `coeff_sum`, `coeff_mul`

-/


noncomputable theory

open Finsupp Finset AddMonoidAlgebra

open_locale BigOperators

namespace Polynomial

universe u v

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiringₓ R] {p q r : Polynomial R}

section Coeff

theorem coeff_one (n : ℕ) : coeff (1 : Polynomial R) n = if 0 = n then 1 else 0 :=
  coeff_monomial

@[simp]
theorem coeff_add (p q : Polynomial R) (n : ℕ) : coeff (p+q) n = coeff p n+coeff q n :=
  by 
    rcases p with ⟨⟩
    rcases q with ⟨⟩
    simp [coeff, add_to_finsupp]

@[simp]
theorem coeff_smul [Monoidₓ S] [DistribMulAction S R] (r : S) (p : Polynomial R) (n : ℕ) :
  coeff (r • p) n = r • coeff p n :=
  by 
    rcases p with ⟨⟩
    simp [coeff, smul_to_finsupp]

theorem support_smul [Monoidₓ S] [DistribMulAction S R] (r : S) (p : Polynomial R) : support (r • p) ⊆ support p :=
  by 
    intro i hi 
    simp [mem_support_iff] at hi⊢
    contrapose! hi 
    simp [hi]

/-- `polynomial.sum` as a linear map. -/
@[simps]
def lsum {R A M : Type _} [Semiringₓ R] [Semiringₓ A] [AddCommMonoidₓ M] [Module R A] [Module R M] (f : ℕ → A →ₗ[R] M) :
  Polynomial A →ₗ[R] M :=
  { toFun := fun p => p.sum fun n r => f n r,
    map_add' := fun p q => sum_add_index p q _ (fun n => (f n).map_zero) fun n _ _ => (f n).map_add _ _,
    map_smul' :=
      fun c p =>
        by 
          rw [sum_eq_of_subset _ (fun n r => f n r) (fun n => (f n).map_zero) _ (support_smul c p)]
          simp only [sum_def, Finset.smul_sum, coeff_smul, LinearMap.map_smul, RingHom.id_apply] }

variable (R)

/-- The nth coefficient, as a linear map. -/
def lcoeff (n : ℕ) : Polynomial R →ₗ[R] R :=
  { toFun := fun p => coeff p n, map_add' := fun p q => coeff_add p q n, map_smul' := fun r p => coeff_smul r p n }

variable {R}

@[simp]
theorem lcoeff_apply (n : ℕ) (f : Polynomial R) : lcoeff R n f = coeff f n :=
  rfl

@[simp]
theorem finset_sum_coeff {ι : Type _} (s : Finset ι) (f : ι → Polynomial R) (n : ℕ) :
  coeff (∑b in s, f b) n = ∑b in s, coeff (f b) n :=
  (lcoeff R n).map_sum

theorem coeff_sum [Semiringₓ S] (n : ℕ) (f : ℕ → R → Polynomial S) :
  coeff (p.sum f) n = p.sum fun a b => coeff (f a b) n :=
  by 
    rcases p with ⟨⟩
    simp [Polynomial.sum, support, coeff]

/-- Decomposes the coefficient of the product `p * q` as a sum
over `nat.antidiagonal`. A version which sums over `range (n + 1)` can be obtained
by using `finset.nat.sum_antidiagonal_eq_sum_range_succ`. -/
theorem coeff_mul (p q : Polynomial R) (n : ℕ) : coeff (p*q) n = ∑x in nat.antidiagonal n, coeff p x.1*coeff q x.2 :=
  by 
    rcases p with ⟨⟩
    rcases q with ⟨⟩
    simp only [coeff, mul_to_finsupp]
    exact AddMonoidAlgebra.mul_apply_antidiagonal p q n _ fun x => nat.mem_antidiagonal

@[simp]
theorem mul_coeff_zero (p q : Polynomial R) : coeff (p*q) 0 = coeff p 0*coeff q 0 :=
  by 
    simp [coeff_mul]

theorem coeff_mul_X_zero (p : Polynomial R) : coeff (p*X) 0 = 0 :=
  by 
    simp 

theorem coeff_X_mul_zero (p : Polynomial R) : coeff (X*p) 0 = 0 :=
  by 
    simp 

theorem coeff_C_mul_X (x : R) (k n : ℕ) : coeff (C x*X ^ k : Polynomial R) n = if n = k then x else 0 :=
  by 
    rw [←monomial_eq_C_mul_X, coeff_monomial]
    congr 1
    simp [eq_comm]

@[simp]
theorem coeff_C_mul (p : Polynomial R) : coeff (C a*p) n = a*coeff p n :=
  by 
    rcases p with ⟨⟩
    simp only [C, monomial, monomial_fun, mul_to_finsupp, RingHom.coe_mk, coeff,
      AddMonoidAlgebra.single_zero_mul_apply p a n]

theorem C_mul' (a : R) (f : Polynomial R) : (C a*f) = a • f :=
  by 
    ext 
    rw [coeff_C_mul, coeff_smul, smul_eq_mul]

@[simp]
theorem coeff_mul_C (p : Polynomial R) (n : ℕ) (a : R) : coeff (p*C a) n = coeff p n*a :=
  by 
    rcases p with ⟨⟩
    simp only [C, monomial, monomial_fun, mul_to_finsupp, RingHom.coe_mk, coeff,
      AddMonoidAlgebra.mul_single_zero_apply p a n]

theorem coeff_X_pow (k n : ℕ) : coeff (X ^ k : Polynomial R) n = if n = k then 1 else 0 :=
  by 
    simp only [one_mulₓ, RingHom.map_one, ←coeff_C_mul_X]

@[simp]
theorem coeff_X_pow_self (n : ℕ) : coeff (X ^ n : Polynomial R) n = 1 :=
  by 
    simp [coeff_X_pow]

theorem coeff_mul_X_pow (p : Polynomial R) (n d : ℕ) : coeff (p*Polynomial.x ^ n) (d+n) = coeff p d :=
  by 
    rw [coeff_mul, sum_eq_single (d, n), coeff_X_pow, if_pos rfl, mul_oneₓ]
    ·
      rintro ⟨i, j⟩ h1 h2 
      rw [coeff_X_pow, if_neg, mul_zero]
      rintro rfl 
      apply h2 
      rw [nat.mem_antidiagonal, add_right_cancel_iffₓ] at h1 
      subst h1
    ·
      exact fun h1 => (h1 (nat.mem_antidiagonal.2 rfl)).elim

theorem coeff_mul_X_pow' (p : Polynomial R) (n d : ℕ) : (p*X ^ n).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 :=
  by 
    splitIfs
    ·
      rw [←tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right]
    ·
      refine' (coeff_mul _ _ _).trans (Finset.sum_eq_zero fun x hx => _)
      rw [coeff_X_pow, if_neg, mul_zero]
      exact
        ne_of_ltₓ
          (lt_of_le_of_ltₓ (Nat.le_of_add_le_right (le_of_eqₓ (finset.nat.mem_antidiagonal.mp hx))) (not_le.mp h))

@[simp]
theorem coeff_mul_X (p : Polynomial R) (n : ℕ) : coeff (p*X) (n+1) = coeff p n :=
  by 
    simpa only [pow_oneₓ] using coeff_mul_X_pow p 1 n

theorem mul_X_pow_eq_zero {p : Polynomial R} {n : ℕ} (H : (p*X ^ n) = 0) : p = 0 :=
  ext$ fun k => (coeff_mul_X_pow p n k).symm.trans$ ext_iff.1 H (k+n)

theorem C_mul_X_pow_eq_monomial (c : R) (n : ℕ) : (C c*X ^ n) = monomial n c :=
  by 
    ext1 
    rw [monomial_eq_smul_X, coeff_smul, coeff_C_mul, smul_eq_mul]

theorem support_mul_X_pow (c : R) (n : ℕ) (H : c ≠ 0) : (C c*X ^ n).Support = singleton n :=
  by 
    rw [C_mul_X_pow_eq_monomial, support_monomial n c H]

theorem support_C_mul_X_pow' {c : R} {n : ℕ} : (C c*X ^ n).Support ⊆ singleton n :=
  by 
    rw [C_mul_X_pow_eq_monomial]
    exact support_monomial' n c

-- error in Data.Polynomial.Coeff: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coeff_X_add_one_pow
(R : Type*)
[semiring R]
(n k : exprℕ()) : «expr = »(«expr ^ »(«expr + »(X, 1), n).coeff k, (n.choose k : R)) :=
begin
  rw ["[", expr (commute_X (1 : polynomial R)).add_pow, ",", "<-", expr lcoeff_apply, ",", expr linear_map.map_sum, "]"] [],
  simp [] [] ["only"] ["[", expr one_pow, ",", expr mul_one, ",", expr lcoeff_apply, ",", "<-", expr C_eq_nat_cast, ",", expr coeff_mul_C, ",", expr nat.cast_id, "]"] [] [],
  rw ["[", expr finset.sum_eq_single k, ",", expr coeff_X_pow_self, ",", expr one_mul, "]"] [],
  { intros ["_", "_"],
    simp [] [] ["only"] ["[", expr coeff_X_pow, ",", expr boole_mul, ",", expr ite_eq_right_iff, ",", expr ne.def, "]"] [] [] { contextual := tt },
    rintro [ident h, ident rfl],
    contradiction },
  { simp [] [] ["only"] ["[", expr coeff_X_pow_self, ",", expr one_mul, ",", expr not_lt, ",", expr finset.mem_range, "]"] [] [],
    intro [ident h],
    rw ["[", expr nat.choose_eq_zero_of_lt h, ",", expr nat.cast_zero, "]"] [] }
end

theorem coeff_one_add_X_pow (R : Type _) [Semiringₓ R] (n k : ℕ) : ((1+X) ^ n).coeff k = (n.choose k : R) :=
  by 
    rw [add_commₓ _ X, coeff_X_add_one_pow]

theorem C_dvd_iff_dvd_coeff (r : R) (φ : Polynomial R) : C r ∣ φ ↔ ∀ i, r ∣ φ.coeff i :=
  by 
    split 
    ·
      rintro ⟨φ, rfl⟩ c 
      rw [coeff_C_mul]
      apply dvd_mul_right
    ·
      intro h 
      choose c hc using h 
      classical 
      let c' : ℕ → R := fun i => if i ∈ φ.support then c i else 0
      let ψ : Polynomial R := ∑i in φ.support, monomial i (c' i)
      use ψ 
      ext i 
      simp only [ψ, c', coeff_C_mul, mem_support_iff, coeff_monomial, finset_sum_coeff, Finset.sum_ite_eq']
      splitIfs with hi hi
      ·
        rw [hc]
      ·
        rw [not_not] at hi 
        rwa [mul_zero]

theorem coeff_bit0_mul (P Q : Polynomial R) (n : ℕ) : coeff (bit0 P*Q) n = 2*coeff (P*Q) n :=
  by 
    simp [bit0, add_mulₓ]

theorem coeff_bit1_mul (P Q : Polynomial R) (n : ℕ) : coeff (bit1 P*Q) n = (2*coeff (P*Q) n)+coeff Q n :=
  by 
    simp [bit1, add_mulₓ, coeff_bit0_mul]

theorem smul_eq_C_mul (a : R) : a • p = C a*p :=
  by 
    simp [ext_iff]

theorem update_eq_add_sub_coeff {R : Type _} [Ringₓ R] (p : Polynomial R) (n : ℕ) (a : R) :
  p.update n a = p+Polynomial.c (a - p.coeff n)*Polynomial.x ^ n :=
  by 
    ext 
    rw [coeff_update_apply, coeff_add, coeff_C_mul_X]
    splitIfs with h <;> simp [h]

end Coeff

section cast

@[simp]
theorem nat_cast_coeff_zero {n : ℕ} {R : Type _} [Semiringₓ R] : (n : Polynomial R).coeff 0 = n :=
  by 
    induction' n with n ih
    ·
      simp 
    ·
      simp [ih]

@[simp, normCast]
theorem nat_cast_inj {m n : ℕ} {R : Type _} [Semiringₓ R] [CharZero R] :
  («expr↑ » m : Polynomial R) = «expr↑ » n ↔ m = n :=
  by 
    fsplit
    ·
      intro h 
      applyFun fun p => p.coeff 0  at h 
      simpa using h
    ·
      rintro rfl 
      rfl

@[simp]
theorem int_cast_coeff_zero {i : ℤ} {R : Type _} [Ringₓ R] : (i : Polynomial R).coeff 0 = i :=
  by 
    cases i <;> simp 

@[simp, normCast]
theorem int_cast_inj {m n : ℤ} {R : Type _} [Ringₓ R] [CharZero R] : («expr↑ » m : Polynomial R) = «expr↑ » n ↔ m = n :=
  by 
    fsplit
    ·
      intro h 
      applyFun fun p => p.coeff 0  at h 
      simpa using h
    ·
      rintro rfl 
      rfl

end cast

end Polynomial

