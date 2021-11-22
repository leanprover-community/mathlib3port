import Mathbin.Data.MvPolynomial.Default 
import Mathbin.LinearAlgebra.StdBasis 
import Mathbin.RingTheory.Ideal.LocalRing 
import Mathbin.RingTheory.Multiplicity 
import Mathbin.RingTheory.AlgebraTower 
import Mathbin.Tactic.Linarith.Default 
import Mathbin.Algebra.BigOperators.NatAntidiagonal

/-!
# Formal power series

This file defines (multivariate) formal power series
and develops the basic properties of these objects.

A formal power series is to a polynomial like an infinite sum is to a finite sum.

We provide the natural inclusion from polynomials to formal power series.

## Generalities

The file starts with setting up the (semi)ring structure on multivariate power series.

`trunc n φ` truncates a formal power series to the polynomial
that has the same coefficients as `φ`, for all `m ≤ n`, and `0` otherwise.

If the constant coefficient of a formal power series is invertible,
then this formal power series is invertible.

Formal power series over a local ring form a local ring.

## Formal power series in one variable

We prove that if the ring of coefficients is an integral domain,
then formal power series in one variable form an integral domain.

The `order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `order` is a valuation
(`order_mul`, `le_order_add`).

## Implementation notes

In this file we define multivariate formal power series with
variables indexed by `σ` and coefficients in `R` as
`mv_power_series σ R := (σ →₀ ℕ) → R`.
Unfortunately there is not yet enough API to show that they are the completion
of the ring of multivariate polynomials. However, we provide most of the infrastructure
that is needed to do this. Once I-adic completion (topological or algebraic) is available
it should not be hard to fill in the details.

Formal power series in one variable are defined as
`power_series R := mv_power_series unit R`.

This allows us to port a lot of proofs and properties
from the multivariate case to the single variable case.
However, it means that formal power series are indexed by `unit →₀ ℕ`,
which is of course canonically isomorphic to `ℕ`.
We then build some glue to treat formal power series as if they are indexed by `ℕ`.
Occasionally this leads to proofs that are uglier than expected.
-/


noncomputable theory

open_locale Classical BigOperators

/-- Multivariate formal power series, where `σ` is the index set of the variables
and `R` is the coefficient ring.-/
def MvPowerSeries (σ : Type _) (R : Type _) :=
  (σ →₀ ℕ) → R

namespace MvPowerSeries

open Finsupp

variable{σ R : Type _}

instance  [Inhabited R] : Inhabited (MvPowerSeries σ R) :=
  ⟨fun _ => default _⟩

instance  [HasZero R] : HasZero (MvPowerSeries σ R) :=
  Pi.hasZero

instance  [AddMonoidₓ R] : AddMonoidₓ (MvPowerSeries σ R) :=
  Pi.addMonoid

instance  [AddGroupₓ R] : AddGroupₓ (MvPowerSeries σ R) :=
  Pi.addGroup

instance  [AddCommMonoidₓ R] : AddCommMonoidₓ (MvPowerSeries σ R) :=
  Pi.addCommMonoid

instance  [AddCommGroupₓ R] : AddCommGroupₓ (MvPowerSeries σ R) :=
  Pi.addCommGroup

instance  [Nontrivial R] : Nontrivial (MvPowerSeries σ R) :=
  Function.nontrivial

instance  {A} [Semiringₓ R] [AddCommMonoidₓ A] [Module R A] : Module R (MvPowerSeries σ A) :=
  Pi.module _ _ _

instance  {A S} [Semiringₓ R] [Semiringₓ S] [AddCommMonoidₓ A] [Module R A] [Module S A] [HasScalar R S]
  [IsScalarTower R S A] : IsScalarTower R S (MvPowerSeries σ A) :=
  Pi.is_scalar_tower

section Semiringₓ

variable(R)[Semiringₓ R]

/-- The `n`th monomial with coefficient `a` as multivariate formal power series.-/
def monomial (n : σ →₀ ℕ) : R →ₗ[R] MvPowerSeries σ R :=
  LinearMap.stdBasis R _ n

/-- The `n`th coefficient of a multivariate formal power series.-/
def coeff (n : σ →₀ ℕ) : MvPowerSeries σ R →ₗ[R] R :=
  LinearMap.proj n

variable{R}

/-- Two multivariate formal power series are equal if all their coefficients are equal.-/
@[ext]
theorem ext {φ ψ} (h : ∀ n : σ →₀ ℕ, coeff R n φ = coeff R n ψ) : φ = ψ :=
  funext h

/-- Two multivariate formal power series are equal
 if and only if all their coefficients are equal.-/
theorem ext_iff {φ ψ : MvPowerSeries σ R} : φ = ψ ↔ ∀ n : σ →₀ ℕ, coeff R n φ = coeff R n ψ :=
  Function.funext_iffₓ

theorem monomial_def [DecidableEq σ] (n : σ →₀ ℕ) : monomial R n = LinearMap.stdBasis R _ n :=
  by 
    convert rfl

theorem coeff_monomial [DecidableEq σ] (m n : σ →₀ ℕ) (a : R) : coeff R m (monomial R n a) = if m = n then a else 0 :=
  by 
    rw [coeff, monomial_def, LinearMap.proj_apply, LinearMap.std_basis_apply, Function.update_apply, Pi.zero_apply]

@[simp]
theorem coeff_monomial_same (n : σ →₀ ℕ) (a : R) : coeff R n (monomial R n a) = a :=
  LinearMap.std_basis_same R _ n a

theorem coeff_monomial_ne {m n : σ →₀ ℕ} (h : m ≠ n) (a : R) : coeff R m (monomial R n a) = 0 :=
  LinearMap.std_basis_ne R _ _ _ h a

theorem eq_of_coeff_monomial_ne_zero {m n : σ →₀ ℕ} {a : R} (h : coeff R m (monomial R n a) ≠ 0) : m = n :=
  by_contra$ fun h' => h$ coeff_monomial_ne h' a

@[simp]
theorem coeff_comp_monomial (n : σ →₀ ℕ) : (coeff R n).comp (monomial R n) = LinearMap.id :=
  LinearMap.ext$ coeff_monomial_same n

@[simp]
theorem coeff_zero (n : σ →₀ ℕ) : coeff R n (0 : MvPowerSeries σ R) = 0 :=
  rfl

variable(m n : σ →₀ ℕ)(φ ψ : MvPowerSeries σ R)

instance  : HasOne (MvPowerSeries σ R) :=
  ⟨monomial R (0 : σ →₀ ℕ) 1⟩

theorem coeff_one [DecidableEq σ] : coeff R n (1 : MvPowerSeries σ R) = if n = 0 then 1 else 0 :=
  coeff_monomial _ _ _

theorem coeff_zero_one : coeff R (0 : σ →₀ ℕ) 1 = 1 :=
  coeff_monomial_same 0 1

theorem monomial_zero_one : monomial R (0 : σ →₀ ℕ) 1 = 1 :=
  rfl

instance  : Mul (MvPowerSeries σ R) :=
  ⟨fun φ ψ n => ∑p in Finsupp.antidiagonal n, coeff R p.1 φ*coeff R p.2 ψ⟩

theorem coeff_mul : coeff R n (φ*ψ) = ∑p in Finsupp.antidiagonal n, coeff R p.1 φ*coeff R p.2 ψ :=
  rfl

protected theorem zero_mul : ((0 : MvPowerSeries σ R)*φ) = 0 :=
  ext$
    fun n =>
      by 
        simp [coeff_mul]

protected theorem mul_zero : (φ*0) = 0 :=
  ext$
    fun n =>
      by 
        simp [coeff_mul]

theorem coeff_monomial_mul (a : R) : coeff R m (monomial R n a*φ) = if n ≤ m then a*coeff R (m - n) φ else 0 :=
  by 
    have  :
      ∀ p _ : p ∈ antidiagonal m, (coeff R (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 (monomial R n a)*coeff R p.2 φ) ≠ 0 → p.1 = n :=
      fun p _ hp => eq_of_coeff_monomial_ne_zero (left_ne_zero_of_mul hp)
    rw [coeff_mul, ←Finset.sum_filter_of_ne this, antidiagonal_filter_fst_eq, Finset.sum_ite_index]
    simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]

theorem coeff_mul_monomial (a : R) : coeff R m (φ*monomial R n a) = if n ≤ m then coeff R (m - n) φ*a else 0 :=
  by 
    have  :
      ∀ p _ : p ∈ antidiagonal m, (coeff R (p : (σ →₀ ℕ) × (σ →₀ ℕ)).1 φ*coeff R p.2 (monomial R n a)) ≠ 0 → p.2 = n :=
      fun p _ hp => eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hp)
    rw [coeff_mul, ←Finset.sum_filter_of_ne this, antidiagonal_filter_snd_eq, Finset.sum_ite_index]
    simp only [Finset.sum_singleton, coeff_monomial_same, Finset.sum_empty]

theorem coeff_add_monomial_mul (a : R) : coeff R (m+n) (monomial R m a*φ) = a*coeff R n φ :=
  by 
    rw [coeff_monomial_mul, if_pos, add_tsub_cancel_left]
    exact le_add_right le_rfl

theorem coeff_add_mul_monomial (a : R) : coeff R (m+n) (φ*monomial R n a) = coeff R m φ*a :=
  by 
    rw [coeff_mul_monomial, if_pos, add_tsub_cancel_right]
    exact le_add_left le_rfl

protected theorem one_mulₓ : ((1 : MvPowerSeries σ R)*φ) = φ :=
  ext$
    fun n =>
      by 
        simpa using coeff_add_monomial_mul 0 n φ 1

protected theorem mul_oneₓ : (φ*1) = φ :=
  ext$
    fun n =>
      by 
        simpa using coeff_add_mul_monomial n 0 φ 1

protected theorem mul_addₓ (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : (φ₁*φ₂+φ₃) = (φ₁*φ₂)+φ₁*φ₃ :=
  ext$
    fun n =>
      by 
        simp only [coeff_mul, mul_addₓ, Finset.sum_add_distrib, LinearMap.map_add]

protected theorem add_mulₓ (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : ((φ₁+φ₂)*φ₃) = (φ₁*φ₃)+φ₂*φ₃ :=
  ext$
    fun n =>
      by 
        simp only [coeff_mul, add_mulₓ, Finset.sum_add_distrib, LinearMap.map_add]

protected theorem mul_assocₓ (φ₁ φ₂ φ₃ : MvPowerSeries σ R) : ((φ₁*φ₂)*φ₃) = φ₁*φ₂*φ₃ :=
  by 
    ext1 n 
    simp only [coeff_mul, Finset.sum_mul, Finset.mul_sum, Finset.sum_sigma']
    refine' Finset.sum_bij (fun p _ => ⟨(p.2.1, p.2.2+p.1.2), (p.2.2, p.1.2)⟩) _ _ _ _ <;>
      simp only [mem_antidiagonal, Finset.mem_sigma, heq_iff_eq, Prod.mk.inj_iffₓ, and_imp, exists_prop]
    ·
      rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩
      dsimp only 
      rintro rfl rfl 
      simp [add_assocₓ]
    ·
      rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
      dsimp only 
      rintro rfl rfl 
      apply mul_assocₓ
    ·
      rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩
      dsimp only 
      rintro rfl rfl - rfl rfl - rfl rfl 
      rfl
    ·
      rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩
      dsimp only 
      rintro rfl rfl 
      refine' ⟨⟨(i+k, l), (i, k)⟩, _, _⟩ <;> simp [add_assocₓ]

instance  : Semiringₓ (MvPowerSeries σ R) :=
  { MvPowerSeries.hasOne, MvPowerSeries.hasMul, MvPowerSeries.addCommMonoid with mul_one := MvPowerSeries.mul_one,
    one_mul := MvPowerSeries.one_mul, mul_assoc := MvPowerSeries.mul_assoc, mul_zero := MvPowerSeries.mul_zero,
    zero_mul := MvPowerSeries.zero_mul, left_distrib := MvPowerSeries.mul_add, right_distrib := MvPowerSeries.add_mul }

end Semiringₓ

instance  [CommSemiringₓ R] : CommSemiringₓ (MvPowerSeries σ R) :=
  { MvPowerSeries.semiring with
    mul_comm :=
      fun φ ψ =>
        ext$
          fun n =>
            by 
              simpa only [coeff_mul, mul_commₓ] using sum_antidiagonal_swap n fun a b => coeff R a φ*coeff R b ψ }

instance  [Ringₓ R] : Ringₓ (MvPowerSeries σ R) :=
  { MvPowerSeries.semiring, MvPowerSeries.addCommGroup with  }

instance  [CommRingₓ R] : CommRingₓ (MvPowerSeries σ R) :=
  { MvPowerSeries.commSemiring, MvPowerSeries.addCommGroup with  }

section Semiringₓ

variable[Semiringₓ R]

theorem monomial_mul_monomial (m n : σ →₀ ℕ) (a b : R) : (monomial R m a*monomial R n b) = monomial R (m+n) (a*b) :=
  by 
    ext k 
    simp only [coeff_mul_monomial, coeff_monomial]
    splitIfs with h₁ h₂ h₃ h₃ h₂ <;>
      try 
        rfl
    ·
      rw [←h₂, tsub_add_cancel_of_le h₁] at h₃ 
      exact (h₃ rfl).elim
    ·
      rw [h₃, add_tsub_cancel_right] at h₂ 
      exact (h₂ rfl).elim
    ·
      exact zero_mul b
    ·
      rw [h₂] at h₁ 
      exact (h₁$ le_add_left le_rfl).elim

variable(σ)(R)

/-- The constant multivariate formal power series.-/
def C : R →+* MvPowerSeries σ R :=
  { monomial R (0 : σ →₀ ℕ) with map_one' := rfl, map_mul' := fun a b => (monomial_mul_monomial 0 0 a b).symm,
    map_zero' := (monomial R (0 : _)).map_zero }

variable{σ}{R}

@[simp]
theorem monomial_zero_eq_C : «expr⇑ » (monomial R (0 : σ →₀ ℕ)) = C σ R :=
  rfl

theorem monomial_zero_eq_C_apply (a : R) : monomial R (0 : σ →₀ ℕ) a = C σ R a :=
  rfl

theorem coeff_C [DecidableEq σ] (n : σ →₀ ℕ) (a : R) : coeff R n (C σ R a) = if n = 0 then a else 0 :=
  coeff_monomial _ _ _

theorem coeff_zero_C (a : R) : coeff R (0 : σ →₀ ℕ) (C σ R a) = a :=
  coeff_monomial_same 0 a

/-- The variables of the multivariate formal power series ring.-/
def X (s : σ) : MvPowerSeries σ R :=
  monomial R (single s 1) 1

theorem coeff_X [DecidableEq σ] (n : σ →₀ ℕ) (s : σ) :
  coeff R n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0 :=
  coeff_monomial _ _ _

theorem coeff_index_single_X [DecidableEq σ] (s t : σ) :
  coeff R (single t 1) (X s : MvPowerSeries σ R) = if t = s then 1 else 0 :=
  by 
    simp only [coeff_X, single_left_inj one_ne_zero]
    splitIfs <;> rfl

@[simp]
theorem coeff_index_single_self_X (s : σ) : coeff R (single s 1) (X s : MvPowerSeries σ R) = 1 :=
  coeff_monomial_same _ _

theorem coeff_zero_X (s : σ) : coeff R (0 : σ →₀ ℕ) (X s : MvPowerSeries σ R) = 0 :=
  by 
    rw [coeff_X, if_neg]
    intro h 
    exact one_ne_zero (single_eq_zero.mp h.symm)

theorem X_def (s : σ) : X s = monomial R (single s 1) 1 :=
  rfl

theorem X_pow_eq (s : σ) (n : ℕ) : ((X s : MvPowerSeries σ R)^n) = monomial R (single s n) 1 :=
  by 
    induction' n with n ih
    ·
      rw [pow_zeroₓ, Finsupp.single_zero, monomial_zero_one]
    ·
      rw [pow_succ'ₓ, ih, Nat.succ_eq_add_one, Finsupp.single_add, X, monomial_mul_monomial, one_mulₓ]

theorem coeff_X_pow [DecidableEq σ] (m : σ →₀ ℕ) (s : σ) (n : ℕ) :
  coeff R m ((X s : MvPowerSeries σ R)^n) = if m = single s n then 1 else 0 :=
  by 
    rw [X_pow_eq s n, coeff_monomial]

@[simp]
theorem coeff_mul_C (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) : coeff R n (φ*C σ R a) = coeff R n φ*a :=
  by 
    simpa using coeff_add_mul_monomial n 0 φ a

@[simp]
theorem coeff_C_mul (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (a : R) : coeff R n (C σ R a*φ) = a*coeff R n φ :=
  by 
    simpa using coeff_add_monomial_mul 0 n φ a

theorem coeff_zero_mul_X (φ : MvPowerSeries σ R) (s : σ) : coeff R (0 : σ →₀ ℕ) (φ*X s) = 0 :=
  by 
    have  : ¬single s 1 ≤ 0 
    exact
      fun h =>
        by 
          simpa using h s 
    simp only [X, coeff_mul_monomial, if_neg this]

theorem coeff_zero_X_mul (φ : MvPowerSeries σ R) (s : σ) : coeff R (0 : σ →₀ ℕ) (X s*φ) = 0 :=
  by 
    have  : ¬single s 1 ≤ 0 
    exact
      fun h =>
        by 
          simpa using h s 
    simp only [X, coeff_monomial_mul, if_neg this]

variable(σ)(R)

/-- The constant coefficient of a formal power series.-/
def constant_coeff : MvPowerSeries σ R →+* R :=
  { coeff R (0 : σ →₀ ℕ) with toFun := coeff R (0 : σ →₀ ℕ), map_one' := coeff_zero_one,
    map_mul' :=
      fun φ ψ =>
        by 
          simp [coeff_mul, support_single_ne_zero],
    map_zero' := LinearMap.map_zero _ }

variable{σ}{R}

@[simp]
theorem coeff_zero_eq_constant_coeff : «expr⇑ » (coeff R (0 : σ →₀ ℕ)) = constant_coeff σ R :=
  rfl

theorem coeff_zero_eq_constant_coeff_apply (φ : MvPowerSeries σ R) : coeff R (0 : σ →₀ ℕ) φ = constant_coeff σ R φ :=
  rfl

@[simp]
theorem constant_coeff_C (a : R) : constant_coeff σ R (C σ R a) = a :=
  rfl

@[simp]
theorem constant_coeff_comp_C : (constant_coeff σ R).comp (C σ R) = RingHom.id R :=
  rfl

@[simp]
theorem constant_coeff_zero : constant_coeff σ R 0 = 0 :=
  rfl

@[simp]
theorem constant_coeff_one : constant_coeff σ R 1 = 1 :=
  rfl

@[simp]
theorem constant_coeff_X (s : σ) : constant_coeff σ R (X s) = 0 :=
  coeff_zero_X s

/-- If a multivariate formal power series is invertible,
 then so is its constant coefficient.-/
theorem is_unit_constant_coeff (φ : MvPowerSeries σ R) (h : IsUnit φ) : IsUnit (constant_coeff σ R φ) :=
  h.map (constant_coeff σ R).toMonoidHom

@[simp]
theorem coeff_smul (f : MvPowerSeries σ R) n (a : R) : coeff _ n (a • f) = a*coeff _ n f :=
  rfl

theorem X_inj [Nontrivial R] {s t : σ} : (X s : MvPowerSeries σ R) = X t ↔ s = t :=
  ⟨by 
      intro h 
      replace h := congr_argₓ (coeff R (single s 1)) h 
      rw [coeff_X, if_pos rfl, coeff_X] at h 
      splitIfs  at h with H
      ·
        rw [Finsupp.single_eq_single_iff] at H 
        cases H
        ·
          exact H.1
        ·
          exFalso 
          exact one_ne_zero H.1
      ·
        exFalso 
        exact one_ne_zero h,
    congr_argₓ X⟩

end Semiringₓ

section Map

variable{S T : Type _}[Semiringₓ R][Semiringₓ S][Semiringₓ T]

variable(f : R →+* S)(g : S →+* T)

variable(σ)

/-- The map between multivariate formal power series induced by a map on the coefficients.-/
def map : MvPowerSeries σ R →+* MvPowerSeries σ S :=
  { toFun := fun φ n => f$ coeff R n φ, map_zero' := ext$ fun n => f.map_zero,
    map_one' :=
      ext$
        fun n =>
          show f ((coeff R n) 1) = (coeff S n) 1by 
            rw [coeff_one, coeff_one]
            splitIfs <;> simp [f.map_one, f.map_zero],
    map_add' :=
      fun φ ψ =>
        ext$
          fun n =>
            show f ((coeff R n) (φ+ψ)) = f ((coeff R n) φ)+f ((coeff R n) ψ)by 
              simp ,
    map_mul' :=
      fun φ ψ =>
        ext$
          fun n =>
            show f _ = _ by 
              rw [coeff_mul, f.map_sum, coeff_mul, Finset.sum_congr rfl]
              rintro ⟨i, j⟩ hij 
              rw [f.map_mul]
              rfl }

variable{σ}

@[simp]
theorem map_id : map σ (RingHom.id R) = RingHom.id _ :=
  rfl

theorem map_comp : map σ (g.comp f) = (map σ g).comp (map σ f) :=
  rfl

@[simp]
theorem coeff_map (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) : coeff S n (map σ f φ) = f (coeff R n φ) :=
  rfl

@[simp]
theorem constant_coeff_map (φ : MvPowerSeries σ R) : constant_coeff σ S (map σ f φ) = f (constant_coeff σ R φ) :=
  rfl

@[simp]
theorem map_monomial (n : σ →₀ ℕ) (a : R) : map σ f (monomial R n a) = monomial S n (f a) :=
  by 
    ext m 
    simp [coeff_monomial, apply_ite f]

@[simp]
theorem map_C (a : R) : map σ f (C σ R a) = C σ S (f a) :=
  map_monomial _ _ _

@[simp]
theorem map_X (s : σ) : map σ f (X s) = X s :=
  by 
    simp [X]

end Map

section Algebra

variable{A : Type _}[CommSemiringₓ R][Semiringₓ A][Algebra R A]

instance  : Algebra R (MvPowerSeries σ A) :=
  { MvPowerSeries.module with
    commutes' :=
      fun a φ =>
        by 
          ext n 
          simp [Algebra.commutes],
    smul_def' :=
      fun a σ =>
        by 
          ext n 
          simp [(coeff A n).map_smul_of_tower a, Algebra.smul_def],
    toRingHom := (MvPowerSeries.map σ (algebraMap R A)).comp (C σ R) }

theorem C_eq_algebra_map : C σ R = algebraMap R (MvPowerSeries σ R) :=
  rfl

theorem algebra_map_apply {r : R} : algebraMap R (MvPowerSeries σ A) r = C σ A (algebraMap R A r) :=
  by 
    change (MvPowerSeries.map σ (algebraMap R A)).comp (C σ R) r = _ 
    simp 

instance  [Nonempty σ] [Nontrivial R] : Nontrivial (Subalgebra R (MvPowerSeries σ R)) :=
  ⟨⟨⊥, ⊤,
      by 
        rw [Ne.def, SetLike.ext_iff, not_forall]
        inhabit σ 
        refine' ⟨X (default σ), _⟩
        simp only [Algebra.mem_bot, not_exists, Set.mem_range, iff_trueₓ, Algebra.mem_top]
        intro x 
        rw [ext_iff, not_forall]
        refine' ⟨Finsupp.single (default σ) 1, _⟩
        simp [algebra_map_apply, coeff_C]⟩⟩

end Algebra

section Trunc

variable[CommSemiringₓ R](n : σ →₀ ℕ)

/-- Auxiliary definition for the truncation function. -/
def trunc_fun (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑m in Iic_finset n, MvPolynomial.monomial m (coeff R m φ)

theorem coeff_trunc_fun (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
  (trunc_fun n φ).coeff m = if m ≤ n then coeff R m φ else 0 :=
  by 
    simp [trunc_fun, MvPolynomial.coeff_sum]

variable(R)

/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial -/
def Trunc : MvPowerSeries σ R →+ MvPolynomial σ R :=
  { toFun := trunc_fun n,
    map_zero' :=
      by 
        ext 
        simp [coeff_trunc_fun],
    map_add' :=
      by 
        intros 
        ext 
        simp [coeff_trunc_fun, ite_add]
        splitIfs <;> rfl }

variable{R}

theorem coeff_trunc (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) : (Trunc R n φ).coeff m = if m ≤ n then coeff R m φ else 0 :=
  by 
    simp [Trunc, coeff_trunc_fun]

@[simp]
theorem trunc_one : Trunc R n 1 = 1 :=
  MvPolynomial.ext _ _$
    fun m =>
      by 
        rw [coeff_trunc, coeff_one]
        splitIfs with H H' H'
        ·
          subst m 
          simp 
        ·
          symm 
          rw [MvPolynomial.coeff_one]
          exact if_neg (Ne.symm H')
        ·
          symm 
          rw [MvPolynomial.coeff_one]
          refine' if_neg _ 
          intro H' 
          apply H 
          subst m 
          intro s 
          exact Nat.zero_leₓ _

@[simp]
theorem trunc_C (a : R) : Trunc R n (C σ R a) = MvPolynomial.c a :=
  MvPolynomial.ext _ _$
    fun m =>
      by 
        rw [coeff_trunc, coeff_C, MvPolynomial.coeff_C]
        splitIfs with H <;>
          first |
            rfl|
            try 
              simp_all 
        exFalso 
        apply H 
        subst m 
        intro s 
        exact Nat.zero_leₓ _

end Trunc

section CommSemiringₓ

variable[CommSemiringₓ R]

theorem X_pow_dvd_iff {s : σ} {n : ℕ} {φ : MvPowerSeries σ R} :
  ((X s : MvPowerSeries σ R)^n) ∣ φ ↔ ∀ m : σ →₀ ℕ, m s < n → coeff R m φ = 0 :=
  by 
    split 
    ·
      rintro ⟨φ, rfl⟩ m h 
      rw [coeff_mul, Finset.sum_eq_zero]
      rintro ⟨i, j⟩ hij 
      rw [coeff_X_pow, if_neg, zero_mul]
      contrapose! h 
      subst i 
      rw [Finsupp.mem_antidiagonal] at hij 
      rw [←hij, Finsupp.add_apply, Finsupp.single_eq_same]
      exact Nat.le_add_rightₓ n _
    ·
      intro h 
      refine' ⟨fun m => coeff R (m+single s n) φ, _⟩
      ext m 
      byCases' H : ((m - single s n)+single s n) = m
      ·
        rw [coeff_mul, Finset.sum_eq_single (single s n, m - single s n)]
        ·
          rw [coeff_X_pow, if_pos rfl, one_mulₓ]
          simpa using congr_argₓ (fun m : σ →₀ ℕ => coeff R m φ) H.symm
        ·
          rintro ⟨i, j⟩ hij hne 
          rw [Finsupp.mem_antidiagonal] at hij 
          rw [coeff_X_pow]
          splitIfs with hi
          ·
            exFalso 
            apply hne 
            rw [←hij, ←hi, Prod.mk.inj_iffₓ]
            refine' ⟨rfl, _⟩
            ext t 
            simp only [add_tsub_cancel_left, Finsupp.add_apply, Finsupp.tsub_apply]
          ·
            exact zero_mul _
        ·
          intro hni 
          exFalso 
          apply hni 
          rwa [Finsupp.mem_antidiagonal, add_commₓ]
      ·
        rw [h, coeff_mul, Finset.sum_eq_zero]
        ·
          rintro ⟨i, j⟩ hij 
          rw [Finsupp.mem_antidiagonal] at hij 
          rw [coeff_X_pow]
          splitIfs with hi
          ·
            exFalso 
            apply H 
            rw [←hij, hi]
            ext 
            rw [coe_add, coe_add, Pi.add_apply, Pi.add_apply, add_tsub_cancel_left, add_commₓ]
          ·
            exact zero_mul _
        ·
          classical 
          contrapose! H 
          ext t 
          byCases' hst : s = t
          ·
            subst t 
            simpa using tsub_add_cancel_of_le H
          ·
            simp [Finsupp.single_apply, hst]

theorem X_dvd_iff {s : σ} {φ : MvPowerSeries σ R} :
  (X s : MvPowerSeries σ R) ∣ φ ↔ ∀ m : σ →₀ ℕ, m s = 0 → coeff R m φ = 0 :=
  by 
    rw [←pow_oneₓ (X s : MvPowerSeries σ R), X_pow_dvd_iff]
    split  <;> intro h m hm
    ·
      exact h m (hm.symm ▸ zero_lt_one)
    ·
      exact h m (Nat.eq_zero_of_le_zeroₓ$ Nat.le_of_succ_le_succₓ hm)

end CommSemiringₓ

section Ringₓ

variable[Ringₓ R]

/-- Auxiliary definition that unifies
 the totalised inverse formal power series `(_)⁻¹` and
 the inverse formal power series that depends on
 an inverse of the constant coefficient `inv_of_unit`.-/
protected noncomputable def inv.aux (a : R) (φ : MvPowerSeries σ R) : MvPowerSeries σ R
| n => if n = 0 then a else (-a)*∑x in n.antidiagonal, if h : x.2 < n then coeff R x.1 φ*inv.aux x.2 else 0

theorem coeff_inv_aux [DecidableEq σ] (n : σ →₀ ℕ) (a : R) (φ : MvPowerSeries σ R) :
  coeff R n (inv.aux a φ) =
    if n = 0 then a else (-a)*∑x in n.antidiagonal, if x.2 < n then coeff R x.1 φ*coeff R x.2 (inv.aux a φ) else 0 :=
  show inv.aux a φ n = _ by 
    rw [inv.aux]
    convert rfl

/-- A multivariate formal power series is invertible if the constant coefficient is invertible.-/
def inv_of_unit (φ : MvPowerSeries σ R) (u : Units R) : MvPowerSeries σ R :=
  inv.aux («expr↑ » (u⁻¹)) φ

theorem coeff_inv_of_unit [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (u : Units R) :
  coeff R n (inv_of_unit φ u) =
    if n = 0 then «expr↑ » (u⁻¹) else
      (-«expr↑ » (u⁻¹))*∑x in n.antidiagonal, if x.2 < n then coeff R x.1 φ*coeff R x.2 (inv_of_unit φ u) else 0 :=
  coeff_inv_aux n («expr↑ » (u⁻¹)) φ

@[simp]
theorem constant_coeff_inv_of_unit (φ : MvPowerSeries σ R) (u : Units R) :
  constant_coeff σ R (inv_of_unit φ u) = «expr↑ » (u⁻¹) :=
  by 
    rw [←coeff_zero_eq_constant_coeff_apply, coeff_inv_of_unit, if_pos rfl]

theorem mul_inv_of_unit (φ : MvPowerSeries σ R) (u : Units R) (h : constant_coeff σ R φ = u) :
  (φ*inv_of_unit φ u) = 1 :=
  ext$
    fun n =>
      if H : n = 0 then
        by 
          rw [H]
          simp [coeff_mul, support_single_ne_zero, h]
      else
        by 
          have  : ((0 : σ →₀ ℕ), n) ∈ n.antidiagonal
          ·
            rw [Finsupp.mem_antidiagonal, zero_addₓ]
          rw [coeff_one, if_neg H, coeff_mul, ←Finset.insert_erase this, Finset.sum_insert (Finset.not_mem_erase _ _),
            coeff_zero_eq_constant_coeff_apply, h, coeff_inv_of_unit, if_neg H, neg_mul_eq_neg_mul_symm,
            mul_neg_eq_neg_mul_symm, Units.mul_inv_cancel_left, ←Finset.insert_erase this,
            Finset.sum_insert (Finset.not_mem_erase _ _), Finset.insert_erase this, if_neg (not_lt_of_geₓ$ le_reflₓ _),
            zero_addₓ, add_commₓ, ←sub_eq_add_neg, sub_eq_zero, Finset.sum_congr rfl]
          rintro ⟨i, j⟩ hij 
          rw [Finset.mem_erase, Finsupp.mem_antidiagonal] at hij 
          cases' hij with h₁ h₂ 
          subst n 
          rw [if_pos]
          suffices  : ((0 : _)+j) < i+j
          ·
            simpa 
          apply add_lt_add_right 
          split 
          ·
            intro s 
            exact Nat.zero_leₓ _
          ·
            intro H 
            apply h₁ 
            suffices  : i = 0
            ·
              simp [this]
            ext1 s 
            exact Nat.eq_zero_of_le_zeroₓ (H s)

end Ringₓ

section CommRingₓ

variable[CommRingₓ R]

/-- Multivariate formal power series over a local ring form a local ring. -/
instance is_local_ring [LocalRing R] : LocalRing (MvPowerSeries σ R) :=
  { is_local :=
      by 
        intro φ 
        rcases LocalRing.is_local (constant_coeff σ R φ) with (⟨u, h⟩ | ⟨u, h⟩) <;> [left, right] <;>
          ·
            refine' is_unit_of_mul_eq_one _ _ (mul_inv_of_unit _ u _)
            simpa using h.symm }

end CommRingₓ

section LocalRing

variable{S : Type _}[CommRingₓ R][CommRingₓ S](f : R →+* S)[IsLocalRingHom f]

/-- The map `A[[X]] → B[[X]]` induced by a local ring hom `A → B` is local -/
instance map.is_local_ring_hom : IsLocalRingHom (map σ f) :=
  ⟨by 
      rintro φ ⟨ψ, h⟩
      replace h := congr_argₓ (constant_coeff σ S) h 
      rw [constant_coeff_map] at h 
      have  : IsUnit (constant_coeff σ S («expr↑ » ψ)) := @is_unit_constant_coeff σ S _ («expr↑ » ψ) ψ.is_unit 
      rw [h] at this 
      rcases is_unit_of_map_unit f _ this with ⟨c, hc⟩
      exact is_unit_of_mul_eq_one φ (inv_of_unit φ c) (mul_inv_of_unit φ c hc.symm)⟩

variable[LocalRing R][LocalRing S]

instance  : LocalRing (MvPowerSeries σ R) :=
  { is_local := LocalRing.is_local }

end LocalRing

section Field

variable{k : Type _}[Field k]

/-- The inverse `1/f` of a multivariable power series `f` over a field -/
protected def inv (φ : MvPowerSeries σ k) : MvPowerSeries σ k :=
  inv.aux (constant_coeff σ k φ⁻¹) φ

instance  : HasInv (MvPowerSeries σ k) :=
  ⟨MvPowerSeries.inv⟩

theorem coeff_inv [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ k) :
  coeff k n (φ⁻¹) =
    if n = 0 then constant_coeff σ k φ⁻¹ else
      (-constant_coeff σ k φ⁻¹)*∑x in n.antidiagonal, if x.2 < n then coeff k x.1 φ*coeff k x.2 (φ⁻¹) else 0 :=
  coeff_inv_aux n _ φ

@[simp]
theorem constant_coeff_inv (φ : MvPowerSeries σ k) : constant_coeff σ k (φ⁻¹) = constant_coeff σ k φ⁻¹ :=
  by 
    rw [←coeff_zero_eq_constant_coeff_apply, coeff_inv, if_pos rfl]

theorem inv_eq_zero {φ : MvPowerSeries σ k} : φ⁻¹ = 0 ↔ constant_coeff σ k φ = 0 :=
  ⟨fun h =>
      by 
        simpa using congr_argₓ (constant_coeff σ k) h,
    fun h =>
      ext$
        fun n =>
          by 
            rw [coeff_inv]
            splitIfs <;> simp only [h, MvPowerSeries.coeff_zero, zero_mul, inv_zero, neg_zero]⟩

@[simp]
theorem inv_of_unit_eq (φ : MvPowerSeries σ k) (h : constant_coeff σ k φ ≠ 0) : inv_of_unit φ (Units.mk0 _ h) = φ⁻¹ :=
  rfl

@[simp]
theorem inv_of_unit_eq' (φ : MvPowerSeries σ k) (u : Units k) (h : constant_coeff σ k φ = u) : inv_of_unit φ u = φ⁻¹ :=
  by 
    rw [←inv_of_unit_eq φ (h.symm ▸ u.ne_zero)]
    congr 1
    rw [Units.ext_iff]
    exact h.symm

@[simp]
protected theorem mul_inv (φ : MvPowerSeries σ k) (h : constant_coeff σ k φ ≠ 0) : (φ*φ⁻¹) = 1 :=
  by 
    rw [←inv_of_unit_eq φ h, mul_inv_of_unit φ (Units.mk0 _ h) rfl]

@[simp]
protected theorem inv_mul (φ : MvPowerSeries σ k) (h : constant_coeff σ k φ ≠ 0) : (φ⁻¹*φ) = 1 :=
  by 
    rw [mul_commₓ, φ.mul_inv h]

protected theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : MvPowerSeries σ k} (h : constant_coeff σ k φ₃ ≠ 0) :
  (φ₁ = φ₂*φ₃⁻¹) ↔ (φ₁*φ₃) = φ₂ :=
  ⟨fun k =>
      by 
        simp [k, mul_assocₓ, MvPowerSeries.inv_mul _ h],
    fun k =>
      by 
        simp [←k, mul_assocₓ, MvPowerSeries.mul_inv _ h]⟩

protected theorem eq_inv_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constant_coeff σ k ψ ≠ 0) :
  φ = ψ⁻¹ ↔ (φ*ψ) = 1 :=
  by 
    rw [←MvPowerSeries.eq_mul_inv_iff_mul_eq h, one_mulₓ]

protected theorem inv_eq_iff_mul_eq_one {φ ψ : MvPowerSeries σ k} (h : constant_coeff σ k ψ ≠ 0) :
  ψ⁻¹ = φ ↔ (φ*ψ) = 1 :=
  by 
    rw [eq_comm, MvPowerSeries.eq_inv_iff_mul_eq_one h]

end Field

end MvPowerSeries

namespace MvPolynomial

open Finsupp

variable{σ : Type _}{R : Type _}[CommSemiringₓ R]

/-- The natural inclusion from multivariate polynomials into multivariate formal power series.-/
instance coe_to_mv_power_series : Coe (MvPolynomial σ R) (MvPowerSeries σ R) :=
  ⟨fun φ n => coeff n φ⟩

@[simp, normCast]
theorem coeff_coe (φ : MvPolynomial σ R) (n : σ →₀ ℕ) : MvPowerSeries.coeff R n («expr↑ » φ) = coeff n φ :=
  rfl

@[simp, normCast]
theorem coe_monomial (n : σ →₀ ℕ) (a : R) : (monomial n a : MvPowerSeries σ R) = MvPowerSeries.monomial R n a :=
  MvPowerSeries.ext$
    fun m =>
      by 
        rw [coeff_coe, coeff_monomial, MvPowerSeries.coeff_monomial]
        splitIfs with h₁ h₂ <;>
          first |
              rfl|
              subst m <;>
            contradiction

@[simp, normCast]
theorem coe_zero : ((0 : MvPolynomial σ R) : MvPowerSeries σ R) = 0 :=
  rfl

@[simp, normCast]
theorem coe_one : ((1 : MvPolynomial σ R) : MvPowerSeries σ R) = 1 :=
  coe_monomial _ _

@[simp, normCast]
theorem coe_add (φ ψ : MvPolynomial σ R) : ((φ+ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ+ψ :=
  rfl

@[simp, normCast]
theorem coe_mul (φ ψ : MvPolynomial σ R) : ((φ*ψ : MvPolynomial σ R) : MvPowerSeries σ R) = φ*ψ :=
  MvPowerSeries.ext$
    fun n =>
      by 
        simp only [coeff_coe, MvPowerSeries.coeff_mul, coeff_mul]

@[simp, normCast]
theorem coe_C (a : R) : ((C a : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.c σ R a :=
  coe_monomial _ _

@[simp, normCast]
theorem coe_X (s : σ) : ((X s : MvPolynomial σ R) : MvPowerSeries σ R) = MvPowerSeries.x s :=
  coe_monomial _ _

/--
The coercion from multivariable polynomials to multivariable power series
as a ring homomorphism.
-/
def coe_to_mv_power_series.ring_hom : MvPolynomial σ R →+* MvPowerSeries σ R :=
  { toFun := (coeₓ : MvPolynomial σ R → MvPowerSeries σ R), map_zero' := coe_zero, map_one' := coe_one,
    map_add' := coe_add, map_mul' := coe_mul }

end MvPolynomial

/-- Formal power series over the coefficient ring `R`.-/
def PowerSeries (R : Type _) :=
  MvPowerSeries Unit R

namespace PowerSeries

open finsupp(single)

variable{R : Type _}

section 

attribute [local reducible] PowerSeries

instance  [Inhabited R] : Inhabited (PowerSeries R) :=
  by 
    infer_instance

instance  [AddMonoidₓ R] : AddMonoidₓ (PowerSeries R) :=
  by 
    infer_instance

instance  [AddGroupₓ R] : AddGroupₓ (PowerSeries R) :=
  by 
    infer_instance

instance  [AddCommMonoidₓ R] : AddCommMonoidₓ (PowerSeries R) :=
  by 
    infer_instance

instance  [AddCommGroupₓ R] : AddCommGroupₓ (PowerSeries R) :=
  by 
    infer_instance

instance  [Semiringₓ R] : Semiringₓ (PowerSeries R) :=
  by 
    infer_instance

instance  [CommSemiringₓ R] : CommSemiringₓ (PowerSeries R) :=
  by 
    infer_instance

instance  [Ringₓ R] : Ringₓ (PowerSeries R) :=
  by 
    infer_instance

instance  [CommRingₓ R] : CommRingₓ (PowerSeries R) :=
  by 
    infer_instance

instance  [Nontrivial R] : Nontrivial (PowerSeries R) :=
  by 
    infer_instance

instance  {A} [Semiringₓ R] [AddCommMonoidₓ A] [Module R A] : Module R (PowerSeries A) :=
  by 
    infer_instance

instance  {A S} [Semiringₓ R] [Semiringₓ S] [AddCommMonoidₓ A] [Module R A] [Module S A] [HasScalar R S]
  [IsScalarTower R S A] : IsScalarTower R S (PowerSeries A) :=
  Pi.is_scalar_tower

instance  {A} [Semiringₓ A] [CommSemiringₓ R] [Algebra R A] : Algebra R (PowerSeries A) :=
  by 
    infer_instance

end 

section Semiringₓ

variable(R)[Semiringₓ R]

/-- The `n`th coefficient of a formal power series.-/
def coeff (n : ℕ) : PowerSeries R →ₗ[R] R :=
  MvPowerSeries.coeff R (single () n)

/-- The `n`th monomial with coefficient `a` as formal power series.-/
def monomial (n : ℕ) : R →ₗ[R] PowerSeries R :=
  MvPowerSeries.monomial R (single () n)

variable{R}

theorem coeff_def {s : Unit →₀ ℕ} {n : ℕ} (h : s () = n) : coeff R n = MvPowerSeries.coeff R s :=
  by 
    erw [coeff, ←h, ←Finsupp.unique_single s]

/-- Two formal power series are equal if all their coefficients are equal.-/
@[ext]
theorem ext {φ ψ : PowerSeries R} (h : ∀ n, coeff R n φ = coeff R n ψ) : φ = ψ :=
  MvPowerSeries.ext$
    fun n =>
      by 
        rw [←coeff_def]
        ·
          apply h 
        rfl

/-- Two formal power series are equal if all their coefficients are equal.-/
theorem ext_iff {φ ψ : PowerSeries R} : φ = ψ ↔ ∀ n, coeff R n φ = coeff R n ψ :=
  ⟨fun h n => congr_argₓ (coeff R n) h, ext⟩

/-- Constructor for formal power series.-/
def mk {R} (f : ℕ → R) : PowerSeries R :=
  fun s => f (s ())

@[simp]
theorem coeff_mk (n : ℕ) (f : ℕ → R) : coeff R n (mk f) = f n :=
  congr_argₓ f Finsupp.single_eq_same

theorem coeff_monomial (m n : ℕ) (a : R) : coeff R m (monomial R n a) = if m = n then a else 0 :=
  calc coeff R m (monomial R n a) = _ := MvPowerSeries.coeff_monomial _ _ _ 
    _ = if m = n then a else 0 :=
    by 
      simp only [Finsupp.unique_single_eq_iff]
      splitIfs <;> rfl
    

theorem monomial_eq_mk (n : ℕ) (a : R) : monomial R n a = mk fun m => if m = n then a else 0 :=
  ext$
    fun m =>
      by 
        rw [coeff_monomial, coeff_mk]

@[simp]
theorem coeff_monomial_same (n : ℕ) (a : R) : coeff R n (monomial R n a) = a :=
  MvPowerSeries.coeff_monomial_same _ _

@[simp]
theorem coeff_comp_monomial (n : ℕ) : (coeff R n).comp (monomial R n) = LinearMap.id :=
  LinearMap.ext$ coeff_monomial_same n

variable(R)

/--The constant coefficient of a formal power series. -/
def constant_coeff : PowerSeries R →+* R :=
  MvPowerSeries.constantCoeff Unit R

/-- The constant formal power series.-/
def C : R →+* PowerSeries R :=
  MvPowerSeries.c Unit R

variable{R}

/-- The variable of the formal power series ring.-/
def X : PowerSeries R :=
  MvPowerSeries.x ()

@[simp]
theorem coeff_zero_eq_constant_coeff : «expr⇑ » (coeff R 0) = constant_coeff R :=
  by 
    rw [coeff, Finsupp.single_zero]
    rfl

theorem coeff_zero_eq_constant_coeff_apply (φ : PowerSeries R) : coeff R 0 φ = constant_coeff R φ :=
  by 
    rw [coeff_zero_eq_constant_coeff] <;> rfl

@[simp]
theorem monomial_zero_eq_C : «expr⇑ » (monomial R 0) = C R :=
  by 
    rw [monomial, Finsupp.single_zero, MvPowerSeries.monomial_zero_eq_C, C]

theorem monomial_zero_eq_C_apply (a : R) : monomial R 0 a = C R a :=
  by 
    simp 

theorem coeff_C (n : ℕ) (a : R) : coeff R n (C R a : PowerSeries R) = if n = 0 then a else 0 :=
  by 
    rw [←monomial_zero_eq_C_apply, coeff_monomial]

@[simp]
theorem coeff_zero_C (a : R) : coeff R 0 (C R a) = a :=
  by 
    rw [←monomial_zero_eq_C_apply, coeff_monomial_same 0 a]

theorem X_eq : (X : PowerSeries R) = monomial R 1 1 :=
  rfl

theorem coeff_X (n : ℕ) : coeff R n (X : PowerSeries R) = if n = 1 then 1 else 0 :=
  by 
    rw [X_eq, coeff_monomial]

@[simp]
theorem coeff_zero_X : coeff R 0 (X : PowerSeries R) = 0 :=
  by 
    rw [coeff, Finsupp.single_zero, X, MvPowerSeries.coeff_zero_X]

@[simp]
theorem coeff_one_X : coeff R 1 (X : PowerSeries R) = 1 :=
  by 
    rw [coeff_X, if_pos rfl]

theorem X_pow_eq (n : ℕ) : ((X : PowerSeries R)^n) = monomial R n 1 :=
  MvPowerSeries.X_pow_eq _ n

theorem coeff_X_pow (m n : ℕ) : coeff R m ((X : PowerSeries R)^n) = if m = n then 1 else 0 :=
  by 
    rw [X_pow_eq, coeff_monomial]

@[simp]
theorem coeff_X_pow_self (n : ℕ) : coeff R n ((X : PowerSeries R)^n) = 1 :=
  by 
    rw [coeff_X_pow, if_pos rfl]

@[simp]
theorem coeff_one (n : ℕ) : coeff R n (1 : PowerSeries R) = if n = 0 then 1 else 0 :=
  coeff_C n 1

theorem coeff_zero_one : coeff R 0 (1 : PowerSeries R) = 1 :=
  coeff_zero_C 1

theorem coeff_mul (n : ℕ) (φ ψ : PowerSeries R) :
  coeff R n (φ*ψ) = ∑p in Finset.Nat.antidiagonal n, coeff R p.1 φ*coeff R p.2 ψ :=
  by 
    symm 
    apply Finset.sum_bij fun p : ℕ × ℕ h => (single () p.1, single () p.2)
    ·
      rintro ⟨i, j⟩ hij 
      rw [Finset.Nat.mem_antidiagonal] at hij 
      rw [Finsupp.mem_antidiagonal, ←Finsupp.single_add, hij]
    ·
      rintro ⟨i, j⟩ hij 
      rfl
    ·
      rintro ⟨i, j⟩ ⟨k, l⟩ hij hkl 
      simpa only [Prod.mk.inj_iffₓ, Finsupp.unique_single_eq_iff] using id
    ·
      rintro ⟨f, g⟩ hfg 
      refine' ⟨(f (), g ()), _, _⟩
      ·
        rw [Finsupp.mem_antidiagonal] at hfg 
        rw [Finset.Nat.mem_antidiagonal, ←Finsupp.add_apply, hfg, Finsupp.single_eq_same]
      ·
        rw [Prod.mk.inj_iffₓ]
        dsimp 
        exact ⟨Finsupp.unique_single f, Finsupp.unique_single g⟩

@[simp]
theorem coeff_mul_C (n : ℕ) (φ : PowerSeries R) (a : R) : coeff R n (φ*C R a) = coeff R n φ*a :=
  MvPowerSeries.coeff_mul_C _ φ a

@[simp]
theorem coeff_C_mul (n : ℕ) (φ : PowerSeries R) (a : R) : coeff R n (C R a*φ) = a*coeff R n φ :=
  MvPowerSeries.coeff_C_mul _ φ a

@[simp]
theorem coeff_smul (n : ℕ) (φ : PowerSeries R) (a : R) : coeff R n (a • φ) = a*coeff R n φ :=
  rfl

@[simp]
theorem coeff_succ_mul_X (n : ℕ) (φ : PowerSeries R) : coeff R (n+1) (φ*X) = coeff R n φ :=
  by 
    simp only [coeff, Finsupp.single_add]
    convert φ.coeff_add_mul_monomial (single () n) (single () 1) _ 
    rw [mul_oneₓ]

@[simp]
theorem coeff_succ_X_mul (n : ℕ) (φ : PowerSeries R) : coeff R (n+1) (X*φ) = coeff R n φ :=
  by 
    simp only [coeff, Finsupp.single_add, add_commₓ n 1]
    convert φ.coeff_add_monomial_mul (single () 1) (single () n) _ 
    rw [one_mulₓ]

@[simp]
theorem constant_coeff_C (a : R) : constant_coeff R (C R a) = a :=
  rfl

@[simp]
theorem constant_coeff_comp_C : (constant_coeff R).comp (C R) = RingHom.id R :=
  rfl

@[simp]
theorem constant_coeff_zero : constant_coeff R 0 = 0 :=
  rfl

@[simp]
theorem constant_coeff_one : constant_coeff R 1 = 1 :=
  rfl

@[simp]
theorem constant_coeff_X : constant_coeff R X = 0 :=
  MvPowerSeries.coeff_zero_X _

theorem coeff_zero_mul_X (φ : PowerSeries R) : coeff R 0 (φ*X) = 0 :=
  by 
    simp 

theorem coeff_zero_X_mul (φ : PowerSeries R) : coeff R 0 (X*φ) = 0 :=
  by 
    simp 

/-- If a formal power series is invertible, then so is its constant coefficient.-/
theorem is_unit_constant_coeff (φ : PowerSeries R) (h : IsUnit φ) : IsUnit (constant_coeff R φ) :=
  MvPowerSeries.is_unit_constant_coeff φ h

/-- Split off the constant coefficient. -/
theorem eq_shift_mul_X_add_const (φ : PowerSeries R) : φ = ((mk fun p => coeff R (p+1) φ)*X)+C R (constant_coeff R φ) :=
  by 
    ext (_ | n)
    ·
      simp only [RingHom.map_add, constant_coeff_C, constant_coeff_X, coeff_zero_eq_constant_coeff, zero_addₓ, mul_zero,
        RingHom.map_mul]
    ·
      simp only [coeff_succ_mul_X, coeff_mk, LinearMap.map_add, coeff_C, n.succ_ne_zero, sub_zero, if_false, add_zeroₓ]

/-- Split off the constant coefficient. -/
theorem eq_X_mul_shift_add_const (φ : PowerSeries R) : φ = (X*mk fun p => coeff R (p+1) φ)+C R (constant_coeff R φ) :=
  by 
    ext (_ | n)
    ·
      simp only [RingHom.map_add, constant_coeff_C, constant_coeff_X, coeff_zero_eq_constant_coeff, zero_addₓ, zero_mul,
        RingHom.map_mul]
    ·
      simp only [coeff_succ_X_mul, coeff_mk, LinearMap.map_add, coeff_C, n.succ_ne_zero, sub_zero, if_false, add_zeroₓ]

section Map

variable{S : Type _}{T : Type _}[Semiringₓ S][Semiringₓ T]

variable(f : R →+* S)(g : S →+* T)

/-- The map between formal power series induced by a map on the coefficients.-/
def map : PowerSeries R →+* PowerSeries S :=
  MvPowerSeries.map _ f

@[simp]
theorem map_id : (map (RingHom.id R) : PowerSeries R → PowerSeries R) = id :=
  rfl

theorem map_comp : map (g.comp f) = (map g).comp (map f) :=
  rfl

@[simp]
theorem coeff_map (n : ℕ) (φ : PowerSeries R) : coeff S n (map f φ) = f (coeff R n φ) :=
  rfl

end Map

end Semiringₓ

section CommSemiringₓ

variable[CommSemiringₓ R]

theorem X_pow_dvd_iff {n : ℕ} {φ : PowerSeries R} : ((X : PowerSeries R)^n) ∣ φ ↔ ∀ m, m < n → coeff R m φ = 0 :=
  by 
    convert @MvPowerSeries.X_pow_dvd_iff Unit R _ () n φ 
    apply propext 
    classical 
    split  <;> intro h m hm
    ·
      rw [Finsupp.unique_single m]
      convert h _ hm
    ·
      apply h 
      simpa only [Finsupp.single_eq_same] using hm

theorem X_dvd_iff {φ : PowerSeries R} : (X : PowerSeries R) ∣ φ ↔ constant_coeff R φ = 0 :=
  by 
    rw [←pow_oneₓ (X : PowerSeries R), X_pow_dvd_iff, ←coeff_zero_eq_constant_coeff_apply]
    split  <;> intro h
    ·
      exact h 0 zero_lt_one
    ·
      intro m hm 
      rwa [Nat.eq_zero_of_le_zeroₓ (Nat.le_of_succ_le_succₓ hm)]

open Finset Nat

/-- The ring homomorphism taking a power series `f(X)` to `f(aX)`. -/
noncomputable def rescale (a : R) : PowerSeries R →+* PowerSeries R :=
  { toFun := fun f => PowerSeries.mk$ fun n => (a^n)*PowerSeries.coeff R n f,
    map_zero' :=
      by 
        ext 
        simp only [LinearMap.map_zero, PowerSeries.coeff_mk, mul_zero],
    map_one' :=
      by 
        ext1 
        simp only [mul_boole, PowerSeries.coeff_mk, PowerSeries.coeff_one]
        splitIfs
        ·
          rw [h, pow_zeroₓ]
        rfl,
    map_add' :=
      by 
        intros 
        ext 
        exact mul_addₓ _ _ _,
    map_mul' :=
      fun f g =>
        by 
          ext 
          rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mul, Finset.mul_sum]
          apply sum_congr rfl 
          simp only [coeff_mk, Prod.forall, nat.mem_antidiagonal]
          intro b c H 
          rw [←H, pow_addₓ, mul_mul_mul_commₓ] }

@[simp]
theorem coeff_rescale (f : PowerSeries R) (a : R) (n : ℕ) : coeff R n (rescale a f) = (a^n)*coeff R n f :=
  coeff_mk n _

@[simp]
theorem rescale_zero : rescale 0 = (C R).comp (constant_coeff R) :=
  by 
    ext 
    simp only [Function.comp_app, RingHom.coe_comp, rescale, RingHom.coe_mk, PowerSeries.coeff_mk _ _, coeff_C]
    splitIfs
    ·
      simp only [h, one_mulₓ, coeff_zero_eq_constant_coeff, pow_zeroₓ]
    ·
      rw [zero_pow' n h, zero_mul]

theorem rescale_zero_apply : rescale 0 X = C R (constant_coeff R X) :=
  by 
    simp 

@[simp]
theorem rescale_one : rescale 1 = RingHom.id (PowerSeries R) :=
  by 
    ext 
    simp only [RingHom.id_apply, rescale, one_pow, coeff_mk, one_mulₓ, RingHom.coe_mk]

section Trunc

/-- The `n`th truncation of a formal power series to a polynomial -/
def Trunc (n : ℕ) (φ : PowerSeries R) : Polynomial R :=
  ∑m in Ico 0 (n+1), Polynomial.monomial m (coeff R m φ)

theorem coeff_trunc m n (φ : PowerSeries R) : (Trunc n φ).coeff m = if m ≤ n then coeff R m φ else 0 :=
  by 
    simp [Trunc, Polynomial.coeff_sum, Polynomial.coeff_monomial, Nat.lt_succ_iff]

@[simp]
theorem trunc_zero n : Trunc n (0 : PowerSeries R) = 0 :=
  Polynomial.ext$
    fun m =>
      by 
        rw [coeff_trunc, LinearMap.map_zero, Polynomial.coeff_zero]
        splitIfs <;> rfl

@[simp]
theorem trunc_one n : Trunc n (1 : PowerSeries R) = 1 :=
  Polynomial.ext$
    fun m =>
      by 
        rw [coeff_trunc, coeff_one]
        splitIfs with H H' H' <;> rw [Polynomial.coeff_one]
        ·
          subst m 
          rw [if_pos rfl]
        ·
          symm 
          exact if_neg (Ne.elim (Ne.symm H'))
        ·
          symm 
          refine' if_neg _ 
          intro H' 
          apply H 
          subst m 
          exact Nat.zero_leₓ _

@[simp]
theorem trunc_C n (a : R) : Trunc n (C R a) = Polynomial.c a :=
  Polynomial.ext$
    fun m =>
      by 
        rw [coeff_trunc, coeff_C, Polynomial.coeff_C]
        splitIfs with H <;>
          first |
            rfl|
            try 
              simp_all 

@[simp]
theorem trunc_add n (φ ψ : PowerSeries R) : Trunc n (φ+ψ) = Trunc n φ+Trunc n ψ :=
  Polynomial.ext$
    fun m =>
      by 
        simp only [coeff_trunc, AddMonoidHom.map_add, Polynomial.coeff_add]
        splitIfs with H
        ·
          rfl
        ·
          rw [zero_addₓ]

end Trunc

end CommSemiringₓ

section Ringₓ

variable[Ringₓ R]

/-- Auxiliary function used for computing inverse of a power series -/
protected def inv.aux : R → PowerSeries R → PowerSeries R :=
  MvPowerSeries.Inv.aux

theorem coeff_inv_aux (n : ℕ) (a : R) (φ : PowerSeries R) :
  coeff R n (inv.aux a φ) =
    if n = 0 then a else
      (-a)*∑x in Finset.Nat.antidiagonal n, if x.2 < n then coeff R x.1 φ*coeff R x.2 (inv.aux a φ) else 0 :=
  by 
    rw [coeff, inv.aux, MvPowerSeries.coeff_inv_aux]
    simp only [Finsupp.single_eq_zero]
    splitIfs
    ·
      rfl 
    congr 1
    symm 
    apply Finset.sum_bij fun p : ℕ × ℕ h => (single () p.1, single () p.2)
    ·
      rintro ⟨i, j⟩ hij 
      rw [Finset.Nat.mem_antidiagonal] at hij 
      rw [Finsupp.mem_antidiagonal, ←Finsupp.single_add, hij]
    ·
      rintro ⟨i, j⟩ hij 
      byCases' H : j < n
      ·
        rw [if_pos H, if_pos]
        ·
          rfl 
        split 
        ·
          rintro ⟨⟩
          simpa [Finsupp.single_eq_same] using le_of_ltₓ H
        ·
          intro hh 
          rw [lt_iff_not_geₓ] at H 
          apply H 
          simpa [Finsupp.single_eq_same] using hh ()
      ·
        rw [if_neg H, if_neg]
        rintro ⟨h₁, h₂⟩
        apply h₂ 
        rintro ⟨⟩
        simpa [Finsupp.single_eq_same] using not_ltₓ.1 H
    ·
      rintro ⟨i, j⟩ ⟨k, l⟩ hij hkl 
      simpa only [Prod.mk.inj_iffₓ, Finsupp.unique_single_eq_iff] using id
    ·
      rintro ⟨f, g⟩ hfg 
      refine' ⟨(f (), g ()), _, _⟩
      ·
        rw [Finsupp.mem_antidiagonal] at hfg 
        rw [Finset.Nat.mem_antidiagonal, ←Finsupp.add_apply, hfg, Finsupp.single_eq_same]
      ·
        rw [Prod.mk.inj_iffₓ]
        dsimp 
        exact ⟨Finsupp.unique_single f, Finsupp.unique_single g⟩

/-- A formal power series is invertible if the constant coefficient is invertible.-/
def inv_of_unit (φ : PowerSeries R) (u : Units R) : PowerSeries R :=
  MvPowerSeries.invOfUnit φ u

theorem coeff_inv_of_unit (n : ℕ) (φ : PowerSeries R) (u : Units R) :
  coeff R n (inv_of_unit φ u) =
    if n = 0 then «expr↑ » (u⁻¹) else
      (-«expr↑ »
            (u⁻¹))*∑x in Finset.Nat.antidiagonal n,
          if x.2 < n then coeff R x.1 φ*coeff R x.2 (inv_of_unit φ u) else 0 :=
  coeff_inv_aux n («expr↑ » (u⁻¹)) φ

@[simp]
theorem constant_coeff_inv_of_unit (φ : PowerSeries R) (u : Units R) :
  constant_coeff R (inv_of_unit φ u) = «expr↑ » (u⁻¹) :=
  by 
    rw [←coeff_zero_eq_constant_coeff_apply, coeff_inv_of_unit, if_pos rfl]

theorem mul_inv_of_unit (φ : PowerSeries R) (u : Units R) (h : constant_coeff R φ = u) : (φ*inv_of_unit φ u) = 1 :=
  MvPowerSeries.mul_inv_of_unit φ u$ h

/-- Two ways of removing the constant coefficient of a power series are the same. -/
theorem sub_const_eq_shift_mul_X (φ : PowerSeries R) :
  φ - C R (constant_coeff R φ) = (PowerSeries.mk fun p => coeff R (p+1) φ)*X :=
  sub_eq_iff_eq_add.mpr (eq_shift_mul_X_add_const φ)

theorem sub_const_eq_X_mul_shift (φ : PowerSeries R) :
  φ - C R (constant_coeff R φ) = X*PowerSeries.mk fun p => coeff R (p+1) φ :=
  sub_eq_iff_eq_add.mpr (eq_X_mul_shift_add_const φ)

end Ringₓ

section CommRingₓ

variable{A : Type _}[CommRingₓ A]

@[simp]
theorem rescale_neg_one_X : rescale (-1 : A) X = -X :=
  by 
    ext 
    simp only [LinearMap.map_neg, coeff_rescale, coeff_X]
    splitIfs with h <;> simp [h]

/-- The ring homomorphism taking a power series `f(X)` to `f(-X)`. -/
noncomputable def eval_neg_hom : PowerSeries A →+* PowerSeries A :=
  rescale (-1 : A)

@[simp]
theorem eval_neg_hom_X : eval_neg_hom (X : PowerSeries A) = -X :=
  rescale_neg_one_X

end CommRingₓ

section Domain

variable[Ringₓ R][IsDomain R]

theorem eq_zero_or_eq_zero_of_mul_eq_zero (φ ψ : PowerSeries R) (h : (φ*ψ) = 0) : φ = 0 ∨ ψ = 0 :=
  by 
    rw [or_iff_not_imp_left]
    intro H 
    have ex : ∃ m, coeff R m φ ≠ 0
    ·
      contrapose! H 
      exact ext H 
    let m := Nat.findₓ ex 
    have hm₁ : coeff R m φ ≠ 0 := Nat.find_specₓ ex 
    have hm₂ : ∀ k _ : k < m, ¬coeff R k φ ≠ 0 := fun k => Nat.find_minₓ ex 
    ext n 
    rw [(coeff R n).map_zero]
    apply Nat.strong_induction_onₓ n 
    clear n 
    intro n ih 
    replace h := congr_argₓ (coeff R (m+n)) h 
    rw [LinearMap.map_zero, coeff_mul, Finset.sum_eq_single (m, n)] at h
    ·
      replace h := eq_zero_or_eq_zero_of_mul_eq_zero h 
      rw [or_iff_not_imp_left] at h 
      exact h hm₁
    ·
      rintro ⟨i, j⟩ hij hne 
      byCases' hj : j < n
      ·
        rw [ih j hj, mul_zero]
      byCases' hi : i < m
      ·
        specialize hm₂ _ hi 
        pushNeg  at hm₂ 
        rw [hm₂, zero_mul]
      rw [Finset.Nat.mem_antidiagonal] at hij 
      pushNeg  at hi hj 
      suffices  : m < i
      ·
        have  : (m+n) < i+j := add_lt_add_of_lt_of_le this hj 
        exFalso 
        exact ne_of_ltₓ this hij.symm 
      contrapose! hne 
      have  : i = m := le_antisymmₓ hne hi 
      subst i 
      clear hi hne 
      simpa [Ne.def, Prod.mk.inj_iffₓ] using (add_right_injₓ m).mp hij
    ·
      contrapose! 
      intro h 
      rw [Finset.Nat.mem_antidiagonal]

instance  : IsDomain (PowerSeries R) :=
  { PowerSeries.nontrivial with eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero }

end Domain

section IsDomain

variable[CommRingₓ R][IsDomain R]

/-- The ideal spanned by the variable in the power series ring
 over an integral domain is a prime ideal.-/
theorem span_X_is_prime : (Ideal.span ({X} : Set (PowerSeries R))).IsPrime :=
  by 
    suffices  : Ideal.span ({X} : Set (PowerSeries R)) = (constant_coeff R).ker
    ·
      rw [this]
      exact RingHom.ker_is_prime _ 
    apply Ideal.ext 
    intro φ 
    rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

/-- The variable of the power series ring over an integral domain is prime.-/
theorem X_prime : Prime (X : PowerSeries R) :=
  by 
    rw [←Ideal.span_singleton_prime]
    ·
      exact span_X_is_prime
    ·
      intro h 
      simpa using congr_argₓ (coeff R 1) h

theorem rescale_injective {a : R} (ha : a ≠ 0) : Function.Injective (rescale a) :=
  by 
    intro p q h 
    rw [PowerSeries.ext_iff] at *
    intro n 
    specialize h n 
    rw [coeff_rescale, coeff_rescale, mul_eq_mul_left_iff] at h 
    apply h.resolve_right 
    intro h' 
    exact ha (pow_eq_zero h')

end IsDomain

section LocalRing

variable{S : Type _}[CommRingₓ R][CommRingₓ S](f : R →+* S)[IsLocalRingHom f]

instance map.is_local_ring_hom : IsLocalRingHom (map f) :=
  MvPowerSeries.map.is_local_ring_hom f

variable[LocalRing R][LocalRing S]

instance  : LocalRing (PowerSeries R) :=
  MvPowerSeries.local_ring

end LocalRing

section Algebra

variable{A : Type _}[CommSemiringₓ R][Semiringₓ A][Algebra R A]

theorem C_eq_algebra_map {r : R} : C R r = (algebraMap R (PowerSeries R)) r :=
  rfl

theorem algebra_map_apply {r : R} : algebraMap R (PowerSeries A) r = C A (algebraMap R A r) :=
  MvPowerSeries.algebra_map_apply

instance  [Nontrivial R] : Nontrivial (Subalgebra R (PowerSeries R)) :=
  MvPowerSeries.Subalgebra.nontrivial

end Algebra

section Field

variable{k : Type _}[Field k]

/-- The inverse 1/f of a power series f defined over a field -/
protected def inv : PowerSeries k → PowerSeries k :=
  MvPowerSeries.inv

instance  : HasInv (PowerSeries k) :=
  ⟨PowerSeries.inv⟩

theorem inv_eq_inv_aux (φ : PowerSeries k) : φ⁻¹ = inv.aux (constant_coeff k φ⁻¹) φ :=
  rfl

theorem coeff_inv n (φ : PowerSeries k) :
  coeff k n (φ⁻¹) =
    if n = 0 then constant_coeff k φ⁻¹ else
      (-constant_coeff k φ⁻¹)*∑x in Finset.Nat.antidiagonal n, if x.2 < n then coeff k x.1 φ*coeff k x.2 (φ⁻¹) else 0 :=
  by 
    rw [inv_eq_inv_aux, coeff_inv_aux n (constant_coeff k φ⁻¹) φ]

@[simp]
theorem constant_coeff_inv (φ : PowerSeries k) : constant_coeff k (φ⁻¹) = constant_coeff k φ⁻¹ :=
  MvPowerSeries.constant_coeff_inv φ

theorem inv_eq_zero {φ : PowerSeries k} : φ⁻¹ = 0 ↔ constant_coeff k φ = 0 :=
  MvPowerSeries.inv_eq_zero

@[simp]
theorem inv_of_unit_eq (φ : PowerSeries k) (h : constant_coeff k φ ≠ 0) : inv_of_unit φ (Units.mk0 _ h) = φ⁻¹ :=
  MvPowerSeries.inv_of_unit_eq _ _

@[simp]
theorem inv_of_unit_eq' (φ : PowerSeries k) (u : Units k) (h : constant_coeff k φ = u) : inv_of_unit φ u = φ⁻¹ :=
  MvPowerSeries.inv_of_unit_eq' φ _ h

@[simp]
protected theorem mul_inv (φ : PowerSeries k) (h : constant_coeff k φ ≠ 0) : (φ*φ⁻¹) = 1 :=
  MvPowerSeries.mul_inv φ h

@[simp]
protected theorem inv_mul (φ : PowerSeries k) (h : constant_coeff k φ ≠ 0) : (φ⁻¹*φ) = 1 :=
  MvPowerSeries.inv_mul φ h

theorem eq_mul_inv_iff_mul_eq {φ₁ φ₂ φ₃ : PowerSeries k} (h : constant_coeff k φ₃ ≠ 0) :
  (φ₁ = φ₂*φ₃⁻¹) ↔ (φ₁*φ₃) = φ₂ :=
  MvPowerSeries.eq_mul_inv_iff_mul_eq h

theorem eq_inv_iff_mul_eq_one {φ ψ : PowerSeries k} (h : constant_coeff k ψ ≠ 0) : φ = ψ⁻¹ ↔ (φ*ψ) = 1 :=
  MvPowerSeries.eq_inv_iff_mul_eq_one h

theorem inv_eq_iff_mul_eq_one {φ ψ : PowerSeries k} (h : constant_coeff k ψ ≠ 0) : ψ⁻¹ = φ ↔ (φ*ψ) = 1 :=
  MvPowerSeries.inv_eq_iff_mul_eq_one h

end Field

end PowerSeries

namespace PowerSeries

variable{R : Type _}

attribute [local instance] Classical.propDecidable

noncomputable theory

section OrderBasic

open multiplicity

variable[CommSemiringₓ R]

/-- The order of a formal power series `φ` is the greatest `n : enat`
such that `X^n` divides `φ`. The order is `⊤` if and only if `φ = 0`. -/
@[reducible]
def order (φ : PowerSeries R) : Enat :=
  multiplicity X φ

theorem order_finite_of_coeff_ne_zero (φ : PowerSeries R) (h : ∃ n, coeff R n φ ≠ 0) : (order φ).Dom :=
  by 
    cases' h with n h 
    refine' ⟨n, _⟩
    dsimp only 
    rw [X_pow_dvd_iff]
    pushNeg 
    exact ⟨n, lt_add_one n, h⟩

/-- If the order of a formal power series is finite,
then the coefficient indexed by the order is nonzero.-/
theorem coeff_order (φ : PowerSeries R) (h : (order φ).Dom) : coeff R (φ.order.get h) φ ≠ 0 :=
  by 
    have H := Nat.find_specₓ h 
    contrapose! H 
    rw [X_pow_dvd_iff]
    intro m hm 
    byCases' Hm : m < Nat.findₓ h
    ·
      have  := Nat.find_minₓ h Hm 
      pushNeg  at this 
      rw [X_pow_dvd_iff] at this 
      exact this m (lt_add_one m)
    have  : m = Nat.findₓ h
    ·
      linarith
    ·
      rwa [this]

/-- If the `n`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `n`.-/
theorem order_le (φ : PowerSeries R) (n : ℕ) (h : coeff R n φ ≠ 0) : order φ ≤ n :=
  by 
    have h : ¬(X^n+1) ∣ φ
    ·
      rw [X_pow_dvd_iff]
      pushNeg 
      exact ⟨n, lt_add_one n, h⟩
    have  : (order φ).Dom := ⟨n, h⟩
    rw [←Enat.coe_get this, Enat.coe_le_coe]
    refine' Nat.find_min'ₓ this h

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.-/
theorem coeff_of_lt_order (φ : PowerSeries R) (n : ℕ) (h : «expr↑ » n < order φ) : coeff R n φ = 0 :=
  by 
    contrapose! h 
    exact order_le _ _ h

/-- The order of the `0` power series is infinite.-/
@[simp]
theorem order_zero : order (0 : PowerSeries R) = ⊤ :=
  multiplicity.zero _

/-- The `0` power series is the unique power series with infinite order.-/
@[simp]
theorem order_eq_top {φ : PowerSeries R} : φ.order = ⊤ ↔ φ = 0 :=
  by 
    split 
    ·
      intro h 
      ext n 
      rw [(coeff R n).map_zero, coeff_of_lt_order]
      simp [h]
    ·
      rintro rfl 
      exact order_zero

-- error in RingTheory.PowerSeries.Basic: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.-/
theorem nat_le_order
(φ : power_series R)
(n : exprℕ())
(h : ∀ i «expr < » n, «expr = »(coeff R i φ, 0)) : «expr ≤ »(«expr↑ »(n), order φ) :=
begin
  by_contra [ident H],
  rw [expr not_le] ["at", ident H],
  have [] [":", expr (order φ).dom] [":=", expr enat.dom_of_le_coe H.le],
  rw ["[", "<-", expr enat.coe_get this, ",", expr enat.coe_lt_coe, "]"] ["at", ident H],
  exact [expr coeff_order _ this (h _ H)]
end

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.-/
theorem le_order (φ : PowerSeries R) (n : Enat) (h : ∀ i : ℕ, «expr↑ » i < n → coeff R i φ = 0) : n ≤ order φ :=
  by 
    induction n using Enat.cases_on
    ·
      show _ ≤ _ 
      rw [top_le_iff, order_eq_top]
      ext i 
      exact h _ (Enat.coe_lt_top i)
    ·
      apply nat_le_order 
      simpa only [Enat.coe_lt_coe] using h

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`.-/
theorem order_eq_nat {φ : PowerSeries R} {n : ℕ} : order φ = n ↔ coeff R n φ ≠ 0 ∧ ∀ i, i < n → coeff R i φ = 0 :=
  by 
    simp only [eq_coe_iff, X_pow_dvd_iff]
    pushNeg 
    split 
    ·
      rintro ⟨h₁, m, hm₁, hm₂⟩
      refine' ⟨_, h₁⟩
      suffices  : n = m
      ·
        rwa [this]
      suffices  : m ≥ n
      ·
        linarith 
      contrapose! hm₂ 
      exact h₁ _ hm₂
    ·
      rintro ⟨h₁, h₂⟩
      exact ⟨h₂, n, lt_add_one n, h₁⟩

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`.-/
theorem order_eq {φ : PowerSeries R} {n : Enat} :
  order φ = n ↔ (∀ i : ℕ, «expr↑ » i = n → coeff R i φ ≠ 0) ∧ ∀ i : ℕ, «expr↑ » i < n → coeff R i φ = 0 :=
  by 
    induction n using Enat.cases_on
    ·
      rw [order_eq_top]
      split 
      ·
        rintro rfl 
        split  <;> intros 
        ·
          exFalso 
          exact Enat.coe_ne_top ‹_› ‹_›
        ·
          exact (coeff _ _).map_zero
      ·
        rintro ⟨h₁, h₂⟩
        ext i 
        exact h₂ i (Enat.coe_lt_top i)
    ·
      simpa [Enat.coe_inj] using order_eq_nat

/-- The order of the sum of two formal power series
 is at least the minimum of their orders.-/
theorem le_order_add (φ ψ : PowerSeries R) : min (order φ) (order ψ) ≤ order (φ+ψ) :=
  multiplicity.min_le_multiplicity_add

private theorem order_add_of_order_eq.aux (φ ψ : PowerSeries R) (h : order φ ≠ order ψ) (H : order φ < order ψ) :
  order (φ+ψ) ≤ order φ⊓order ψ :=
  by 
    suffices  : order (φ+ψ) = order φ
    ·
      rw [le_inf_iff, this]
      exact ⟨le_reflₓ _, le_of_ltₓ H⟩
    ·
      rw [order_eq]
      split 
      ·
        intro i hi 
        rw [(coeff _ _).map_add, coeff_of_lt_order ψ i (hi.symm ▸ H), add_zeroₓ]
        exact (order_eq_nat.1 hi.symm).1
      ·
        intro i hi 
        rw [(coeff _ _).map_add, coeff_of_lt_order φ i hi, coeff_of_lt_order ψ i (lt_transₓ hi H), zero_addₓ]

/-- The order of the sum of two formal power series
 is the minimum of their orders if their orders differ.-/
theorem order_add_of_order_eq (φ ψ : PowerSeries R) (h : order φ ≠ order ψ) : order (φ+ψ) = order φ⊓order ψ :=
  by 
    refine' le_antisymmₓ _ (le_order_add _ _)
    byCases' H₁ : order φ < order ψ
    ·
      apply order_add_of_order_eq.aux _ _ h H₁ 
    byCases' H₂ : order ψ < order φ
    ·
      simpa only [add_commₓ, inf_comm] using order_add_of_order_eq.aux _ _ h.symm H₂ 
    exFalso 
    exact h (le_antisymmₓ (not_ltₓ.1 H₂) (not_ltₓ.1 H₁))

/-- The order of the product of two formal power series
 is at least the sum of their orders.-/
theorem order_mul_ge (φ ψ : PowerSeries R) : (order φ+order ψ) ≤ order (φ*ψ) :=
  by 
    apply le_order 
    intro n hn 
    rw [coeff_mul, Finset.sum_eq_zero]
    rintro ⟨i, j⟩ hij 
    byCases' hi : «expr↑ » i < order φ
    ·
      rw [coeff_of_lt_order φ i hi, zero_mul]
    byCases' hj : «expr↑ » j < order ψ
    ·
      rw [coeff_of_lt_order ψ j hj, mul_zero]
    rw [not_ltₓ] at hi hj 
    rw [Finset.Nat.mem_antidiagonal] at hij 
    exFalso 
    apply ne_of_ltₓ (lt_of_lt_of_leₓ hn$ add_le_add hi hj)
    rw [←Nat.cast_add, hij]

/-- The order of the monomial `a*X^n` is infinite if `a = 0` and `n` otherwise.-/
theorem order_monomial (n : ℕ) (a : R) [Decidable (a = 0)] : order (monomial R n a) = if a = 0 then ⊤ else n :=
  by 
    splitIfs with h
    ·
      rw [h, order_eq_top, LinearMap.map_zero]
    ·
      rw [order_eq]
      split  <;> intro i hi
      ·
        rw [Enat.coe_inj] at hi 
        rwa [hi, coeff_monomial_same]
      ·
        rw [Enat.coe_lt_coe] at hi 
        rw [coeff_monomial, if_neg]
        exact ne_of_ltₓ hi

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`.-/
theorem order_monomial_of_ne_zero (n : ℕ) (a : R) (h : a ≠ 0) : order (monomial R n a) = n :=
  by 
    rw [order_monomial, if_neg h]

/-- If `n` is strictly smaller than the order of `ψ`, then the `n`th coefficient of its product
with any other power series is `0`. -/
theorem coeff_mul_of_lt_order {φ ψ : PowerSeries R} {n : ℕ} (h : «expr↑ » n < ψ.order) : coeff R n (φ*ψ) = 0 :=
  by 
    suffices  : coeff R n (φ*ψ) = ∑p in Finset.Nat.antidiagonal n, 0
    rw [this, Finset.sum_const_zero]
    rw [coeff_mul]
    apply Finset.sum_congr rfl fun x hx => _ 
    refine' mul_eq_zero_of_right (coeff R x.fst φ) (ψ.coeff_of_lt_order x.snd (lt_of_le_of_ltₓ _ h))
    rw [Finset.Nat.mem_antidiagonal] at hx 
    normCast 
    linarith

theorem coeff_mul_one_sub_of_lt_order {R : Type _} [CommRingₓ R] {φ ψ : PowerSeries R} (n : ℕ)
  (h : «expr↑ » n < ψ.order) : coeff R n (φ*1 - ψ) = coeff R n φ :=
  by 
    simp [coeff_mul_of_lt_order h, mul_sub]

theorem coeff_mul_prod_one_sub_of_lt_order {R ι : Type _} [CommRingₓ R] (k : ℕ) (s : Finset ι) (φ : PowerSeries R)
  (f : ι → PowerSeries R) : (∀ i _ : i ∈ s, «expr↑ » k < (f i).order) → coeff R k (φ*∏i in s, 1 - f i) = coeff R k φ :=
  by 
    apply Finset.induction_on s
    ·
      simp 
    ·
      intro a s ha ih t 
      simp only [Finset.mem_insert, forall_eq_or_imp] at t 
      rw [Finset.prod_insert ha, ←mul_assocₓ, mul_right_commₓ, coeff_mul_one_sub_of_lt_order _ t.1]
      exact ih t.2

end OrderBasic

section OrderZeroNeOne

variable[CommSemiringₓ R][Nontrivial R]

/-- The order of the formal power series `1` is `0`.-/
@[simp]
theorem order_one : order (1 : PowerSeries R) = 0 :=
  by 
    simpa using order_monomial_of_ne_zero 0 (1 : R) one_ne_zero

/-- The order of the formal power series `X` is `1`.-/
@[simp]
theorem order_X : order (X : PowerSeries R) = 1 :=
  by 
    simpa only [Nat.cast_one] using order_monomial_of_ne_zero 1 (1 : R) one_ne_zero

/-- The order of the formal power series `X^n` is `n`.-/
@[simp]
theorem order_X_pow (n : ℕ) : order ((X : PowerSeries R)^n) = n :=
  by 
    rw [X_pow_eq, order_monomial_of_ne_zero]
    exact one_ne_zero

end OrderZeroNeOne

section OrderIsDomain

variable[CommRingₓ R][IsDomain R]

/-- The order of the product of two formal power series over an integral domain
 is the sum of their orders.-/
theorem order_mul (φ ψ : PowerSeries R) : order (φ*ψ) = order φ+order ψ :=
  multiplicity.mul X_prime

end OrderIsDomain

end PowerSeries

namespace Polynomial

open Finsupp

variable{σ : Type _}{R : Type _}[CommSemiringₓ R]

/-- The natural inclusion from polynomials into formal power series.-/
instance coe_to_power_series : Coe (Polynomial R) (PowerSeries R) :=
  ⟨fun φ => PowerSeries.mk$ fun n => coeff φ n⟩

@[simp, normCast]
theorem coeff_coe (φ : Polynomial R) n : PowerSeries.coeff R n φ = coeff φ n :=
  congr_argₓ (coeff φ) Finsupp.single_eq_same

@[simp, normCast]
theorem coe_monomial (n : ℕ) (a : R) : (monomial n a : PowerSeries R) = PowerSeries.monomial R n a :=
  by 
    ext 
    simp [coeff_coe, PowerSeries.coeff_monomial, Polynomial.coeff_monomial, eq_comm]

@[simp, normCast]
theorem coe_zero : ((0 : Polynomial R) : PowerSeries R) = 0 :=
  rfl

@[simp, normCast]
theorem coe_one : ((1 : Polynomial R) : PowerSeries R) = 1 :=
  by 
    have  := coe_monomial 0 (1 : R)
    rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, normCast]
theorem coe_add (φ ψ : Polynomial R) : ((φ+ψ : Polynomial R) : PowerSeries R) = φ+ψ :=
  by 
    ext 
    simp 

@[simp, normCast]
theorem coe_mul (φ ψ : Polynomial R) : ((φ*ψ : Polynomial R) : PowerSeries R) = φ*ψ :=
  PowerSeries.ext$
    fun n =>
      by 
        simp only [coeff_coe, PowerSeries.coeff_mul, coeff_mul]

@[simp, normCast]
theorem coe_C (a : R) : ((C a : Polynomial R) : PowerSeries R) = PowerSeries.c R a :=
  by 
    have  := coe_monomial 0 a 
    rwa [PowerSeries.monomial_zero_eq_C_apply] at this

@[simp, normCast]
theorem coe_X : ((X : Polynomial R) : PowerSeries R) = PowerSeries.x :=
  coe_monomial _ _

/--
The coercion from polynomials to power series
as a ring homomorphism.
-/
def coe_to_power_series.ring_hom : Polynomial R →+* PowerSeries R :=
  { toFun := (coeₓ : Polynomial R → PowerSeries R), map_zero' := coe_zero, map_one' := coe_one, map_add' := coe_add,
    map_mul' := coe_mul }

end Polynomial

