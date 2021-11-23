import Mathbin.Algebra.BigOperators.Ring 
import Mathbin.NumberTheory.Divisors 
import Mathbin.Algebra.Squarefree 
import Mathbin.Algebra.Invertible

/-!
# Arithmetic Functions and Dirichlet Convolution

This file defines arithmetic functions, which are functions from `ℕ` to a specified type that map 0
to 0. In the literature, they are often instead defined as functions from `ℕ+`. These arithmetic
functions are endowed with a multiplication, given by Dirichlet convolution, and pointwise addition,
to form the Dirichlet ring.

## Main Definitions
 * `arithmetic_function R` consists of functions `f : ℕ → R` such that `f 0 = 0`.
 * An arithmetic function `f` `is_multiplicative` when `x.coprime y → f (x * y) = f x * f y`.
 * The pointwise operations `pmul` and `ppow` differ from the multiplication
  and power instances on `arithmetic_function R`, which use Dirichlet multiplication.
 * `ζ` is the arithmetic function such that `ζ x = 1` for `0 < x`.
 * `σ k` is the arithmetic function such that `σ k x = ∑ y in divisors x, y ^ k` for `0 < x`.
 * `pow k` is the arithmetic function such that `pow k x = x ^ k` for `0 < x`.
 * `id` is the identity arithmetic function on `ℕ`.
 * `ω n` is the number of distinct prime factors of `n`.
 * `Ω n` is the number of prime factors of `n` counted with multiplicity.
 * `μ` is the Möbius function.

## Main Results
 * Several forms of Möbius inversion:
 * `sum_eq_iff_sum_mul_moebius_eq` for functions to a `comm_ring`
 * `sum_eq_iff_sum_smul_moebius_eq` for functions to an `add_comm_group`
 * `prod_eq_iff_prod_pow_moebius_eq` for functions to a `comm_group`
 * `prod_eq_iff_prod_pow_moebius_eq_of_nonzero` for functions to a `comm_group_with_zero`

## Notation
The arithmetic functions `ζ` and `σ` have Greek letter names, which are localized notation in
the namespace `arithmetic_function`.

## Tags
arithmetic functions, dirichlet convolution, divisors

-/


open Finset

open_locale BigOperators

namespace Nat

variable(R : Type _)

-- error in NumberTheory.ArithmeticFunction: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler has_zero
/-- An arithmetic function is a function from `ℕ` that maps 0 to 0. In the literature, they are
  often instead defined as functions from `ℕ+`. Multiplication on `arithmetic_functions` is by
  Dirichlet convolution. -/
@[derive #["[", expr has_zero, ",", expr inhabited, "]"]]
def arithmetic_function [has_zero R] :=
zero_hom exprℕ() R

variable{R}

namespace ArithmeticFunction

section HasZero

variable[HasZero R]

instance  : CoeFun (arithmetic_function R) fun _ => ℕ → R :=
  ZeroHom.hasCoeToFun

@[simp]
theorem to_fun_eq (f : arithmetic_function R) : f.to_fun = f :=
  rfl

@[simp]
theorem map_zero {f : arithmetic_function R} : f 0 = 0 :=
  ZeroHom.map_zero' f

theorem coe_inj {f g : arithmetic_function R} : (f : ℕ → R) = g ↔ f = g :=
  ⟨fun h => ZeroHom.coe_inj h, fun h => h ▸ rfl⟩

@[simp]
theorem zero_apply {x : ℕ} : (0 : arithmetic_function R) x = 0 :=
  ZeroHom.zero_apply x

@[ext]
theorem ext ⦃f g : arithmetic_function R⦄ (h : ∀ x, f x = g x) : f = g :=
  ZeroHom.ext h

theorem ext_iff {f g : arithmetic_function R} : f = g ↔ ∀ x, f x = g x :=
  ZeroHom.ext_iff

section HasOne

variable[HasOne R]

instance  : HasOne (arithmetic_function R) :=
  ⟨⟨fun x => ite (x = 1) 1 0, rfl⟩⟩

@[simp]
theorem one_one : (1 : arithmetic_function R) 1 = 1 :=
  rfl

@[simp]
theorem one_apply_ne {x : ℕ} (h : x ≠ 1) : (1 : arithmetic_function R) x = 0 :=
  if_neg h

end HasOne

end HasZero

instance nat_coe [HasZero R] [HasOne R] [Add R] : Coe (arithmetic_function ℕ) (arithmetic_function R) :=
  ⟨fun f =>
      ⟨«expr↑ » (f : ℕ → ℕ),
        by 
          trans «expr↑ » (f 0)
          rfl 
          simp ⟩⟩

@[simp]
theorem nat_coe_nat (f : arithmetic_function ℕ) : («expr↑ » f : arithmetic_function ℕ) = f :=
  ext$ fun _ => cast_id _

@[simp]
theorem nat_coe_apply [HasZero R] [HasOne R] [Add R] {f : arithmetic_function ℕ} {x : ℕ} :
  (f : arithmetic_function R) x = f x :=
  rfl

instance int_coe [HasZero R] [HasOne R] [Add R] [Neg R] : Coe (arithmetic_function ℤ) (arithmetic_function R) :=
  ⟨fun f =>
      ⟨«expr↑ » (f : ℕ → ℤ),
        by 
          trans «expr↑ » (f 0)
          rfl 
          simp ⟩⟩

@[simp]
theorem int_coe_int (f : arithmetic_function ℤ) : («expr↑ » f : arithmetic_function ℤ) = f :=
  ext$ fun _ => Int.cast_id _

@[simp]
theorem int_coe_apply [HasZero R] [HasOne R] [Add R] [Neg R] {f : arithmetic_function ℤ} {x : ℕ} :
  (f : arithmetic_function R) x = f x :=
  rfl

@[simp]
theorem coe_coe [HasZero R] [HasOne R] [Add R] [Neg R] {f : arithmetic_function ℕ} :
  ((f : arithmetic_function ℤ) : arithmetic_function R) = f :=
  by 
    ext 
    simp 

section AddMonoidₓ

variable[AddMonoidₓ R]

instance  : Add (arithmetic_function R) :=
  ⟨fun f g =>
      ⟨fun n => f n+g n,
        by 
          simp ⟩⟩

@[simp]
theorem add_apply {f g : arithmetic_function R} {n : ℕ} : (f+g) n = f n+g n :=
  rfl

instance  : AddMonoidₓ (arithmetic_function R) :=
  { arithmetic_function.has_zero R, arithmetic_function.has_add with
    add_assoc := fun _ _ _ => ext fun _ => add_assocₓ _ _ _, zero_add := fun _ => ext fun _ => zero_addₓ _,
    add_zero := fun _ => ext fun _ => add_zeroₓ _ }

end AddMonoidₓ

instance  [AddCommMonoidₓ R] : AddCommMonoidₓ (arithmetic_function R) :=
  { arithmetic_function.add_monoid with add_comm := fun _ _ => ext fun _ => add_commₓ _ _ }

instance  [AddGroupₓ R] : AddGroupₓ (arithmetic_function R) :=
  { arithmetic_function.add_monoid with
    neg :=
      fun f =>
        ⟨fun n => -f n,
          by 
            simp ⟩,
    add_left_neg := fun _ => ext fun _ => add_left_negₓ _ }

instance  [AddCommGroupₓ R] : AddCommGroupₓ (arithmetic_function R) :=
  { arithmetic_function.add_comm_monoid, arithmetic_function.add_group with  }

section HasScalar

variable{M : Type _}[HasZero R][AddCommMonoidₓ M][HasScalar R M]

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
instance  : HasScalar (arithmetic_function R) (arithmetic_function M) :=
  ⟨fun f g =>
      ⟨fun n => ∑x in divisors_antidiagonal n, f x.fst • g x.snd,
        by 
          simp ⟩⟩

@[simp]
theorem smul_apply {f : arithmetic_function R} {g : arithmetic_function M} {n : ℕ} :
  (f • g) n = ∑x in divisors_antidiagonal n, f x.fst • g x.snd :=
  rfl

end HasScalar

/-- The Dirichlet convolution of two arithmetic functions `f` and `g` is another arithmetic function
  such that `(f * g) n` is the sum of `f x * g y` over all `(x,y)` such that `x * y = n`. -/
instance  [Semiringₓ R] : Mul (arithmetic_function R) :=
  ⟨· • ·⟩

@[simp]
theorem mul_apply [Semiringₓ R] {f g : arithmetic_function R} {n : ℕ} :
  (f*g) n = ∑x in divisors_antidiagonal n, f x.fst*g x.snd :=
  rfl

section Module

variable{M : Type _}[Semiringₓ R][AddCommMonoidₓ M][Module R M]

theorem mul_smul' (f g : arithmetic_function R) (h : arithmetic_function M) : (f*g) • h = f • g • h :=
  by 
    ext n 
    simp only [mul_apply, smul_apply, sum_smul, mul_smul, smul_sum, Finset.sum_sigma']
    apply Finset.sum_bij 
    swap 5
    ·
      rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H 
      exact ⟨(k, l*j), (l, j)⟩
    ·
      rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H 
      simp only [Finset.mem_sigma, mem_divisors_antidiagonal] at H⊢
      rcases H with ⟨⟨rfl, n0⟩, rfl, i0⟩
      refine' ⟨⟨(mul_assocₓ _ _ _).symm, n0⟩, rfl, _⟩
      rw [mul_ne_zero_iff] at *
      exact ⟨i0.2, n0.2⟩
    ·
      rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H 
      simp only [mul_assocₓ]
    ·
      rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩ H₁ H₂ 
      simp only [Finset.mem_sigma, mem_divisors_antidiagonal, and_imp, Prod.mk.inj_iffₓ, add_commₓ, heq_iff_eq] at H₁
        H₂⊢
      rintro rfl h2 rfl rfl 
      exact ⟨⟨Eq.trans H₁.2.1.symm H₂.2.1, rfl⟩, rfl, rfl⟩
    ·
      rintro ⟨⟨i, j⟩, ⟨k, l⟩⟩ H 
      refine' ⟨⟨(i*k, l), (i, k)⟩, _, _⟩
      ·
        simp only [Finset.mem_sigma, mem_divisors_antidiagonal] at H⊢
        rcases H with ⟨⟨rfl, n0⟩, rfl, j0⟩
        refine' ⟨⟨mul_assocₓ _ _ _, n0⟩, rfl, _⟩
        rw [mul_ne_zero_iff] at *
        exact ⟨n0.1, j0.1⟩
      ·
        simp only [true_andₓ, mem_divisors_antidiagonal, and_trueₓ, Prod.mk.inj_iffₓ, eq_self_iff_true, Ne.def,
          mem_sigma, heq_iff_eq] at H⊢
        rw [H.2.1]

-- error in NumberTheory.ArithmeticFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem one_smul' (b : arithmetic_function M) : «expr = »(«expr • »((1 : arithmetic_function R), b), b) :=
begin
  ext [] [] [],
  rw [expr smul_apply] [],
  by_cases [expr x0, ":", expr «expr = »(x, 0)],
  { simp [] [] [] ["[", expr x0, "]"] [] [] },
  have [ident h] [":", expr «expr ⊆ »({(1, x)}, divisors_antidiagonal x)] [":=", expr by simp [] [] [] ["[", expr x0, "]"] [] []],
  rw ["<-", expr sum_subset h] [],
  { simp [] [] [] [] [] [] },
  intros [ident y, ident ymem, ident ynmem],
  have [ident y1ne] [":", expr «expr ≠ »(y.fst, 1)] [],
  { intro [ident con],
    simp [] [] ["only"] ["[", expr con, ",", expr mem_divisors_antidiagonal, ",", expr one_mul, ",", expr ne.def, "]"] [] ["at", ident ymem],
    simp [] [] ["only"] ["[", expr mem_singleton, ",", expr prod.ext_iff, "]"] [] ["at", ident ynmem],
    tauto [] },
  simp [] [] [] ["[", expr y1ne, "]"] [] []
end

end Module

section Semiringₓ

variable[Semiringₓ R]

-- error in NumberTheory.ArithmeticFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : monoid (arithmetic_function R) :=
{ one_mul := one_smul',
  mul_one := λ f, begin
    ext [] [] [],
    rw [expr mul_apply] [],
    by_cases [expr x0, ":", expr «expr = »(x, 0)],
    { simp [] [] [] ["[", expr x0, "]"] [] [] },
    have [ident h] [":", expr «expr ⊆ »({(x, 1)}, divisors_antidiagonal x)] [":=", expr by simp [] [] [] ["[", expr x0, "]"] [] []],
    rw ["<-", expr sum_subset h] [],
    { simp [] [] [] [] [] [] },
    intros [ident y, ident ymem, ident ynmem],
    have [ident y2ne] [":", expr «expr ≠ »(y.snd, 1)] [],
    { intro [ident con],
      simp [] [] ["only"] ["[", expr con, ",", expr mem_divisors_antidiagonal, ",", expr mul_one, ",", expr ne.def, "]"] [] ["at", ident ymem],
      simp [] [] ["only"] ["[", expr mem_singleton, ",", expr prod.ext_iff, "]"] [] ["at", ident ynmem],
      tauto [] },
    simp [] [] [] ["[", expr y2ne, "]"] [] []
  end,
  mul_assoc := mul_smul',
  ..arithmetic_function.has_one,
  ..arithmetic_function.has_mul }

instance  : Semiringₓ (arithmetic_function R) :=
  { arithmetic_function.has_zero R, arithmetic_function.has_mul, arithmetic_function.has_add,
    arithmetic_function.add_comm_monoid, arithmetic_function.monoid with
    zero_mul :=
      fun f =>
        by 
          ext 
          simp only [mul_apply, zero_mul, sum_const_zero, zero_apply],
    mul_zero :=
      fun f =>
        by 
          ext 
          simp only [mul_apply, sum_const_zero, mul_zero, zero_apply],
    left_distrib :=
      fun a b c =>
        by 
          ext 
          simp only [←sum_add_distrib, mul_addₓ, mul_apply, add_apply],
    right_distrib :=
      fun a b c =>
        by 
          ext 
          simp only [←sum_add_distrib, add_mulₓ, mul_apply, add_apply] }

end Semiringₓ

instance  [CommSemiringₓ R] : CommSemiringₓ (arithmetic_function R) :=
  { arithmetic_function.semiring with
    mul_comm :=
      fun f g =>
        by 
          ext 
          rw [mul_apply, ←map_swap_divisors_antidiagonal, sum_map]
          simp [mul_commₓ] }

instance  [CommRingₓ R] : CommRingₓ (arithmetic_function R) :=
  { arithmetic_function.add_comm_group, arithmetic_function.comm_semiring with  }

instance  {M : Type _} [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] :
  Module (arithmetic_function R) (arithmetic_function M) :=
  { one_smul := one_smul', mul_smul := mul_smul',
    smul_add :=
      fun r x y =>
        by 
          ext 
          simp only [sum_add_distrib, smul_add, smul_apply, add_apply],
    smul_zero :=
      fun r =>
        by 
          ext 
          simp only [smul_apply, sum_const_zero, smul_zero, zero_apply],
    add_smul :=
      fun r s x =>
        by 
          ext 
          simp only [add_smul, sum_add_distrib, smul_apply, add_apply],
    zero_smul :=
      fun r =>
        by 
          ext 
          simp only [smul_apply, sum_const_zero, zero_smul, zero_apply] }

section Zeta

/-- `ζ 0 = 0`, otherwise `ζ x = 1`. The Dirichlet Series is the Riemann ζ.  -/
def zeta : arithmetic_function ℕ :=
  ⟨fun x => ite (x = 0) 0 1, rfl⟩

localized [ArithmeticFunction] notation "ζ" => zeta

@[simp]
theorem zeta_apply {x : ℕ} : ζ x = if x = 0 then 0 else 1 :=
  rfl

theorem zeta_apply_ne {x : ℕ} (h : x ≠ 0) : ζ x = 1 :=
  if_neg h

@[simp]
theorem coe_zeta_mul_apply [Semiringₓ R] {f : arithmetic_function R} {x : ℕ} :
  («expr↑ » ζ*f) x = ∑i in divisors x, f i :=
  by 
    rw [mul_apply]
    trans ∑i in divisors_antidiagonal x, f i.snd
    ·
      apply sum_congr rfl 
      intro i hi 
      rcases mem_divisors_antidiagonal.1 hi with ⟨rfl, h⟩
      rw [nat_coe_apply, zeta_apply_ne (left_ne_zero_of_mul h), cast_one, one_mulₓ]
    ·
      apply sum_bij fun i h => Prod.snd i
      ·
        rintro ⟨a, b⟩ h 
        simp [snd_mem_divisors_of_mem_antidiagonal h]
      ·
        rintro ⟨a, b⟩ h 
        rfl
      ·
        rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h1 h2 h 
        dsimp  at h 
        rw [h] at *
        rw [mem_divisors_antidiagonal] at *
        ext 
        swap
        ·
          rfl 
        simp only [Prod.fst, Prod.snd] at *
        apply Nat.eq_of_mul_eq_mul_rightₓ _ (Eq.trans h1.1 h2.1.symm)
        rcases h1 with ⟨rfl, h⟩
        apply Nat.pos_of_ne_zeroₓ (right_ne_zero_of_mul h)
      ·
        intro a ha 
        rcases mem_divisors.1 ha with ⟨⟨b, rfl⟩, ne0⟩
        use (b, a)
        simp [ne0, mul_commₓ]

theorem coe_zeta_smul_apply {M : Type _} [CommRingₓ R] [AddCommGroupₓ M] [Module R M] {f : arithmetic_function M}
  {x : ℕ} : ((«expr↑ » ζ : arithmetic_function R) • f) x = ∑i in divisors x, f i :=
  by 
    rw [smul_apply]
    trans ∑i in divisors_antidiagonal x, f i.snd
    ·
      apply sum_congr rfl 
      intro i hi 
      rcases mem_divisors_antidiagonal.1 hi with ⟨rfl, h⟩
      rw [nat_coe_apply, zeta_apply_ne (left_ne_zero_of_mul h), cast_one, one_smul]
    ·
      apply sum_bij fun i h => Prod.snd i
      ·
        rintro ⟨a, b⟩ h 
        simp [snd_mem_divisors_of_mem_antidiagonal h]
      ·
        rintro ⟨a, b⟩ h 
        rfl
      ·
        rintro ⟨a1, b1⟩ ⟨a2, b2⟩ h1 h2 h 
        dsimp  at h 
        rw [h] at *
        rw [mem_divisors_antidiagonal] at *
        ext 
        swap
        ·
          rfl 
        simp only [Prod.fst, Prod.snd] at *
        apply Nat.eq_of_mul_eq_mul_rightₓ _ (Eq.trans h1.1 h2.1.symm)
        rcases h1 with ⟨rfl, h⟩
        apply Nat.pos_of_ne_zeroₓ (right_ne_zero_of_mul h)
      ·
        intro a ha 
        rcases mem_divisors.1 ha with ⟨⟨b, rfl⟩, ne0⟩
        use (b, a)
        simp [ne0, mul_commₓ]

@[simp]
theorem coe_mul_zeta_apply [Semiringₓ R] {f : arithmetic_function R} {x : ℕ} : (f*ζ) x = ∑i in divisors x, f i :=
  by 
    apply MulOpposite.op_injective 
    rw [op_sum]
    convert
      @coe_zeta_mul_apply («expr ᵐᵒᵖ» R) _
        { toFun := MulOpposite.op ∘ f,
          map_zero' :=
            by 
              simp  }
        x 
    rw [mul_apply, mul_apply, op_sum]
    convLHS => rw [←map_swap_divisors_antidiagonal]
    rw [sum_map]
    apply sum_congr rfl 
    intro y hy 
    byCases' h1 : y.fst = 0
    ·
      simp [Function.comp_apply, h1]
    ·
      simp only [h1, mul_oneₓ, one_mulₓ, Prod.fst_swap, Function.Embedding.coe_fn_mk, Prod.snd_swap, if_false,
        zeta_apply, ZeroHom.coe_mk, nat_coe_apply, cast_one]

theorem zeta_mul_apply {f : arithmetic_function ℕ} {x : ℕ} : (ζ*f) x = ∑i in divisors x, f i :=
  by 
    rw [←nat_coe_nat ζ, coe_zeta_mul_apply]

theorem mul_zeta_apply {f : arithmetic_function ℕ} {x : ℕ} : (f*ζ) x = ∑i in divisors x, f i :=
  by 
    rw [←nat_coe_nat ζ, coe_mul_zeta_apply]

end Zeta

open_locale ArithmeticFunction

section Pmul

/-- This is the pointwise product of `arithmetic_function`s. -/
def pmul [MulZeroClass R] (f g : arithmetic_function R) : arithmetic_function R :=
  ⟨fun x => f x*g x,
    by 
      simp ⟩

@[simp]
theorem pmul_apply [MulZeroClass R] {f g : arithmetic_function R} {x : ℕ} : f.pmul g x = f x*g x :=
  rfl

theorem pmul_comm [CommMonoidWithZero R] (f g : arithmetic_function R) : f.pmul g = g.pmul f :=
  by 
    ext 
    simp [mul_commₓ]

variable[Semiringₓ R]

@[simp]
theorem pmul_zeta (f : arithmetic_function R) : f.pmul («expr↑ » ζ) = f :=
  by 
    ext x 
    cases x <;> simp [Nat.succ_ne_zero]

@[simp]
theorem zeta_pmul (f : arithmetic_function R) : (ζ : arithmetic_function R).pmul f = f :=
  by 
    ext x 
    cases x <;> simp [Nat.succ_ne_zero]

/-- This is the pointwise power of `arithmetic_function`s. -/
def ppow (f : arithmetic_function R) (k : ℕ) : arithmetic_function R :=
  if h0 : k = 0 then ζ else
    ⟨fun x => f x^k,
      by 
        rw [map_zero]
        exact zero_pow (Nat.pos_of_ne_zeroₓ h0)⟩

@[simp]
theorem ppow_zero {f : arithmetic_function R} : f.ppow 0 = ζ :=
  by 
    rw [ppow, dif_pos rfl]

@[simp]
theorem ppow_apply {f : arithmetic_function R} {k x : ℕ} (kpos : 0 < k) : f.ppow k x = (f x^k) :=
  by 
    rw [ppow, dif_neg (ne_of_gtₓ kpos)]
    rfl

theorem ppow_succ {f : arithmetic_function R} {k : ℕ} : f.ppow (k+1) = f.pmul (f.ppow k) :=
  by 
    ext x 
    rw [ppow_apply (Nat.succ_posₓ k), pow_succₓ]
    induction k <;> simp 

theorem ppow_succ' {f : arithmetic_function R} {k : ℕ} {kpos : 0 < k} : f.ppow (k+1) = (f.ppow k).pmul f :=
  by 
    ext x 
    rw [ppow_apply (Nat.succ_posₓ k), pow_succ'ₓ]
    induction k <;> simp 

end Pmul

/-- Multiplicative functions -/
def is_multiplicative [MonoidWithZeroₓ R] (f : arithmetic_function R) : Prop :=
  f 1 = 1 ∧ ∀ {m n : ℕ}, m.coprime n → f (m*n) = f m*f n

namespace IsMultiplicative

section MonoidWithZeroₓ

variable[MonoidWithZeroₓ R]

@[simp]
theorem map_one {f : arithmetic_function R} (h : f.is_multiplicative) : f 1 = 1 :=
  h.1

@[simp]
theorem map_mul_of_coprime {f : arithmetic_function R} (hf : f.is_multiplicative) {m n : ℕ} (h : m.coprime n) :
  f (m*n) = f m*f n :=
  hf.2 h

end MonoidWithZeroₓ

theorem nat_cast {f : arithmetic_function ℕ} [Semiringₓ R] (h : f.is_multiplicative) :
  is_multiplicative (f : arithmetic_function R) :=
  ⟨by 
      simp [h],
    fun m n cop =>
      by 
        simp [cop, h]⟩

theorem int_cast {f : arithmetic_function ℤ} [Ringₓ R] (h : f.is_multiplicative) :
  is_multiplicative (f : arithmetic_function R) :=
  ⟨by 
      simp [h],
    fun m n cop =>
      by 
        simp [cop, h]⟩

theorem mul [CommSemiringₓ R] {f g : arithmetic_function R} (hf : f.is_multiplicative) (hg : g.is_multiplicative) :
  is_multiplicative (f*g) :=
  ⟨by 
      simp [hf, hg],
    by 
      simp only [mul_apply]
      intro m n cop 
      rw [sum_mul_sum]
      symm 
      apply sum_bij fun x : (ℕ × ℕ) × ℕ × ℕ h => (x.1.1*x.2.1, x.1.2*x.2.2)
      ·
        rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h 
        simp only [mem_divisors_antidiagonal, Ne.def, mem_product] at h 
        rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
        simp only [mem_divisors_antidiagonal, Nat.mul_eq_zero, Ne.def]
        split 
        ·
          ring 
        rw [Nat.mul_eq_zero] at *
        apply not_orₓ ha hb
      ·
        rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ h 
        simp only [mem_divisors_antidiagonal, Ne.def, mem_product] at h 
        rcases h with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
        dsimp only 
        rw [hf.map_mul_of_coprime cop.coprime_mul_right.coprime_mul_right_right,
          hg.map_mul_of_coprime cop.coprime_mul_left.coprime_mul_left_right]
        ring
      ·
        rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ ⟨⟨c1, c2⟩, ⟨d1, d2⟩⟩ hab hcd h 
        simp only [mem_divisors_antidiagonal, Ne.def, mem_product] at hab 
        rcases hab with ⟨⟨rfl, ha⟩, ⟨rfl, hb⟩⟩
        simp only [mem_divisors_antidiagonal, Ne.def, mem_product] at hcd 
        simp only [Prod.mk.inj_iffₓ] at h 
        ext <;> dsimp only
        ·
          trans Nat.gcdₓ (a1*a2) (a1*b1)
          ·
            rw [Nat.gcd_mul_leftₓ, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_oneₓ]
          ·
            rw [←hcd.1.1, ←hcd.2.1] at cop 
            rw [←hcd.1.1, h.1, Nat.gcd_mul_leftₓ, cop.coprime_mul_left.coprime_mul_right_right.gcd_eq_one, mul_oneₓ]
        ·
          trans Nat.gcdₓ (a1*a2) (a2*b2)
          ·
            rw [mul_commₓ, Nat.gcd_mul_leftₓ, cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one, mul_oneₓ]
          ·
            rw [←hcd.1.1, ←hcd.2.1] at cop 
            rw [←hcd.1.1, h.2, mul_commₓ, Nat.gcd_mul_leftₓ, cop.coprime_mul_right.coprime_mul_left_right.gcd_eq_one,
              mul_oneₓ]
        ·
          trans Nat.gcdₓ (b1*b2) (a1*b1)
          ·
            rw [mul_commₓ, Nat.gcd_mul_rightₓ, cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, one_mulₓ]
          ·
            rw [←hcd.1.1, ←hcd.2.1] at cop 
            rw [←hcd.2.1, h.1, mul_commₓ c1 d1, Nat.gcd_mul_leftₓ,
              cop.coprime_mul_right.coprime_mul_left_right.symm.gcd_eq_one, mul_oneₓ]
        ·
          trans Nat.gcdₓ (b1*b2) (a2*b2)
          ·
            rw [Nat.gcd_mul_rightₓ, cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one, one_mulₓ]
          ·
            rw [←hcd.1.1, ←hcd.2.1] at cop 
            rw [←hcd.2.1, h.2, Nat.gcd_mul_rightₓ, cop.coprime_mul_left.coprime_mul_right_right.symm.gcd_eq_one,
              one_mulₓ]
      ·
        rintro ⟨b1, b2⟩ h 
        simp only [mem_divisors_antidiagonal, Ne.def, mem_product] at h 
        use ((b1.gcd m, b2.gcd m), (b1.gcd n, b2.gcd n))
        simp only [exists_prop, Prod.mk.inj_iffₓ, Ne.def, mem_product, mem_divisors_antidiagonal]
        rw [←cop.gcd_mul _, ←cop.gcd_mul _, ←h.1, Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mulₓ cop h.1,
          Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mulₓ cop.symm _]
        ·
          rw [Nat.mul_eq_zero, Decidable.not_or_iff_and_not] at h 
          simp [h.2.1, h.2.2]
        rw [mul_commₓ n m, h.1]⟩

theorem pmul [CommSemiringₓ R] {f g : arithmetic_function R} (hf : f.is_multiplicative) (hg : g.is_multiplicative) :
  is_multiplicative (f.pmul g) :=
  ⟨by 
      simp [hf, hg],
    fun m n cop =>
      by 
        simp only [pmul_apply, hf.map_mul_of_coprime cop, hg.map_mul_of_coprime cop]
        ring⟩

end IsMultiplicative

section SpecialFunctions

/-- The identity on `ℕ` as an `arithmetic_function`.  -/
def id : arithmetic_function ℕ :=
  ⟨id, rfl⟩

@[simp]
theorem id_apply {x : ℕ} : id x = x :=
  rfl

/-- `pow k n = n ^ k`, except `pow 0 0 = 0`. -/
def pow (k : ℕ) : arithmetic_function ℕ :=
  id.ppow k

@[simp]
theorem pow_apply {k n : ℕ} : pow k n = if k = 0 ∧ n = 0 then 0 else n^k :=
  by 
    cases k
    ·
      simp [pow]
    simp [pow, (ne_of_ltₓ (Nat.succ_posₓ k)).symm]

/-- `σ k n` is the sum of the `k`th powers of the divisors of `n` -/
def Sigma (k : ℕ) : arithmetic_function ℕ :=
  ⟨fun n => ∑d in divisors n, d^k,
    by 
      simp ⟩

localized [ArithmeticFunction] notation "σ" => Sigma

@[simp]
theorem sigma_apply {k n : ℕ} : σ k n = ∑d in divisors n, d^k :=
  rfl

theorem sigma_one_apply {n : ℕ} : σ 1 n = ∑d in divisors n, d :=
  by 
    simp 

theorem zeta_mul_pow_eq_sigma {k : ℕ} : (ζ*pow k) = σ k :=
  by 
    ext 
    rw [Sigma, zeta_mul_apply]
    apply sum_congr rfl 
    intro x hx 
    rw [pow_apply, if_neg (not_and_of_not_right _ _)]
    contrapose! hx 
    simp [hx]

theorem is_multiplicative_zeta : is_multiplicative ζ :=
  ⟨by 
      simp ,
    fun m n cop =>
      by 
        cases m
        ·
          simp 
        cases n
        ·
          simp 
        simp [Nat.succ_ne_zero]⟩

theorem is_multiplicative_id : is_multiplicative arithmetic_function.id :=
  ⟨rfl, fun _ _ _ => rfl⟩

theorem is_multiplicative.ppow [CommSemiringₓ R] {f : arithmetic_function R} (hf : f.is_multiplicative) {k : ℕ} :
  is_multiplicative (f.ppow k) :=
  by 
    induction' k with k hi
    ·
      exact is_multiplicative_zeta.nat_cast
    ·
      rw [ppow_succ]
      apply hf.pmul hi

theorem is_multiplicative_pow {k : ℕ} : is_multiplicative (pow k) :=
  is_multiplicative_id.ppow

theorem is_multiplicative_sigma {k : ℕ} : is_multiplicative (Sigma k) :=
  by 
    rw [←zeta_mul_pow_eq_sigma]
    apply is_multiplicative_zeta.mul is_multiplicative_pow

/-- `Ω n` is the number of prime factors of `n`. -/
def card_factors : arithmetic_function ℕ :=
  ⟨fun n => n.factors.length,
    by 
      simp ⟩

localized [ArithmeticFunction] notation "Ω" => card_factors

theorem card_factors_apply {n : ℕ} : Ω n = n.factors.length :=
  rfl

@[simp]
theorem card_factors_one : Ω 1 = 0 :=
  by 
    simp [card_factors]

theorem card_factors_eq_one_iff_prime {n : ℕ} : Ω n = 1 ↔ n.prime :=
  by 
    refine' ⟨fun h => _, fun h => List.length_eq_one.2 ⟨n, factors_prime h⟩⟩
    cases n
    ·
      contrapose! h 
      simp 
    rcases List.length_eq_one.1 h with ⟨x, hx⟩
    rw [←prod_factors n.succ_pos, hx, List.prod_singleton]
    apply prime_of_mem_factors 
    rw [hx, List.mem_singleton]

theorem card_factors_mul {m n : ℕ} (m0 : m ≠ 0) (n0 : n ≠ 0) : Ω (m*n) = Ω m+Ω n :=
  by 
    rw [card_factors_apply, card_factors_apply, card_factors_apply, ←Multiset.coe_card, ←factors_eq,
      UniqueFactorizationMonoid.normalized_factors_mul m0 n0, factors_eq, factors_eq, Multiset.card_add,
      Multiset.coe_card, Multiset.coe_card]

theorem card_factors_multiset_prod {s : Multiset ℕ} (h0 : s.prod ≠ 0) : Ω s.prod = (Multiset.map Ω s).Sum :=
  by 
    revert h0 
    apply s.induction_on
    ·
      simp 
    intro a t h h0 
    rw [Multiset.prod_cons, mul_ne_zero_iff] at h0 
    simp [h0, card_factors_mul, h]

/-- `ω n` is the number of distinct prime factors of `n`. -/
def card_distinct_factors : arithmetic_function ℕ :=
  ⟨fun n => n.factors.erase_dup.length,
    by 
      simp ⟩

localized [ArithmeticFunction] notation "ω" => card_distinct_factors

theorem card_distinct_factors_zero : ω 0 = 0 :=
  by 
    simp 

theorem card_distinct_factors_apply {n : ℕ} : ω n = n.factors.erase_dup.length :=
  rfl

theorem card_distinct_factors_eq_card_factors_iff_squarefree {n : ℕ} (h0 : n ≠ 0) : ω n = Ω n ↔ Squarefree n :=
  by 
    rw [squarefree_iff_nodup_factors h0, card_distinct_factors_apply]
    split  <;> intro h
    ·
      rw [←List.eq_of_sublist_of_length_eq n.factors.erase_dup_sublist h]
      apply List.nodup_erase_dup
    ·
      rw [h.erase_dup]
      rfl

/-- `μ` is the Möbius function. If `n` is squarefree with an even number of distinct prime factors,
  `μ n = 1`. If `n` is squarefree with an odd number of distinct prime factors, `μ n = -1`.
  If `n` is not squarefree, `μ n = 0`. -/
def moebius : arithmetic_function ℤ :=
  ⟨fun n => if Squarefree n then -1^card_factors n else 0,
    by 
      simp ⟩

localized [ArithmeticFunction] notation "μ" => moebius

@[simp]
theorem moebius_apply_of_squarefree {n : ℕ} (h : Squarefree n) : μ n = (-1^card_factors n) :=
  if_pos h

@[simp]
theorem moebius_eq_zero_of_not_squarefree {n : ℕ} (h : ¬Squarefree n) : μ n = 0 :=
  if_neg h

theorem moebius_ne_zero_iff_squarefree {n : ℕ} : μ n ≠ 0 ↔ Squarefree n :=
  by 
    split  <;> intro h
    ·
      contrapose! h 
      simp [h]
    ·
      simp [h, pow_ne_zero]

theorem moebius_ne_zero_iff_eq_or {n : ℕ} : μ n ≠ 0 ↔ μ n = 1 ∨ μ n = -1 :=
  by 
    split  <;> intro h
    ·
      rw [moebius_ne_zero_iff_squarefree] at h 
      rw [moebius_apply_of_squarefree h]
      apply neg_one_pow_eq_or
    ·
      rcases h with (h | h) <;> simp [h]

open UniqueFactorizationMonoid

-- error in NumberTheory.ArithmeticFunction: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem coe_moebius_mul_coe_zeta [comm_ring R] : «expr = »((«expr * »(exprμ(), exprζ()) : arithmetic_function R), 1) :=
begin
  ext [] [ident x] [],
  cases [expr x] [],
  { simp [] [] ["only"] ["[", expr divisors_zero, ",", expr sum_empty, ",", expr ne.def, ",", expr not_false_iff, ",", expr coe_mul_zeta_apply, ",", expr zero_ne_one, ",", expr one_apply_ne, "]"] [] [] },
  cases [expr x] [],
  { simp [] [] ["only"] ["[", expr moebius_apply_of_squarefree, ",", expr card_factors_one, ",", expr squarefree_one, ",", expr divisors_one, ",", expr int.cast_one, ",", expr sum_singleton, ",", expr coe_mul_zeta_apply, ",", expr one_one, ",", expr int_coe_apply, ",", expr pow_zero, "]"] [] [] },
  rw ["[", expr coe_mul_zeta_apply, ",", expr one_apply_ne (ne_of_gt (succ_lt_succ (nat.succ_pos _))), "]"] [],
  simp_rw ["[", expr int_coe_apply, "]"] [],
  rw ["[", "<-", expr int.cast_sum, ",", "<-", expr sum_filter_ne_zero, "]"] [],
  convert [] [expr int.cast_zero] [],
  simp [] [] ["only"] ["[", expr moebius_ne_zero_iff_squarefree, "]"] [] [],
  suffices [] [":", expr «expr = »(«expr∑ in , »((y : finset exprℕ()), (unique_factorization_monoid.normalized_factors x.succ.succ).to_finset.powerset, ite (squarefree y.val.prod) «expr ^ »((«expr- »(1) : exprℤ()), exprΩ() y.val.prod) 0), 0)],
  { have [ident h] [":", expr «expr = »(«expr∑ in , »((i), _, ite (squarefree i) «expr ^ »((«expr- »(1) : exprℤ()), exprΩ() i) 0), _)] [":=", expr sum_divisors_filter_squarefree (nat.succ_ne_zero _)],
    exact [expr (eq.trans (by congr' [] []) h).trans this] },
  apply [expr eq.trans (sum_congr rfl _) (sum_powerset_neg_one_pow_card_of_nonempty _)],
  { intros [ident y, ident hy],
    rw ["[", expr finset.mem_powerset, ",", "<-", expr finset.val_le_iff, ",", expr multiset.to_finset_val, "]"] ["at", ident hy],
    have [ident h] [":", expr «expr = »(unique_factorization_monoid.normalized_factors y.val.prod, y.val)] [],
    { apply [expr factors_multiset_prod_of_irreducible],
      intros [ident z, ident hz],
      apply [expr irreducible_of_normalized_factor _ (multiset.subset_of_le (le_trans hy (multiset.erase_dup_le _)) hz)] },
    rw ["[", expr if_pos, "]"] [],
    { rw ["[", expr card_factors_apply, ",", "<-", expr multiset.coe_card, ",", "<-", expr factors_eq, ",", expr h, ",", expr finset.card, "]"] [] },
    rw ["[", expr unique_factorization_monoid.squarefree_iff_nodup_normalized_factors, ",", expr h, "]"] [],
    { apply [expr y.nodup] },
    rw ["[", expr ne.def, ",", expr multiset.prod_eq_zero_iff, "]"] [],
    intro [ident con],
    rw ["<-", expr h] ["at", ident con],
    exact [expr not_irreducible_zero (irreducible_of_normalized_factor 0 con)] },
  { rw [expr finset.nonempty] [],
    rcases [expr wf_dvd_monoid.exists_irreducible_factor _ (nat.succ_ne_zero _), "with", "⟨", ident i, ",", ident hi, "⟩"],
    { rcases [expr exists_mem_normalized_factors_of_dvd (nat.succ_ne_zero _) hi.1 hi.2, "with", "⟨", ident j, ",", ident hj, ",", ident hj2, "⟩"],
      use [expr j],
      apply [expr multiset.mem_to_finset.2 hj] },
    rw [expr nat.is_unit_iff] [],
    norm_num [] [] }
end

@[simp]
theorem coe_zeta_mul_coe_moebius [CommRingₓ R] : (ζ*μ : arithmetic_function R) = 1 :=
  by 
    rw [mul_commₓ, coe_moebius_mul_coe_zeta]

@[simp]
theorem moebius_mul_coe_zeta : (μ*ζ : arithmetic_function ℤ) = 1 :=
  by 
    rw [←int_coe_int μ, coe_moebius_mul_coe_zeta]

@[simp]
theorem coe_zeta_mul_moebius : (ζ*μ : arithmetic_function ℤ) = 1 :=
  by 
    rw [←int_coe_int μ, coe_zeta_mul_coe_moebius]

section CommRingₓ

variable[CommRingₓ R]

instance  : Invertible (ζ : arithmetic_function R) :=
  { invOf := μ, inv_of_mul_self := coe_moebius_mul_coe_zeta, mul_inv_of_self := coe_zeta_mul_coe_moebius }

/-- A unit in `arithmetic_function R` that evaluates to `ζ`, with inverse `μ`. -/
def zeta_unit : Units (arithmetic_function R) :=
  ⟨ζ, μ, coe_zeta_mul_coe_moebius, coe_moebius_mul_coe_zeta⟩

@[simp]
theorem coe_zeta_unit : ((zeta_unit : Units (arithmetic_function R)) : arithmetic_function R) = ζ :=
  rfl

@[simp]
theorem inv_zeta_unit : ((zeta_unit⁻¹ : Units (arithmetic_function R)) : arithmetic_function R) = μ :=
  rfl

end CommRingₓ

/-- Möbius inversion for functions to an `add_comm_group`. -/
theorem sum_eq_iff_sum_smul_moebius_eq [AddCommGroupₓ R] {f g : ℕ → R} :
  (∀ n : ℕ, 0 < n → (∑i in n.divisors, f i) = g n) ↔
    ∀ n : ℕ, 0 < n → (∑x : ℕ × ℕ in n.divisors_antidiagonal, μ x.fst • g x.snd) = f n :=
  by 
    let f' : arithmetic_function R := ⟨fun x => if x = 0 then 0 else f x, if_pos rfl⟩
    let g' : arithmetic_function R := ⟨fun x => if x = 0 then 0 else g x, if_pos rfl⟩
    trans (ζ : arithmetic_function ℤ) • f' = g'
    ·
      rw [ext_iff]
      apply forall_congrₓ 
      intro n 
      cases n
      ·
        simp 
      rw [coe_zeta_smul_apply]
      simp only [n.succ_ne_zero, forall_prop_of_true, succ_pos', if_false, ZeroHom.coe_mk]
      rw [sum_congr rfl fun x hx => _]
      rw [if_neg (ne_of_gtₓ (Nat.pos_of_mem_divisors hx))]
    trans μ • g' = f'
    ·
      split  <;> intro h
      ·
        rw [←h, ←mul_smul, moebius_mul_coe_zeta, one_smul]
      ·
        rw [←h, ←mul_smul, coe_zeta_mul_moebius, one_smul]
    ·
      rw [ext_iff]
      apply forall_congrₓ 
      intro n 
      cases n
      ·
        simp 
      simp only [n.succ_ne_zero, forall_prop_of_true, succ_pos', smul_apply, if_false, ZeroHom.coe_mk]
      rw [sum_congr rfl fun x hx => _]
      rw [if_neg (ne_of_gtₓ (Nat.pos_of_mem_divisors (snd_mem_divisors_of_mem_antidiagonal hx)))]

/-- Möbius inversion for functions to a `comm_ring`. -/
theorem sum_eq_iff_sum_mul_moebius_eq [CommRingₓ R] {f g : ℕ → R} :
  (∀ n : ℕ, 0 < n → (∑i in n.divisors, f i) = g n) ↔
    ∀ n : ℕ, 0 < n → (∑x : ℕ × ℕ in n.divisors_antidiagonal, (μ x.fst : R)*g x.snd) = f n :=
  by 
    rw [sum_eq_iff_sum_smul_moebius_eq]
    apply forall_congrₓ 
    intro a 
    apply imp_congr (Iff.refl _) (Eq.congr_left (sum_congr rfl fun x hx => _))
    rw [zsmul_eq_mul]

/-- Möbius inversion for functions to a `comm_group`. -/
theorem prod_eq_iff_prod_pow_moebius_eq [CommGroupₓ R] {f g : ℕ → R} :
  (∀ n : ℕ, 0 < n → (∏i in n.divisors, f i) = g n) ↔
    ∀ n : ℕ, 0 < n → (∏x : ℕ × ℕ in n.divisors_antidiagonal, g x.snd^μ x.fst) = f n :=
  @sum_eq_iff_sum_smul_moebius_eq (Additive R) _ _ _

/-- Möbius inversion for functions to a `comm_group_with_zero`. -/
theorem prod_eq_iff_prod_pow_moebius_eq_of_nonzero [CommGroupWithZero R] {f g : ℕ → R} (hf : ∀ n : ℕ, 0 < n → f n ≠ 0)
  (hg : ∀ n : ℕ, 0 < n → g n ≠ 0) :
  (∀ n : ℕ, 0 < n → (∏i in n.divisors, f i) = g n) ↔
    ∀ n : ℕ, 0 < n → (∏x : ℕ × ℕ in n.divisors_antidiagonal, g x.snd^μ x.fst) = f n :=
  by 
    refine'
        Iff.trans
          (Iff.trans (forall_congrₓ fun n => _)
            (@prod_eq_iff_prod_pow_moebius_eq (Units R) _ (fun n => if h : 0 < n then Units.mk0 (f n) (hf n h) else 1)
              fun n => if h : 0 < n then Units.mk0 (g n) (hg n h) else 1))
          (forall_congrₓ fun n => _) <;>
      refine' imp_congr_right fun hn => _
    ·
      dsimp 
      rw [dif_pos hn, ←Units.eq_iff, ←Units.coe_hom_apply, MonoidHom.map_prod, Units.coe_mk0, prod_congr rfl _]
      intro x hx 
      rw [dif_pos (Nat.pos_of_mem_divisors hx), Units.coe_hom_apply, Units.coe_mk0]
    ·
      dsimp 
      rw [dif_pos hn, ←Units.eq_iff, ←Units.coe_hom_apply, MonoidHom.map_prod, Units.coe_mk0, prod_congr rfl _]
      intro x hx 
      rw [dif_pos (Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx)), Units.coe_hom_apply,
        Units.coe_zpow₀, Units.coe_mk0]

end SpecialFunctions

end ArithmeticFunction

end Nat

