import Mathbin.Algebra.MonoidAlgebra.Basic

/-!
# Theory of univariate polynomials

This file defines `polynomial R`, the type of univariate polynomials over the semiring `R`, builds
a semiring structure on it, and gives basic definitions that are expanded in other files in this
directory.

## Main definitions

* `monomial n a` is the polynomial `a X^n`. Note that `monomial n` is defined as an `R`-linear map.
* `C a` is the constant polynomial `a`. Note that `C` is defined as a ring homomorphism.
* `X` is the polynomial `X`, i.e., `monomial 1 1`.
* `p.sum f` is `∑ n in p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`.
* `p.erase n` is the polynomial `p` in which one removes the `c X^n` term.

There are often two natural variants of lemmas involving sums, depending on whether one acts on the
polynomials, or on the function. The naming convention is that one adds `index` when acting on
the polynomials. For instance,
* `sum_add_index` states that `(p + q).sum f = p.sum f + q.sum f`;
* `sum_add` states that `p.sum (λ n x, f n x + g n x) = p.sum f + p.sum g`.

## Implementation

Polynomials are defined using `add_monoid_algebra R ℕ`, where `R` is a commutative semiring, but
through a structure to make them irreducible from the point of view of the kernel. Most operations
are irreducible since Lean can not compute anyway with `add_monoid_algebra`. There are two
exceptions that we make semireducible:
* The zero polynomial, so that its coefficients are definitionally equal to `0`.
* The scalar action, to permit typeclass search to unfold it to resolve potential instance
  diamonds.

The raw implementation of the equivalence between `polynomial R` and `add_monoid_algebra R ℕ` is
done through `of_finsupp` and `to_finsupp` (or, equivalently, `rcases p` when `p` is a polynomial
gives an element `q` of `add_monoid_algebra R ℕ`, and conversely `⟨q⟩` gives back `p`). The
equivalence is also registered as a ring equiv in `polynomial.to_finsupp_iso`. These should
in general not be used once the basic API for polynomials is constructed.
-/


noncomputable theory

/-- `polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
structure Polynomial (R : Type _) [Semiringₓ R] where of_finsupp :: 
  toFinsupp : AddMonoidAlgebra R ℕ

open Finsupp AddMonoidAlgebra

open_locale BigOperators

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

section Semiringₓ

variable [Semiringₓ R] {p q : Polynomial R}

theorem forall_iff_forall_finsupp (P : Polynomial R → Prop) : (∀ p, P p) ↔ ∀ q : AddMonoidAlgebra R ℕ, P ⟨q⟩ :=
  ⟨fun h q => h ⟨q⟩, fun h ⟨p⟩ => h p⟩

theorem exists_iff_exists_finsupp (P : Polynomial R → Prop) : (∃ p, P p) ↔ ∃ q : AddMonoidAlgebra R ℕ, P ⟨q⟩ :=
  ⟨fun ⟨⟨p⟩, hp⟩ => ⟨p, hp⟩, fun ⟨q, hq⟩ => ⟨⟨q⟩, hq⟩⟩

/-- The function version of `monomial`. Use `monomial` instead of this one. -/
irreducible_def monomial_fun (n : ℕ) (a : R) : Polynomial R :=
  ⟨Finsupp.single n a⟩

private irreducible_def add : Polynomial R → Polynomial R → Polynomial R
| ⟨a⟩, ⟨b⟩ => ⟨a+b⟩

private irreducible_def neg {R : Type u} [Ringₓ R] : Polynomial R → Polynomial R
| ⟨a⟩ => ⟨-a⟩

private irreducible_def mul : Polynomial R → Polynomial R → Polynomial R
| ⟨a⟩, ⟨b⟩ => ⟨a*b⟩

instance : HasZero (Polynomial R) :=
  ⟨⟨0⟩⟩

instance : HasOne (Polynomial R) :=
  ⟨monomial_fun 0 (1 : R)⟩

instance : Add (Polynomial R) :=
  ⟨add⟩

instance {R : Type u} [Ringₓ R] : Neg (Polynomial R) :=
  ⟨neg⟩

instance : Mul (Polynomial R) :=
  ⟨mul⟩

instance {S : Type _} [Monoidₓ S] [DistribMulAction S R] : HasScalar S (Polynomial R) :=
  ⟨fun r p => ⟨r • p.to_finsupp⟩⟩

theorem zero_to_finsupp : (⟨0⟩ : Polynomial R) = 0 :=
  rfl

theorem one_to_finsupp : (⟨1⟩ : Polynomial R) = 1 :=
  by 
    change (⟨1⟩ : Polynomial R) = monomial_fun 0 (1 : R)
    rw [monomial_fun]
    rfl

theorem add_to_finsupp {a b} : (⟨a⟩+⟨b⟩ : Polynomial R) = ⟨a+b⟩ :=
  show add _ _ = _ by 
    rw [add]

theorem neg_to_finsupp {R : Type u} [Ringₓ R] {a} : (-⟨a⟩ : Polynomial R) = ⟨-a⟩ :=
  show neg _ = _ by 
    rw [neg]

theorem mul_to_finsupp {a b} : (⟨a⟩*⟨b⟩ : Polynomial R) = ⟨a*b⟩ :=
  show mul _ _ = _ by 
    rw [mul]

theorem smul_to_finsupp {S : Type _} [Monoidₓ S] [DistribMulAction S R] {a : S} {b} :
  (a • ⟨b⟩ : Polynomial R) = ⟨a • b⟩ :=
  rfl

theorem _root_.is_smul_regular.polynomial {S : Type _} [Monoidₓ S] [DistribMulAction S R] {a : S}
  (ha : IsSmulRegular R a) : IsSmulRegular (Polynomial R) a
| ⟨x⟩, ⟨y⟩, h => congr_argₓ _$ ha.finsupp (Polynomial.of_finsupp.inj h)

instance : Inhabited (Polynomial R) :=
  ⟨0⟩

instance : Semiringₓ (Polynomial R) :=
  by 
    refineStruct
        { zero := (0 : Polynomial R), one := 1, mul := ·*·, add := ·+·, nsmul := · • ·, npow := npowRec,
          npow_zero' := fun x => rfl, npow_succ' := fun n x => rfl } <;>
      ·
        repeat' 
            rintro ⟨_⟩ <;>
          simp [←zero_to_finsupp, ←one_to_finsupp, add_to_finsupp, mul_to_finsupp, mul_assocₓ, mul_addₓ, add_mulₓ,
              smul_to_finsupp, Nat.succ_eq_one_add] <;>
            abel

instance {S} [Monoidₓ S] [DistribMulAction S R] : DistribMulAction S (Polynomial R) :=
  { smul := · • ·,
    one_smul :=
      by 
        rintro ⟨⟩
        simp [smul_to_finsupp],
    mul_smul :=
      by 
        rintro _ _ ⟨⟩
        simp [smul_to_finsupp, mul_smul],
    smul_add :=
      by 
        rintro _ ⟨⟩ ⟨⟩
        simp [smul_to_finsupp, add_to_finsupp],
    smul_zero :=
      by 
        rintro _ 
        simp [←zero_to_finsupp, smul_to_finsupp] }

instance {S} [Monoidₓ S] [DistribMulAction S R] [HasFaithfulScalar S R] : HasFaithfulScalar S (Polynomial R) :=
  { eq_of_smul_eq_smul := fun s₁ s₂ h => eq_of_smul_eq_smul$ fun a : ℕ →₀ R => congr_argₓ to_finsupp (h ⟨a⟩) }

instance {S} [Semiringₓ S] [Module S R] : Module S (Polynomial R) :=
  { Polynomial.distribMulAction with smul := · • ·,
    add_smul :=
      by 
        rintro _ _ ⟨⟩
        simp [smul_to_finsupp, add_to_finsupp, add_smul],
    zero_smul :=
      by 
        rintro ⟨⟩
        simp [smul_to_finsupp, ←zero_to_finsupp] }

instance {S₁ S₂} [Monoidₓ S₁] [Monoidₓ S₂] [DistribMulAction S₁ R] [DistribMulAction S₂ R] [SmulCommClass S₁ S₂ R] :
  SmulCommClass S₁ S₂ (Polynomial R) :=
  ⟨by 
      rintro _ _ ⟨⟩
      simp [smul_to_finsupp, smul_comm]⟩

instance {S₁ S₂} [HasScalar S₁ S₂] [Monoidₓ S₁] [Monoidₓ S₂] [DistribMulAction S₁ R] [DistribMulAction S₂ R]
  [IsScalarTower S₁ S₂ R] : IsScalarTower S₁ S₂ (Polynomial R) :=
  ⟨by 
      rintro _ _ ⟨⟩
      simp [smul_to_finsupp]⟩

instance [Subsingleton R] : Unique (Polynomial R) :=
  { Polynomial.inhabited with
    uniq :=
      by 
        rintro ⟨x⟩
        change (⟨x⟩ : Polynomial R) = 0
        rw [←zero_to_finsupp]
        simp  }

variable (R)

/-- Ring isomorphism between `polynomial R` and `add_monoid_algebra R ℕ`. This is just an
implementation detail, but it can be useful to transfer results from `finsupp` to polynomials. -/
@[simps]
def to_finsupp_iso : Polynomial R ≃+* AddMonoidAlgebra R ℕ :=
  { toFun := fun p => p.to_finsupp, invFun := fun p => ⟨p⟩, left_inv := fun ⟨p⟩ => rfl, right_inv := fun p => rfl,
    map_mul' :=
      by 
        rintro ⟨⟩ ⟨⟩
        simp [mul_to_finsupp],
    map_add' :=
      by 
        rintro ⟨⟩ ⟨⟩
        simp [add_to_finsupp] }

/-- Ring isomorphism between `(polynomial R)ᵐᵒᵖ` and `polynomial Rᵐᵒᵖ`. -/
@[simps]
def op_ring_equiv : «expr ᵐᵒᵖ» (Polynomial R) ≃+* Polynomial («expr ᵐᵒᵖ» R) :=
  ((to_finsupp_iso R).op.trans AddMonoidAlgebra.opRingEquiv).trans (to_finsupp_iso _).symm

variable {R}

theorem sum_to_finsupp {ι : Type _} (s : Finset ι) (f : ι → AddMonoidAlgebra R ℕ) :
  (∑i in s, (⟨f i⟩ : Polynomial R)) = ⟨∑i in s, f i⟩ :=
  ((to_finsupp_iso R).symm.toAddMonoidHom.map_sum f s).symm

/--
The set of all `n` such that `X^n` has a non-zero coefficient.
-/
def support : Polynomial R → Finset ℕ
| ⟨p⟩ => p.support

@[simp]
theorem support_zero : (0 : Polynomial R).Support = ∅ :=
  rfl

@[simp]
theorem support_eq_empty : p.support = ∅ ↔ p = 0 :=
  by 
    rcases p with ⟨⟩
    simp [support, ←zero_to_finsupp]

theorem card_support_eq_zero : p.support.card = 0 ↔ p = 0 :=
  by 
    simp 

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (n : ℕ) : R →ₗ[R] Polynomial R :=
  { toFun := monomial_fun n,
    map_add' :=
      by 
        simp [monomial_fun, add_to_finsupp],
    map_smul' :=
      by 
        simp [monomial_fun, smul_to_finsupp] }

@[simp]
theorem monomial_zero_right (n : ℕ) : monomial n (0 : R) = 0 :=
  by 
    simp [monomial, monomial_fun]

theorem monomial_zero_one : monomial 0 (1 : R) = 1 :=
  rfl

theorem monomial_add (n : ℕ) (r s : R) : monomial n (r+s) = monomial n r+monomial n s :=
  by 
    simp [monomial, monomial_fun]

theorem monomial_mul_monomial (n m : ℕ) (r s : R) : (monomial n r*monomial m s) = monomial (n+m) (r*s) :=
  by 
    simp only [monomial, monomial_fun, LinearMap.coe_mk, mul_to_finsupp, AddMonoidAlgebra.single_mul_single]

@[simp]
theorem monomial_pow (n : ℕ) (r : R) (k : ℕ) : monomial n r ^ k = monomial (n*k) (r ^ k) :=
  by 
    induction' k with k ih
    ·
      simp [pow_zeroₓ, monomial_zero_one]
    ·
      simp [pow_succₓ, ih, monomial_mul_monomial, Nat.succ_eq_add_one, mul_addₓ, add_commₓ]

theorem smul_monomial {S} [Monoidₓ S] [DistribMulAction S R] (a : S) (n : ℕ) (b : R) :
  a • monomial n b = monomial n (a • b) :=
  by 
    simp [monomial, monomial_fun, smul_to_finsupp]

@[simp]
theorem to_finsupp_iso_monomial : (to_finsupp_iso R) (monomial n a) = single n a :=
  by 
    simp [to_finsupp_iso, monomial, monomial_fun]

@[simp]
theorem to_finsupp_iso_symm_single : (to_finsupp_iso R).symm (single n a) = monomial n a :=
  by 
    simp [to_finsupp_iso, monomial, monomial_fun]

theorem monomial_injective (n : ℕ) : Function.Injective (monomial n : R → Polynomial R) :=
  by 
    convert (to_finsupp_iso R).symm.Injective.comp (single_injective n)
    ext 
    simp 

@[simp]
theorem monomial_eq_zero_iff (t : R) (n : ℕ) : monomial n t = 0 ↔ t = 0 :=
  LinearMap.map_eq_zero_iff _ (Polynomial.monomial_injective n)

theorem support_add : (p+q).Support ⊆ p.support ∪ q.support :=
  by 
    rcases p with ⟨⟩
    rcases q with ⟨⟩
    simp only [add_to_finsupp, support]
    exact support_add

/--
`C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
def C : R →+* Polynomial R :=
  { monomial 0 with
    map_one' :=
      by 
        simp [monomial_zero_one],
    map_mul' :=
      by 
        simp [monomial_mul_monomial],
    map_zero' :=
      by 
        simp  }

@[simp]
theorem monomial_zero_left (a : R) : monomial 0 a = C a :=
  rfl

theorem C_0 : C (0 : R) = 0 :=
  by 
    simp 

theorem C_1 : C (1 : R) = 1 :=
  rfl

theorem C_mul : C (a*b) = C a*C b :=
  C.map_mul a b

theorem C_add : C (a+b) = C a+C b :=
  C.map_add a b

@[simp]
theorem smul_C {S} [Monoidₓ S] [DistribMulAction S R] (s : S) (r : R) : s • C r = C (s • r) :=
  smul_monomial _ _ r

@[simp]
theorem C_bit0 : C (bit0 a) = bit0 (C a) :=
  C_add

@[simp]
theorem C_bit1 : C (bit1 a) = bit1 (C a) :=
  by 
    simp [bit1, C_bit0]

theorem C_pow : C (a ^ n) = C a ^ n :=
  C.map_pow a n

@[simp]
theorem C_eq_nat_cast (n : ℕ) : C (n : R) = (n : Polynomial R) :=
  C.map_nat_cast n

@[simp]
theorem C_mul_monomial : (C a*monomial n b) = monomial n (a*b) :=
  by 
    simp only [←monomial_zero_left, monomial_mul_monomial, zero_addₓ]

@[simp]
theorem monomial_mul_C : (monomial n a*C b) = monomial n (a*b) :=
  by 
    simp only [←monomial_zero_left, monomial_mul_monomial, add_zeroₓ]

/-- `X` is the polynomial variable (aka indeterminate). -/
def X : Polynomial R :=
  monomial 1 1

theorem monomial_one_one_eq_X : monomial 1 (1 : R) = X :=
  rfl

theorem monomial_one_right_eq_X_pow (n : ℕ) : monomial n (1 : R) = X ^ n :=
  by 
    induction' n with n ih
    ·
      simp [monomial_zero_one]
    ·
      rw [pow_succₓ, ←ih, ←monomial_one_one_eq_X, monomial_mul_monomial, add_commₓ, one_mulₓ]

/-- `X` commutes with everything, even when the coefficients are noncommutative. -/
theorem X_mul : (X*p) = p*X :=
  by 
    rcases p with ⟨⟩
    simp only [X, monomial, monomial_fun, mul_to_finsupp, LinearMap.coe_mk]
    ext 
    simp [AddMonoidAlgebra.mul_apply, sum_single_index, add_commₓ]

theorem X_pow_mul {n : ℕ} : ((X ^ n)*p) = p*X ^ n :=
  by 
    induction' n with n ih
    ·
      simp 
    ·
      convLHS => rw [pow_succ'ₓ]
      rw [mul_assocₓ, X_mul, ←mul_assocₓ, ih, mul_assocₓ, ←pow_succ'ₓ]

theorem X_pow_mul_assoc {n : ℕ} : ((p*X ^ n)*q) = (p*q)*X ^ n :=
  by 
    rw [mul_assocₓ, X_pow_mul, ←mul_assocₓ]

theorem commute_X (p : Polynomial R) : Commute X p :=
  X_mul

@[simp]
theorem monomial_mul_X (n : ℕ) (r : R) : (monomial n r*X) = monomial (n+1) r :=
  by 
    erw [monomial_mul_monomial, mul_oneₓ]

@[simp]
theorem monomial_mul_X_pow (n : ℕ) (r : R) (k : ℕ) : (monomial n r*X ^ k) = monomial (n+k) r :=
  by 
    induction' k with k ih
    ·
      simp 
    ·
      simp [ih, pow_succ'ₓ, ←mul_assocₓ, add_assocₓ]

@[simp]
theorem X_mul_monomial (n : ℕ) (r : R) : (X*monomial n r) = monomial (n+1) r :=
  by 
    rw [X_mul, monomial_mul_X]

@[simp]
theorem X_pow_mul_monomial (k n : ℕ) (r : R) : ((X ^ k)*monomial n r) = monomial (n+k) r :=
  by 
    rw [X_pow_mul, monomial_mul_X_pow]

/-- `coeff p n` (often denoted `p.coeff n`) is the coefficient of `X^n` in `p`. -/
def coeff : Polynomial R → ℕ → R
| ⟨p⟩, n => p n

theorem coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 :=
  by 
    simp only [monomial, monomial_fun, coeff, LinearMap.coe_mk]
    rw [Finsupp.single_apply]

@[simp]
theorem coeff_zero (n : ℕ) : coeff (0 : Polynomial R) n = 0 :=
  rfl

@[simp]
theorem coeff_one_zero : coeff (1 : Polynomial R) 0 = 1 :=
  by 
    rw [←monomial_zero_one, coeff_monomial]
    simp 

@[simp]
theorem coeff_X_one : coeff (X : Polynomial R) 1 = 1 :=
  coeff_monomial

@[simp]
theorem coeff_X_zero : coeff (X : Polynomial R) 0 = 0 :=
  coeff_monomial

@[simp]
theorem coeff_monomial_succ : coeff (monomial (n+1) a) 0 = 0 :=
  by 
    simp [coeff_monomial]

theorem coeff_X : coeff (X : Polynomial R) n = if 1 = n then 1 else 0 :=
  coeff_monomial

theorem coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : coeff (X : Polynomial R) n = 0 :=
  by 
    rw [coeff_X, if_neg hn.symm]

@[simp]
theorem mem_support_iff : n ∈ p.support ↔ p.coeff n ≠ 0 :=
  by 
    rcases p with ⟨⟩
    simp [support, coeff]

theorem not_mem_support_iff : n ∉ p.support ↔ p.coeff n = 0 :=
  by 
    simp 

theorem coeff_C : coeff (C a) n = ite (n = 0) a 0 :=
  by 
    convert coeff_monomial using 2
    simp [eq_comm]

@[simp]
theorem coeff_C_zero : coeff (C a) 0 = a :=
  coeff_monomial

theorem coeff_C_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 :=
  by 
    rw [coeff_C, if_neg h]

theorem nontrivial.of_polynomial_ne (h : p ≠ q) : Nontrivial R :=
  ⟨⟨0, 1,
      fun h01 : 0 = 1 =>
        h$
          by 
            rw [←mul_oneₓ p, ←mul_oneₓ q, ←C_1, ←h01, C_0, mul_zero, mul_zero]⟩⟩

theorem monomial_eq_C_mul_X : ∀ {n}, monomial n a = C a*X ^ n
| 0 => (mul_oneₓ _).symm
| n+1 =>
  calc monomial (n+1) a = monomial n a*X :=
    by 
      rw [X, monomial_mul_monomial, mul_oneₓ]
    _ = (C a*X ^ n)*X :=
    by 
      rw [monomial_eq_C_mul_X]
    _ = C a*X ^ n+1 :=
    by 
      simp only [pow_addₓ, mul_assocₓ, pow_oneₓ]
    

@[simp]
theorem C_inj : C a = C b ↔ a = b :=
  ⟨fun h => coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_argₓ C⟩

@[simp]
theorem C_eq_zero : C a = 0 ↔ a = 0 :=
  calc C a = 0 ↔ C a = C 0 :=
    by 
      rw [C_0]
    _ ↔ a = 0 := C_inj
    

theorem ext_iff {p q : Polynomial R} : p = q ↔ ∀ n, coeff p n = coeff q n :=
  by 
    rcases p with ⟨⟩
    rcases q with ⟨⟩
    simp [coeff, Finsupp.ext_iff]

@[ext]
theorem ext {p q : Polynomial R} : (∀ n, coeff p n = coeff q n) → p = q :=
  ext_iff.2

-- error in Data.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem add_hom_ext
{M : Type*}
[add_monoid M]
{f g : «expr →+ »(polynomial R, M)}
(h : ∀ n a, «expr = »(f (monomial n a), g (monomial n a))) : «expr = »(f, g) :=
begin
  set [] [ident f'] [":", expr «expr →+ »(add_monoid_algebra R exprℕ(), M)] [":="] [expr f.comp (to_finsupp_iso R).symm] ["with", ident hf'],
  set [] [ident g'] [":", expr «expr →+ »(add_monoid_algebra R exprℕ(), M)] [":="] [expr g.comp (to_finsupp_iso R).symm] ["with", ident hg'],
  have [] [":", expr ∀
   n
   a, «expr = »(f' (single n a), g' (single n a))] [":=", expr λ
   n, by simp [] [] [] ["[", expr hf', ",", expr hg', ",", expr h n, "]"] [] []],
  have [ident A] [":", expr «expr = »(f', g')] [":=", expr finsupp.add_hom_ext this],
  have [ident B] [":", expr «expr = »(f, f'.comp (to_finsupp_iso R))] [],
  by { rw ["[", expr hf', ",", expr add_monoid_hom.comp_assoc, "]"] [],
    ext [] [ident x] [],
    simp [] [] ["only"] ["[", expr ring_equiv.symm_apply_apply, ",", expr add_monoid_hom.coe_comp, ",", expr function.comp_app, ",", expr ring_hom.coe_add_monoid_hom, ",", expr ring_equiv.coe_to_ring_hom, ",", expr coe_coe, "]"] [] [] },
  have [ident C] [":", expr «expr = »(g, g'.comp (to_finsupp_iso R))] [],
  by { rw ["[", expr hg', ",", expr add_monoid_hom.comp_assoc, "]"] [],
    ext [] [ident x] [],
    simp [] [] ["only"] ["[", expr ring_equiv.symm_apply_apply, ",", expr add_monoid_hom.coe_comp, ",", expr function.comp_app, ",", expr ring_hom.coe_add_monoid_hom, ",", expr ring_equiv.coe_to_ring_hom, ",", expr coe_coe, "]"] [] [] },
  rw ["[", expr B, ",", expr C, ",", expr A, "]"] []
end

@[ext]
theorem add_hom_ext' {M : Type _} [AddMonoidₓ M] {f g : Polynomial R →+ M}
  (h : ∀ n, f.comp (monomial n).toAddMonoidHom = g.comp (monomial n).toAddMonoidHom) : f = g :=
  add_hom_ext fun n => AddMonoidHom.congr_fun (h n)

@[ext]
theorem lhom_ext' {M : Type _} [AddCommMonoidₓ M] [Module R M] {f g : Polynomial R →ₗ[R] M}
  (h : ∀ n, f.comp (monomial n) = g.comp (monomial n)) : f = g :=
  LinearMap.to_add_monoid_hom_injective$ add_hom_ext$ fun n => LinearMap.congr_fun (h n)

theorem eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : Polynomial R) : p = 0 :=
  by 
    rw [←one_smul R p, ←h, zero_smul]

theorem support_monomial n (a : R) (H : a ≠ 0) : (monomial n a).Support = singleton n :=
  by 
    simp [monomial, monomial_fun, support, Finsupp.support_single_ne_zero H]

theorem support_monomial' n (a : R) : (monomial n a).Support ⊆ singleton n :=
  by 
    simp [monomial, monomial_fun, support, Finsupp.support_single_subset]

theorem X_pow_eq_monomial n : X ^ n = monomial n (1 : R) :=
  by 
    induction' n with n hn
    ·
      rw [pow_zeroₓ, monomial_zero_one]
    ·
      rw [pow_succ'ₓ, hn, X, monomial_mul_monomial, one_mulₓ]

theorem monomial_eq_smul_X {n} : monomial n (a : R) = a • X ^ n :=
  calc monomial n a = monomial n (a*1) :=
    by 
      simp 
    _ = a • monomial n 1 :=
    by 
      simp [monomial, monomial_fun, smul_to_finsupp]
    _ = a • X ^ n :=
    by 
      rw [X_pow_eq_monomial]
    

theorem support_X_pow (H : ¬(1 : R) = 0) (n : ℕ) : (X ^ n : Polynomial R).Support = singleton n :=
  by 
    convert support_monomial n 1 H 
    exact X_pow_eq_monomial n

theorem support_X_empty (H : (1 : R) = 0) : (X : Polynomial R).Support = ∅ :=
  by 
    rw [X, H, monomial_zero_right, support_zero]

theorem support_X (H : ¬(1 : R) = 0) : (X : Polynomial R).Support = singleton 1 :=
  by 
    rw [←pow_oneₓ X, support_X_pow H 1]

theorem monomial_left_inj {R : Type _} [Semiringₓ R] {a : R} (ha : a ≠ 0) {i j : ℕ} :
  monomial i a = monomial j a ↔ i = j :=
  by 
    simp [monomial, monomial_fun, Finsupp.single_left_inj ha]

theorem nat_cast_mul {R : Type _} [Semiringₓ R] (n : ℕ) (p : Polynomial R) : ((n : Polynomial R)*p) = n • p :=
  (nsmul_eq_mul _ _).symm

/-- Summing the values of a function applied to the coefficients of a polynomial -/
def Sum {S : Type _} [AddCommMonoidₓ S] (p : Polynomial R) (f : ℕ → R → S) : S :=
  ∑n in p.support, f n (p.coeff n)

theorem sum_def {S : Type _} [AddCommMonoidₓ S] (p : Polynomial R) (f : ℕ → R → S) :
  p.sum f = ∑n in p.support, f n (p.coeff n) :=
  rfl

theorem sum_eq_of_subset {S : Type _} [AddCommMonoidₓ S] (p : Polynomial R) (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0)
  (s : Finset ℕ) (hs : p.support ⊆ s) : p.sum f = ∑n in s, f n (p.coeff n) :=
  by 
    apply Finset.sum_subset hs fun n hn h'n => _ 
    rw [not_mem_support_iff] at h'n 
    simp [h'n, hf]

/-- Expressing the product of two polynomials as a double sum. -/
theorem mul_eq_sum_sum : (p*q) = ∑i in p.support, q.sum fun j a => (monomial (i+j)) (p.coeff i*a) :=
  by 
    rcases p with ⟨⟩
    rcases q with ⟨⟩
    simp [mul_to_finsupp, support, monomial, Sum, monomial_fun, coeff, sum_to_finsupp]
    rfl

@[simp]
theorem sum_zero_index {S : Type _} [AddCommMonoidₓ S] (f : ℕ → R → S) : (0 : Polynomial R).Sum f = 0 :=
  by 
    simp [Sum]

@[simp]
theorem sum_monomial_index {S : Type _} [AddCommMonoidₓ S] (n : ℕ) (a : R) (f : ℕ → R → S) (hf : f n 0 = 0) :
  (monomial n a : Polynomial R).Sum f = f n a :=
  by 
    byCases' h : a = 0
    ·
      simp [h, hf]
    ·
      simp [Sum, support_monomial, h, coeff_monomial]

@[simp]
theorem sum_C_index {a} {β} [AddCommMonoidₓ β] {f : ℕ → R → β} (h : f 0 0 = 0) : (C a).Sum f = f 0 a :=
  sum_monomial_index 0 a f h

@[simp]
theorem sum_X_index {S : Type _} [AddCommMonoidₓ S] {f : ℕ → R → S} (hf : f 1 0 = 0) :
  (X : Polynomial R).Sum f = f 1 1 :=
  sum_monomial_index 1 1 f hf

theorem sum_add_index {S : Type _} [AddCommMonoidₓ S] (p q : Polynomial R) (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0)
  (h_add : ∀ a b₁ b₂, f a (b₁+b₂) = f a b₁+f a b₂) : (p+q).Sum f = p.sum f+q.sum f :=
  by 
    rcases p with ⟨⟩
    rcases q with ⟨⟩
    simp only [add_to_finsupp, Sum, support, coeff, Pi.add_apply, coe_add]
    exact Finsupp.sum_add_index hf h_add

theorem sum_add' {S : Type _} [AddCommMonoidₓ S] (p : Polynomial R) (f g : ℕ → R → S) : p.sum (f+g) = p.sum f+p.sum g :=
  by 
    simp [sum_def, Finset.sum_add_distrib]

theorem sum_add {S : Type _} [AddCommMonoidₓ S] (p : Polynomial R) (f g : ℕ → R → S) :
  (p.sum fun n x => f n x+g n x) = p.sum f+p.sum g :=
  sum_add' _ _ _

theorem sum_smul_index {S : Type _} [AddCommMonoidₓ S] (p : Polynomial R) (b : R) (f : ℕ → R → S)
  (hf : ∀ i, f i 0 = 0) : (b • p).Sum f = p.sum fun n a => f n (b*a) :=
  by 
    rcases p with ⟨⟩
    simp [smul_to_finsupp, Sum, support, coeff]
    exact Finsupp.sum_smul_index hf

/-- `erase p n` is the polynomial `p` in which the `X^n` term has been erased. -/
irreducible_def erase (n : ℕ) : Polynomial R → Polynomial R
| ⟨p⟩ => ⟨p.erase n⟩

@[simp]
theorem support_erase (p : Polynomial R) (n : ℕ) : support (p.erase n) = (support p).erase n :=
  by 
    rcases p with ⟨⟩
    simp only [support, erase, support_erase]
    congr

theorem monomial_add_erase (p : Polynomial R) (n : ℕ) : (monomial n (coeff p n)+p.erase n) = p :=
  by 
    rcases p with ⟨⟩
    simp [add_to_finsupp, monomial, monomial_fun, coeff, erase]
    exact Finsupp.single_add_erase _ _

theorem coeff_erase (p : Polynomial R) (n i : ℕ) : (p.erase n).coeff i = if i = n then 0 else p.coeff i :=
  by 
    rcases p with ⟨⟩
    simp only [erase, coeff]
    convert rfl

@[simp]
theorem erase_zero (n : ℕ) : (0 : Polynomial R).erase n = 0 :=
  by 
    simp [←zero_to_finsupp, erase]

@[simp]
theorem erase_monomial {n : ℕ} {a : R} : erase n (monomial n a) = 0 :=
  by 
    simp [monomial, monomial_fun, erase, ←zero_to_finsupp]

@[simp]
theorem erase_same (p : Polynomial R) (n : ℕ) : coeff (p.erase n) n = 0 :=
  by 
    simp [coeff_erase]

@[simp]
theorem erase_ne (p : Polynomial R) (n i : ℕ) (h : i ≠ n) : coeff (p.erase n) i = coeff p i :=
  by 
    simp [coeff_erase, h]

section Update

/-- Replace the coefficient of a `p : polynomial p` at a given degree `n : ℕ`
by a given value `a : R`. If `a = 0`, this is equal to `p.erase n`
If `p.nat_degree < n` and `a ≠ 0`, this increases the degree to `n`.  -/
def update (p : Polynomial R) (n : ℕ) (a : R) : Polynomial R :=
  Polynomial.of_finsupp (p.to_finsupp.update n a)

theorem coeff_update (p : Polynomial R) (n : ℕ) (a : R) : (p.update n a).coeff = Function.update p.coeff n a :=
  by 
    ext 
    cases p 
    simp only [coeff, update, Function.update_apply, coe_update]
    congr

theorem coeff_update_apply (p : Polynomial R) (n : ℕ) (a : R) (i : ℕ) :
  (p.update n a).coeff i = if i = n then a else p.coeff i :=
  by 
    rw [coeff_update, Function.update_apply]

@[simp]
theorem coeff_update_same (p : Polynomial R) (n : ℕ) (a : R) : (p.update n a).coeff n = a :=
  by 
    rw [p.coeff_update_apply, if_pos rfl]

theorem coeff_update_ne (p : Polynomial R) {n : ℕ} (a : R) {i : ℕ} (h : i ≠ n) : (p.update n a).coeff i = p.coeff i :=
  by 
    rw [p.coeff_update_apply, if_neg h]

@[simp]
theorem update_zero_eq_erase (p : Polynomial R) (n : ℕ) : p.update n 0 = p.erase n :=
  by 
    ext 
    rw [coeff_update_apply, coeff_erase]

theorem support_update (p : Polynomial R) (n : ℕ) (a : R) [Decidable (a = 0)] :
  support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support :=
  by 
    cases p 
    simp only [support, update, support_update]
    congr

theorem support_update_zero (p : Polynomial R) (n : ℕ) : support (p.update n 0) = p.support.erase n :=
  by 
    rw [update_zero_eq_erase, support_erase]

theorem support_update_ne_zero (p : Polynomial R) (n : ℕ) {a : R} (ha : a ≠ 0) :
  support (p.update n a) = insert n p.support :=
  by 
    classical <;> rw [support_update, if_neg ha]

end Update

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R]

instance : CommSemiringₓ (Polynomial R) :=
  { Polynomial.semiring with
    mul_comm :=
      by 
        rintro ⟨⟩ ⟨⟩
        simp [mul_to_finsupp, mul_commₓ] }

end CommSemiringₓ

section Ringₓ

variable [Ringₓ R]

instance : Ringₓ (Polynomial R) :=
  { Polynomial.semiring with neg := Neg.neg,
    add_left_neg :=
      by 
        rintro ⟨⟩
        simp [neg_to_finsupp, add_to_finsupp, ←zero_to_finsupp],
    zsmul := · • ·,
    zsmul_zero' :=
      by 
        rintro ⟨⟩
        simp [smul_to_finsupp, ←zero_to_finsupp],
    zsmul_succ' :=
      by 
        rintro n ⟨⟩
        simp [smul_to_finsupp, add_to_finsupp, add_smul, add_commₓ],
    zsmul_neg' :=
      by 
        rintro n ⟨⟩
        simp only [smul_to_finsupp, neg_to_finsupp]
        simp [add_smul, add_mulₓ] }

@[simp]
theorem coeff_neg (p : Polynomial R) (n : ℕ) : coeff (-p) n = -coeff p n :=
  by 
    rcases p with ⟨⟩
    simp [coeff, neg_to_finsupp]

@[simp]
theorem coeff_sub (p q : Polynomial R) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n :=
  by 
    rcases p with ⟨⟩
    rcases q with ⟨⟩
    simp [coeff, sub_eq_add_neg, add_to_finsupp, neg_to_finsupp]

@[simp]
theorem monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -monomial n a :=
  by 
    rw [eq_neg_iff_add_eq_zero, ←monomial_add, neg_add_selfₓ, monomial_zero_right]

@[simp]
theorem support_neg {p : Polynomial R} : (-p).Support = p.support :=
  by 
    rcases p with ⟨⟩
    simp [support, neg_to_finsupp]

end Ringₓ

instance [CommRingₓ R] : CommRingₓ (Polynomial R) :=
  { Polynomial.commSemiring, Polynomial.ring with  }

section NonzeroSemiring

variable [Semiringₓ R] [Nontrivial R]

-- error in Data.Polynomial.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : nontrivial (polynomial R) :=
begin
  have [ident h] [":", expr nontrivial (add_monoid_algebra R exprℕ())] [":=", expr by apply_instance],
  rcases [expr h.exists_pair_ne, "with", "⟨", ident x, ",", ident y, ",", ident hxy, "⟩"],
  refine [expr ⟨⟨⟨x⟩, ⟨y⟩, _⟩⟩],
  simp [] [] [] ["[", expr hxy, "]"] [] []
end

theorem X_ne_zero : (X : Polynomial R) ≠ 0 :=
  mt (congr_argₓ fun p => coeff p 1)
    (by 
      simp )

end NonzeroSemiring

section reprₓ

variable [Semiringₓ R]

open_locale Classical

instance [HasRepr R] : HasRepr (Polynomial R) :=
  ⟨fun p =>
      if p = 0 then "0" else
        (p.support.sort (· ≤ ·)).foldr
          (fun n a =>
            (a ++ if a = "" then "" else " + ") ++
              if n = 0 then "C (" ++ reprₓ (coeff p n) ++ ")" else
                if n = 1 then if coeff p n = 1 then "X" else "C (" ++ reprₓ (coeff p n) ++ ") * X" else
                  if coeff p n = 1 then "X ^ " ++ reprₓ n else "C (" ++ reprₓ (coeff p n) ++ ") * X ^ " ++ reprₓ n)
          ""⟩

end reprₓ

end Polynomial

