import Mathbin.Data.Polynomial.Degree.Definitions

/-!
# Theory of univariate polynomials

The main defs here are `eval₂`, `eval`, and `map`.
We give several lemmas about their interaction with each other and with module operations.
-/


noncomputable theory

open Finset AddMonoidAlgebra

open_locale BigOperators

namespace Polynomial

universe u v w y

variable{R : Type u}{S : Type v}{T : Type w}{ι : Type y}{a b : R}{m n : ℕ}

section Semiringₓ

variable[Semiringₓ R]{p q r : Polynomial R}

section 

variable[Semiringₓ S]

variable(f : R →+* S)(x : S)

/-- Evaluate a polynomial `p` given a ring hom `f` from the scalar ring
  to the target and a value `x` for the variable in the target -/
def eval₂ (p : Polynomial R) : S :=
  p.sum fun e a => f a*x ^ e

theorem eval₂_eq_sum {f : R →+* S} {x : S} : p.eval₂ f x = p.sum fun e a => f a*x ^ e :=
  rfl

theorem eval₂_congr {R S : Type _} [Semiringₓ R] [Semiringₓ S] {f g : R →+* S} {s t : S} {φ ψ : Polynomial R} :
  f = g → s = t → φ = ψ → eval₂ f s φ = eval₂ g t ψ :=
  by 
    rintro rfl rfl rfl <;> rfl

-- error in Data.Polynomial.Eval: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem eval₂_at_zero : «expr = »(p.eval₂ f 0, f (coeff p 0)) :=
by simp [] [] ["only"] ["[", expr eval₂_eq_sum, ",", expr zero_pow_eq, ",", expr mul_ite, ",", expr mul_zero, ",", expr mul_one, ",", expr sum, ",", expr not_not, ",", expr mem_support_iff, ",", expr sum_ite_eq', ",", expr ite_eq_left_iff, ",", expr ring_hom.map_zero, ",", expr implies_true_iff, ",", expr eq_self_iff_true, "]"] [] [] { contextual := tt }

@[simp]
theorem eval₂_zero : (0 : Polynomial R).eval₂ f x = 0 :=
  by 
    simp [eval₂_eq_sum]

@[simp]
theorem eval₂_C : (C a).eval₂ f x = f a :=
  by 
    simp [eval₂_eq_sum]

@[simp]
theorem eval₂_X : X.eval₂ f x = x :=
  by 
    simp [eval₂_eq_sum]

@[simp]
theorem eval₂_monomial {n : ℕ} {r : R} : (monomial n r).eval₂ f x = f r*x ^ n :=
  by 
    simp [eval₂_eq_sum]

@[simp]
theorem eval₂_X_pow {n : ℕ} : (X ^ n).eval₂ f x = x ^ n :=
  by 
    rw [X_pow_eq_monomial]
    convert eval₂_monomial f x 
    simp 

@[simp]
theorem eval₂_add : (p+q).eval₂ f x = p.eval₂ f x+q.eval₂ f x :=
  by 
    apply sum_add_index <;> simp [add_mulₓ]

@[simp]
theorem eval₂_one : (1 : Polynomial R).eval₂ f x = 1 :=
  by 
    rw [←C_1, eval₂_C, f.map_one]

@[simp]
theorem eval₂_bit0 : (bit0 p).eval₂ f x = bit0 (p.eval₂ f x) :=
  by 
    rw [bit0, eval₂_add, bit0]

@[simp]
theorem eval₂_bit1 : (bit1 p).eval₂ f x = bit1 (p.eval₂ f x) :=
  by 
    rw [bit1, eval₂_add, eval₂_bit0, eval₂_one, bit1]

@[simp]
theorem eval₂_smul (g : R →+* S) (p : Polynomial R) (x : S) {s : R} : eval₂ g x (s • p) = g s*eval₂ g x p :=
  by 
    have A : p.nat_degree < p.nat_degree.succ := Nat.lt_succ_selfₓ _ 
    have B : (s • p).natDegree < p.nat_degree.succ := (nat_degree_smul_le _ _).trans_lt A 
    rw [eval₂_eq_sum, eval₂_eq_sum, sum_over_range' _ _ _ A, sum_over_range' _ _ _ B] <;> simp [mul_sum, mul_assocₓ]

@[simp]
theorem eval₂_C_X : eval₂ C X p = p :=
  Polynomial.induction_on' p
    (fun p q hp hq =>
      by 
        simp [hp, hq])
    fun n x =>
      by 
        rw [eval₂_monomial, monomial_eq_smul_X, C_mul']

/-- `eval₂_add_monoid_hom (f : R →+* S) (x : S)` is the `add_monoid_hom` from
`polynomial R` to `S` obtained by evaluating the pushforward of `p` along `f` at `x`. -/
@[simps]
def eval₂_add_monoid_hom : Polynomial R →+ S :=
  { toFun := eval₂ f x, map_zero' := eval₂_zero _ _, map_add' := fun _ _ => eval₂_add _ _ }

@[simp]
theorem eval₂_nat_cast (n : ℕ) : (n : Polynomial R).eval₂ f x = n :=
  by 
    induction' n with n ih
    ·
      simp only [eval₂_zero, Nat.cast_zero]
    ·
      rw [n.cast_succ, eval₂_add, ih, eval₂_one, n.cast_succ]

variable[Semiringₓ T]

theorem eval₂_sum (p : Polynomial T) (g : ℕ → T → Polynomial R) (x : S) :
  (p.sum g).eval₂ f x = p.sum fun n a => (g n a).eval₂ f x :=
  by 
    let T : Polynomial R →+ S :=
      { toFun := eval₂ f x, map_zero' := eval₂_zero _ _, map_add' := fun p q => eval₂_add _ _ }
    have A : ∀ y, eval₂ f x y = T y := fun y => rfl 
    simp only [A]
    rw [Sum, T.map_sum, Sum]

theorem eval₂_finset_sum (s : Finset ι) (g : ι → Polynomial R) (x : S) :
  (∑i in s, g i).eval₂ f x = ∑i in s, (g i).eval₂ f x :=
  by 
    classical 
    induction' s using Finset.induction with p hp s hs 
    simp 
    rw [sum_insert, eval₂_add, hs, sum_insert] <;> assumption

theorem eval₂_to_finsupp_eq_lift_nc {f : R →+* S} {x : S} {p : AddMonoidAlgebra R ℕ} :
  eval₂ f x (⟨p⟩ : Polynomial R) = lift_nc («expr↑ » f) (powersHom S x) p :=
  by 
    simp only [eval₂_eq_sum, Sum, sum_to_finsupp, support, coeff]
    rfl

theorem eval₂_mul_noncomm (hf : ∀ k, Commute (f$ q.coeff k) x) : eval₂ f x (p*q) = eval₂ f x p*eval₂ f x q :=
  by 
    rcases p with ⟨⟩
    rcases q with ⟨⟩
    simp only [coeff] at hf 
    simp only [mul_to_finsupp, eval₂_to_finsupp_eq_lift_nc]
    exact lift_nc_mul _ _ p q fun k n hn => (hf k).pow_right n

@[simp]
theorem eval₂_mul_X : eval₂ f x (p*X) = eval₂ f x p*x :=
  by 
    refine'
      trans (eval₂_mul_noncomm _ _$ fun k => _)
        (by 
          rw [eval₂_X])
    rcases em (k = 1) with (rfl | hk)
    ·
      simp 
    ·
      simp [coeff_X_of_ne_one hk]

@[simp]
theorem eval₂_X_mul : eval₂ f x (X*p) = eval₂ f x p*x :=
  by 
    rw [X_mul, eval₂_mul_X]

theorem eval₂_mul_C' (h : Commute (f a) x) : eval₂ f x (p*C a) = eval₂ f x p*f a :=
  by 
    rw [eval₂_mul_noncomm, eval₂_C]
    intro k 
    byCases' hk : k = 0
    ·
      simp only [hk, h, coeff_C_zero, coeff_C_ne_zero]
    ·
      simp only [coeff_C_ne_zero hk, RingHom.map_zero, Commute.zero_left]

theorem eval₂_list_prod_noncomm (ps : List (Polynomial R)) (hf : ∀ p _ : p ∈ ps k, Commute (f$ coeff p k) x) :
  eval₂ f x ps.prod = (ps.map (Polynomial.eval₂ f x)).Prod :=
  by 
    induction' ps using List.reverseRecOn with ps p ihp
    ·
      simp 
    ·
      simp only [List.forall_mem_appendₓ, List.forall_mem_singleton] at hf 
      simp [eval₂_mul_noncomm _ _ hf.2, ihp hf.1]

/-- `eval₂` as a `ring_hom` for noncommutative rings -/
def eval₂_ring_hom' (f : R →+* S) (x : S) (hf : ∀ a, Commute (f a) x) : Polynomial R →+* S :=
  { toFun := eval₂ f x, map_add' := fun _ _ => eval₂_add _ _, map_zero' := eval₂_zero _ _,
    map_mul' := fun p q => eval₂_mul_noncomm f x fun k => hf$ coeff q k, map_one' := eval₂_one _ _ }

end 

/-!
We next prove that eval₂ is multiplicative
as long as target ring is commutative
(even if the source ring is not).
-/


section Eval₂

variable[CommSemiringₓ S]

variable(f : R →+* S)(x : S)

@[simp]
theorem eval₂_mul : (p*q).eval₂ f x = p.eval₂ f x*q.eval₂ f x :=
  eval₂_mul_noncomm _ _$ fun k => Commute.all _ _

theorem eval₂_mul_eq_zero_of_left (q : Polynomial R) (hp : p.eval₂ f x = 0) : (p*q).eval₂ f x = 0 :=
  by 
    rw [eval₂_mul f x]
    exact mul_eq_zero_of_left hp (q.eval₂ f x)

theorem eval₂_mul_eq_zero_of_right (p : Polynomial R) (hq : q.eval₂ f x = 0) : (p*q).eval₂ f x = 0 :=
  by 
    rw [eval₂_mul f x]
    exact mul_eq_zero_of_right (p.eval₂ f x) hq

/-- `eval₂` as a `ring_hom` -/
def eval₂_ring_hom (f : R →+* S) (x : S) : Polynomial R →+* S :=
  { eval₂_add_monoid_hom f x with map_one' := eval₂_one _ _, map_mul' := fun _ _ => eval₂_mul _ _ }

@[simp]
theorem coe_eval₂_ring_hom (f : R →+* S) x : «expr⇑ » (eval₂_ring_hom f x) = eval₂ f x :=
  rfl

theorem eval₂_pow (n : ℕ) : (p ^ n).eval₂ f x = p.eval₂ f x ^ n :=
  (eval₂_ring_hom _ _).map_pow _ _

theorem eval₂_eq_sum_range : p.eval₂ f x = ∑i in Finset.range (p.nat_degree+1), f (p.coeff i)*x ^ i :=
  trans (congr_argₓ _ p.as_sum_range)
    (trans (eval₂_finset_sum f _ _ x)
      (congr_argₓ _
        (by 
          simp )))

theorem eval₂_eq_sum_range' (f : R →+* S) {p : Polynomial R} {n : ℕ} (hn : p.nat_degree < n) (x : S) :
  eval₂ f x p = ∑i in Finset.range n, f (p.coeff i)*x ^ i :=
  by 
    rw [eval₂_eq_sum, p.sum_over_range' _ _ hn]
    intro i 
    rw [f.map_zero, zero_mul]

theorem eval₂_dvd : p ∣ q → eval₂ f x p ∣ eval₂ f x q :=
  (eval₂_ring_hom f x).map_dvd

theorem eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (h : p ∣ q) (h0 : eval₂ f x p = 0) : eval₂ f x q = 0 :=
  zero_dvd_iff.mp (h0 ▸ eval₂_dvd f x h)

end Eval₂

section Eval

variable{x : R}

/-- `eval x p` is the evaluation of the polynomial `p` at `x` -/
def eval : R → Polynomial R → R :=
  eval₂ (RingHom.id _)

theorem eval_eq_sum : p.eval x = p.sum fun e a => a*x ^ e :=
  rfl

theorem eval_eq_finset_sum (p : Polynomial R) (x : R) : p.eval x = ∑i in range (p.nat_degree+1), p.coeff i*x ^ i :=
  by 
    rw [eval_eq_sum, sum_over_range]
    simp 

theorem eval_eq_finset_sum' (P : Polynomial R) :
  (fun x => eval x P) = fun x => ∑i in range (P.nat_degree+1), P.coeff i*x ^ i :=
  by 
    ext 
    exact P.eval_eq_finset_sum x

@[simp]
theorem eval₂_at_apply {S : Type _} [Semiringₓ S] (f : R →+* S) (r : R) : p.eval₂ f (f r) = f (p.eval r) :=
  by 
    rw [eval₂_eq_sum, eval_eq_sum, Sum, Sum, f.map_sum]
    simp only [f.map_mul, f.map_pow]

@[simp]
theorem eval₂_at_one {S : Type _} [Semiringₓ S] (f : R →+* S) : p.eval₂ f 1 = f (p.eval 1) :=
  by 
    convert eval₂_at_apply f 1
    simp 

@[simp]
theorem eval₂_at_nat_cast {S : Type _} [Semiringₓ S] (f : R →+* S) (n : ℕ) : p.eval₂ f n = f (p.eval n) :=
  by 
    convert eval₂_at_apply f n 
    simp 

@[simp]
theorem eval_C : (C a).eval x = a :=
  eval₂_C _ _

@[simp]
theorem eval_nat_cast {n : ℕ} : (n : Polynomial R).eval x = n :=
  by 
    simp only [←C_eq_nat_cast, eval_C]

@[simp]
theorem eval_X : X.eval x = x :=
  eval₂_X _ _

@[simp]
theorem eval_monomial {n a} : (monomial n a).eval x = a*x ^ n :=
  eval₂_monomial _ _

@[simp]
theorem eval_zero : (0 : Polynomial R).eval x = 0 :=
  eval₂_zero _ _

@[simp]
theorem eval_add : (p+q).eval x = p.eval x+q.eval x :=
  eval₂_add _ _

@[simp]
theorem eval_one : (1 : Polynomial R).eval x = 1 :=
  eval₂_one _ _

@[simp]
theorem eval_bit0 : (bit0 p).eval x = bit0 (p.eval x) :=
  eval₂_bit0 _ _

@[simp]
theorem eval_bit1 : (bit1 p).eval x = bit1 (p.eval x) :=
  eval₂_bit1 _ _

@[simp]
theorem eval_smul (p : Polynomial R) (x : R) {s : R} : (s • p).eval x = s*p.eval x :=
  eval₂_smul (RingHom.id _) _ _

@[simp]
theorem eval_C_mul : (C a*p).eval x = a*p.eval x :=
  by 
    apply Polynomial.induction_on' p
    ·
      intro p q ph qh 
      simp only [mul_addₓ, eval_add, ph, qh]
    ·
      intro n b 
      simp only [mul_assocₓ, C_mul_monomial, eval_monomial]

/-- `polynomial.eval` as linear map -/
@[simps]
def leval {R : Type _} [Semiringₓ R] (r : R) : Polynomial R →ₗ[R] R :=
  { toFun := fun f => f.eval r, map_add' := fun f g => eval_add, map_smul' := fun c f => eval_smul f r }

@[simp]
theorem eval_nat_cast_mul {n : ℕ} : ((n : Polynomial R)*p).eval x = n*p.eval x :=
  by 
    rw [←C_eq_nat_cast, eval_C_mul]

@[simp]
theorem eval_mul_X : (p*X).eval x = p.eval x*x :=
  by 
    apply Polynomial.induction_on' p
    ·
      intro p q ph qh 
      simp only [add_mulₓ, eval_add, ph, qh]
    ·
      intro n a 
      simp only [←monomial_one_one_eq_X, monomial_mul_monomial, eval_monomial, mul_oneₓ, pow_succ'ₓ, mul_assocₓ]

@[simp]
theorem eval_mul_X_pow {k : ℕ} : (p*X ^ k).eval x = p.eval x*x ^ k :=
  by 
    induction' k with k ih
    ·
      simp 
    ·
      simp [pow_succ'ₓ, ←mul_assocₓ, ih]

theorem eval_sum (p : Polynomial R) (f : ℕ → R → Polynomial R) (x : R) :
  (p.sum f).eval x = p.sum fun n a => (f n a).eval x :=
  eval₂_sum _ _ _ _

theorem eval_finset_sum (s : Finset ι) (g : ι → Polynomial R) (x : R) : (∑i in s, g i).eval x = ∑i in s, (g i).eval x :=
  eval₂_finset_sum _ _ _ _

/-- `is_root p x` implies `x` is a root of `p`. The evaluation of `p` at `x` is zero -/
def is_root (p : Polynomial R) (a : R) : Prop :=
  p.eval a = 0

instance  [DecidableEq R] : Decidable (is_root p a) :=
  by 
    unfold is_root <;> infer_instance

@[simp]
theorem is_root.def : is_root p a ↔ p.eval a = 0 :=
  Iff.rfl

theorem coeff_zero_eq_eval_zero (p : Polynomial R) : coeff p 0 = p.eval 0 :=
  calc coeff p 0 = coeff p 0*0 ^ 0 :=
    by 
      simp 
    _ = p.eval 0 :=
    Eq.symm$
      Finset.sum_eq_single _
        (fun b _ hb =>
          by 
            simp [zero_pow (Nat.pos_of_ne_zeroₓ hb)])
        (by 
          simp )
    

theorem zero_is_root_of_coeff_zero_eq_zero {p : Polynomial R} (hp : p.coeff 0 = 0) : is_root p 0 :=
  by 
    rwa [coeff_zero_eq_eval_zero] at hp

end Eval

section Comp

/-- The composition of polynomials as a polynomial. -/
def comp (p q : Polynomial R) : Polynomial R :=
  p.eval₂ C q

theorem comp_eq_sum_left : p.comp q = p.sum fun e a => C a*q ^ e :=
  rfl

@[simp]
theorem comp_X : p.comp X = p :=
  by 
    simp only [comp, eval₂, ←monomial_eq_C_mul_X]
    exact sum_monomial_eq _

@[simp]
theorem X_comp : X.comp p = p :=
  eval₂_X _ _

@[simp]
theorem comp_C : p.comp (C a) = C (p.eval a) :=
  by 
    simp [comp, (C : R →+* _).map_sum]

@[simp]
theorem C_comp : (C a).comp p = C a :=
  eval₂_C _ _

@[simp]
theorem nat_cast_comp {n : ℕ} : (n : Polynomial R).comp p = n :=
  by 
    rw [←C_eq_nat_cast, C_comp]

@[simp]
theorem comp_zero : p.comp (0 : Polynomial R) = C (p.eval 0) :=
  by 
    rw [←C_0, comp_C]

@[simp]
theorem zero_comp : comp (0 : Polynomial R) p = 0 :=
  by 
    rw [←C_0, C_comp]

@[simp]
theorem comp_one : p.comp 1 = C (p.eval 1) :=
  by 
    rw [←C_1, comp_C]

@[simp]
theorem one_comp : comp (1 : Polynomial R) p = 1 :=
  by 
    rw [←C_1, C_comp]

@[simp]
theorem add_comp : (p+q).comp r = p.comp r+q.comp r :=
  eval₂_add _ _

@[simp]
theorem monomial_comp (n : ℕ) : (monomial n a).comp p = C a*p ^ n :=
  eval₂_monomial _ _

@[simp]
theorem mul_X_comp : (p*X).comp r = p.comp r*r :=
  by 
    apply Polynomial.induction_on' p
    ·
      intro p q hp hq 
      simp only [hp, hq, add_mulₓ, add_comp]
    ·
      intro n b 
      simp only [pow_succ'ₓ, mul_assocₓ, monomial_mul_X, monomial_comp]

@[simp]
theorem X_pow_comp {k : ℕ} : (X ^ k).comp p = p ^ k :=
  by 
    induction' k with k ih
    ·
      simp 
    ·
      simp [pow_succ'ₓ, mul_X_comp, ih]

@[simp]
theorem mul_X_pow_comp {k : ℕ} : (p*X ^ k).comp r = p.comp r*r ^ k :=
  by 
    induction' k with k ih
    ·
      simp 
    ·
      simp [ih, pow_succ'ₓ, ←mul_assocₓ, mul_X_comp]

@[simp]
theorem C_mul_comp : (C a*p).comp r = C a*p.comp r :=
  by 
    apply Polynomial.induction_on' p
    ·
      intro p q hp hq 
      simp [hp, hq, mul_addₓ]
    ·
      intro n b 
      simp [mul_assocₓ]

@[simp]
theorem nat_cast_mul_comp {n : ℕ} : ((n : Polynomial R)*p).comp r = n*p.comp r :=
  by 
    rw [←C_eq_nat_cast, C_mul_comp, C_eq_nat_cast]

@[simp]
theorem mul_comp {R : Type _} [CommSemiringₓ R] (p q r : Polynomial R) : (p*q).comp r = p.comp r*q.comp r :=
  eval₂_mul _ _

theorem prod_comp {R : Type _} [CommSemiringₓ R] (s : Multiset (Polynomial R)) (p : Polynomial R) :
  s.prod.comp p = (s.map fun q : Polynomial R => q.comp p).Prod :=
  (s.prod_hom (MonoidHom.mk (fun q : Polynomial R => q.comp p) one_comp fun q r => mul_comp q r p)).symm

@[simp]
theorem pow_comp {R : Type _} [CommSemiringₓ R] (p q : Polynomial R) (n : ℕ) : (p ^ n).comp q = p.comp q ^ n :=
  ((MonoidHom.mk fun r : Polynomial R => r.comp q) one_comp fun r s => mul_comp r s q).map_pow p n

@[simp]
theorem bit0_comp : comp (bit0 p : Polynomial R) q = bit0 (p.comp q) :=
  by 
    simp only [bit0, add_comp]

@[simp]
theorem bit1_comp : comp (bit1 p : Polynomial R) q = bit1 (p.comp q) :=
  by 
    simp only [bit1, add_comp, bit0_comp, one_comp]

theorem comp_assoc {R : Type _} [CommSemiringₓ R] (φ ψ χ : Polynomial R) : (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) :=
  by 
    apply Polynomial.induction_on φ <;>
      ·
        intros 
        simp_all only [add_comp, mul_comp, C_comp, X_comp, pow_succ'ₓ, ←mul_assocₓ]

end Comp

section Map

variable[Semiringₓ S]

variable(f : R →+* S)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : Polynomial R → Polynomial S :=
  eval₂ (C.comp f) X

@[simp]
theorem map_C : (C a).map f = C (f a) :=
  eval₂_C _ _

@[simp]
theorem map_X : X.map f = X :=
  eval₂_X _ _

@[simp]
theorem map_monomial {n a} : (monomial n a).map f = monomial n (f a) :=
  by 
    dsimp only [map]
    rw [eval₂_monomial, monomial_eq_C_mul_X]
    rfl

@[simp]
theorem map_zero : (0 : Polynomial R).map f = 0 :=
  eval₂_zero _ _

@[simp]
theorem map_add : (p+q).map f = p.map f+q.map f :=
  eval₂_add _ _

@[simp]
theorem map_one : (1 : Polynomial R).map f = 1 :=
  eval₂_one _ _

@[simp]
theorem map_mul : (p*q).map f = p.map f*q.map f :=
  by 
    rw [map, eval₂_mul_noncomm]
    exact fun k => (commute_X _).symm

@[simp]
theorem map_smul (r : R) : (r • p).map f = f r • p.map f :=
  by 
    rw [map, eval₂_smul, RingHom.comp_apply, C_mul']

/-- `polynomial.map` as a `ring_hom` -/
def map_ring_hom (f : R →+* S) : Polynomial R →+* Polynomial S :=
  { toFun := Polynomial.map f, map_add' := fun _ _ => map_add f, map_zero' := map_zero f,
    map_mul' := fun _ _ => map_mul f, map_one' := map_one f }

@[simp]
theorem coe_map_ring_hom (f : R →+* S) : «expr⇑ » (map_ring_hom f) = map f :=
  rfl

@[simp]
theorem map_nat_cast (n : ℕ) : (n : Polynomial R).map f = n :=
  (map_ring_hom f).map_nat_cast n

@[simp]
theorem coeff_map (n : ℕ) : coeff (p.map f) n = f (coeff p n) :=
  by 
    rw [map, eval₂, coeff_sum, Sum]
    convRHS => rw [←sum_C_mul_X_eq p, coeff_sum, Sum, RingHom.map_sum]
    refine' Finset.sum_congr rfl fun x hx => _ 
    simp [Function.comp, coeff_C_mul_X, f.map_mul]
    splitIfs <;> simp [f.map_zero]

/-- If `R` and `S` are isomorphic, then so are their polynomial rings. -/
@[simps]
def map_equiv (e : R ≃+* S) : Polynomial R ≃+* Polynomial S :=
  RingEquiv.ofHomInv (map_ring_hom e) (map_ring_hom e.symm)
    (by 
      ext <;> simp )
    (by 
      ext <;> simp )

theorem map_map [Semiringₓ T] (g : S →+* T) (p : Polynomial R) : (p.map f).map g = p.map (g.comp f) :=
  ext
    (by 
      simp [coeff_map])

@[simp]
theorem map_id : p.map (RingHom.id _) = p :=
  by 
    simp [Polynomial.ext_iff, coeff_map]

theorem eval₂_eq_eval_map {x : S} : p.eval₂ f x = (p.map f).eval x :=
  by 
    apply Polynomial.induction_on' p
    ·
      intro p q hp hq 
      simp [hp, hq]
    ·
      intro n r 
      simp 

theorem map_injective (hf : Function.Injective f) : Function.Injective (map f) :=
  fun p q h =>
    ext$
      fun m =>
        hf$
          by 
            rw [←coeff_map f, ←coeff_map f, h]

theorem map_surjective (hf : Function.Surjective f) : Function.Surjective (map f) :=
  fun p =>
    Polynomial.induction_on' p
      (fun p q hp hq =>
        let ⟨p', hp'⟩ := hp 
        let ⟨q', hq'⟩ := hq
        ⟨p'+q',
          by 
            rw [map_add f, hp', hq']⟩)
      fun n s =>
        let ⟨r, hr⟩ := hf s
        ⟨monomial n r,
          by 
            rw [map_monomial f, hr]⟩

theorem degree_map_le (p : Polynomial R) : degree (p.map f) ≤ degree p :=
  by 
    apply (degree_le_iff_coeff_zero _ _).2 fun m hm => _ 
    rw [degree_lt_iff_coeff_zero] at hm 
    simp [hm m (le_reflₓ _)]

theorem nat_degree_map_le (p : Polynomial R) : nat_degree (p.map f) ≤ nat_degree p :=
  nat_degree_le_nat_degree (degree_map_le f p)

variable{f}

theorem map_monic_eq_zero_iff (hp : p.monic) : p.map f = 0 ↔ ∀ x, f x = 0 :=
  ⟨fun hfp x =>
      calc f x = f x*f p.leading_coeff :=
        by 
          simp only [mul_oneₓ, hp.leading_coeff, f.map_one]
        _ = f x*(p.map f).coeff p.nat_degree := congr_argₓ _ (coeff_map _ _).symm 
        _ = 0 :=
        by 
          simp only [hfp, mul_zero, coeff_zero]
        ,
    fun h =>
      ext
        fun n =>
          by 
            simp only [h, coeff_map, coeff_zero]⟩

theorem map_monic_ne_zero (hp : p.monic) [Nontrivial S] : p.map f ≠ 0 :=
  fun h => f.map_one_ne_zero ((map_monic_eq_zero_iff hp).mp h _)

theorem degree_map_eq_of_leading_coeff_ne_zero (f : R →+* S) (hf : f (leading_coeff p) ≠ 0) :
  degree (p.map f) = degree p :=
  le_antisymmₓ (degree_map_le f _)$
    have hp0 : p ≠ 0 := leading_coeff_ne_zero.mp fun hp0 => hf (trans (congr_argₓ _ hp0) f.map_zero)
    by 
      rw [degree_eq_nat_degree hp0]
      refine' le_degree_of_ne_zero _ 
      rw [coeff_map]
      exact hf

theorem nat_degree_map_of_leading_coeff_ne_zero (f : R →+* S) (hf : f (leading_coeff p) ≠ 0) :
  nat_degree (p.map f) = nat_degree p :=
  nat_degree_eq_of_degree_eq (degree_map_eq_of_leading_coeff_ne_zero f hf)

theorem leading_coeff_map_of_leading_coeff_ne_zero (f : R →+* S) (hf : f (leading_coeff p) ≠ 0) :
  leading_coeff (p.map f) = f (leading_coeff p) :=
  by 
    unfold leading_coeff 
    rw [coeff_map, nat_degree_map_of_leading_coeff_ne_zero f hf]

variable(f)

@[simp]
theorem map_ring_hom_id : map_ring_hom (RingHom.id R) = RingHom.id (Polynomial R) :=
  RingHom.ext$ fun x => map_id

@[simp]
theorem map_ring_hom_comp [Semiringₓ T] (f : S →+* T) (g : R →+* S) :
  (map_ring_hom f).comp (map_ring_hom g) = map_ring_hom (f.comp g) :=
  RingHom.ext$ map_map g f

theorem map_list_prod (L : List (Polynomial R)) : L.prod.map f = (L.map$ map f).Prod :=
  Eq.symm$ List.prod_hom _ (map_ring_hom f).toMonoidHom

@[simp]
theorem map_pow (n : ℕ) : (p ^ n).map f = p.map f ^ n :=
  (map_ring_hom f).map_pow _ _

theorem mem_map_srange {p : Polynomial S} : p ∈ (map_ring_hom f).srange ↔ ∀ n, p.coeff n ∈ f.srange :=
  by 
    split 
    ·
      rintro ⟨p, rfl⟩ n 
      rw [coe_map_ring_hom, coeff_map]
      exact Set.mem_range_self _
    ·
      intro h 
      rw [p.as_sum_range_C_mul_X_pow]
      refine' (map_ring_hom f).srange.sum_mem _ 
      intro i hi 
      rcases h i with ⟨c, hc⟩
      use C c*X ^ i 
      rw [coe_map_ring_hom, map_mul, map_C, hc, map_pow, map_X]

theorem mem_map_range {R S : Type _} [Ringₓ R] [Ringₓ S] (f : R →+* S) {p : Polynomial S} :
  p ∈ (map_ring_hom f).range ↔ ∀ n, p.coeff n ∈ f.range :=
  mem_map_srange f

theorem eval₂_map [Semiringₓ T] (g : S →+* T) (x : T) : (p.map f).eval₂ g x = p.eval₂ (g.comp f) x :=
  by 
    have A : nat_degree (p.map f) < p.nat_degree.succ := (nat_degree_map_le _ _).trans_lt (Nat.lt_succ_selfₓ _)
    convLHS => rw [eval₂_eq_sum]
    rw [sum_over_range' _ _ _ A]
    ·
      simp only [coeff_map, eval₂_eq_sum, sum_over_range, forall_const, zero_mul, RingHom.map_zero, Function.comp_app,
        RingHom.coe_comp]
    ·
      simp only [forall_const, zero_mul, RingHom.map_zero]

theorem eval_map (x : S) : (p.map f).eval x = p.eval₂ f x :=
  eval₂_map f (RingHom.id _) x

theorem map_sum {ι : Type _} (g : ι → Polynomial R) (s : Finset ι) : (∑i in s, g i).map f = ∑i in s, (g i).map f :=
  (map_ring_hom f).map_sum _ _

-- error in Data.Polynomial.Eval: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_comp (p q : polynomial R) : «expr = »(map f (p.comp q), (map f p).comp (map f q)) :=
polynomial.induction_on p (by simp [] [] ["only"] ["[", expr map_C, ",", expr forall_const, ",", expr C_comp, ",", expr eq_self_iff_true, "]"] [] []) (by simp [] [] ["only"] ["[", expr map_add, ",", expr add_comp, ",", expr forall_const, ",", expr implies_true_iff, ",", expr eq_self_iff_true, "]"] [] [] { contextual := tt }) (by simp [] [] ["only"] ["[", expr pow_succ', ",", "<-", expr mul_assoc, ",", expr comp, ",", expr forall_const, ",", expr eval₂_mul_X, ",", expr implies_true_iff, ",", expr eq_self_iff_true, ",", expr map_X, ",", expr map_mul, "]"] [] [] { contextual := tt })

@[simp]
theorem eval_zero_map (f : R →+* S) (p : Polynomial R) : (p.map f).eval 0 = f (p.eval 0) :=
  by 
    simp [←coeff_zero_eq_eval_zero]

@[simp]
theorem eval_one_map (f : R →+* S) (p : Polynomial R) : (p.map f).eval 1 = f (p.eval 1) :=
  by 
    apply Polynomial.induction_on' p
    ·
      intro p q hp hq 
      simp only [hp, hq, map_add, RingHom.map_add, eval_add]
    ·
      intro n r 
      simp only [one_pow, mul_oneₓ, eval_monomial, map_monomial]

@[simp]
theorem eval_nat_cast_map (f : R →+* S) (p : Polynomial R) (n : ℕ) : (p.map f).eval n = f (p.eval n) :=
  by 
    apply Polynomial.induction_on' p
    ·
      intro p q hp hq 
      simp only [hp, hq, map_add, RingHom.map_add, eval_add]
    ·
      intro n r 
      simp only [f.map_nat_cast, eval_monomial, map_monomial, f.map_pow, f.map_mul]

@[simp]
theorem eval_int_cast_map {R S : Type _} [Ringₓ R] [Ringₓ S] (f : R →+* S) (p : Polynomial R) (i : ℤ) :
  (p.map f).eval i = f (p.eval i) :=
  by 
    apply Polynomial.induction_on' p
    ·
      intro p q hp hq 
      simp only [hp, hq, map_add, RingHom.map_add, eval_add]
    ·
      intro n r 
      simp only [f.map_int_cast, eval_monomial, map_monomial, f.map_pow, f.map_mul]

end Map

/-!
After having set up the basic theory of `eval₂`, `eval`, `comp`, and `map`,
we make `eval₂` irreducible.

Perhaps we can make the others irreducible too?
-/


attribute [irreducible] Polynomial.eval₂

section HomEval₂

variable[CommSemiringₓ S][CommSemiringₓ T]

variable(f : R →+* S)(g : S →+* T)(p)

theorem hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.comp f) (g x) :=
  by 
    apply Polynomial.induction_on p <;> clear p
    ·
      simp only [forall_const, eq_self_iff_true, eval₂_C, RingHom.coe_comp]
    ·
      intro p q hp hq 
      simp only [hp, hq, eval₂_add, g.map_add]
    ·
      intro n a ih 
      simpa only [eval₂_mul, eval₂_C, eval₂_X_pow, g.map_mul, g.map_pow]

end HomEval₂

end Semiringₓ

section CommSemiringₓ

section Eval

variable[CommSemiringₓ R]{p q : Polynomial R}{x : R}

theorem eval₂_comp [CommSemiringₓ S] (f : R →+* S) {x : S} : eval₂ f x (p.comp q) = eval₂ f (eval₂ f x q) p :=
  by 
    rw [comp, p.as_sum_range] <;> simp [eval₂_finset_sum, eval₂_pow]

@[simp]
theorem eval_mul : (p*q).eval x = p.eval x*q.eval x :=
  eval₂_mul _ _

/-- `eval r`, regarded as a ring homomorphism from `polynomial R` to `R`. -/
def eval_ring_hom : R → Polynomial R →+* R :=
  eval₂_ring_hom (RingHom.id _)

@[simp]
theorem coe_eval_ring_hom (r : R) : (eval_ring_hom r : Polynomial R → R) = eval r :=
  rfl

@[simp]
theorem eval_pow (n : ℕ) : (p ^ n).eval x = p.eval x ^ n :=
  eval₂_pow _ _ _

@[simp]
theorem eval_comp : (p.comp q).eval x = p.eval (q.eval x) :=
  by 
    apply Polynomial.induction_on' p
    ·
      intro r s hr hs 
      simp [add_comp, hr, hs]
    ·
      intro n a 
      simp 

/-- `comp p`, regarded as a ring homomorphism from `polynomial R` to itself. -/
def comp_ring_hom : Polynomial R → Polynomial R →+* Polynomial R :=
  eval₂_ring_hom C

theorem eval₂_hom [CommSemiringₓ S] (f : R →+* S) (x : R) : p.eval₂ f (f x) = f (p.eval x) :=
  RingHom.comp_id f ▸ (hom_eval₂ p (RingHom.id R) f x).symm

theorem root_mul_left_of_is_root (p : Polynomial R) {q : Polynomial R} : is_root q a → is_root (p*q) a :=
  fun H =>
    by 
      rw [is_root, eval_mul, is_root.def.1 H, mul_zero]

theorem root_mul_right_of_is_root {p : Polynomial R} (q : Polynomial R) : is_root p a → is_root (p*q) a :=
  fun H =>
    by 
      rw [is_root, eval_mul, is_root.def.1 H, zero_mul]

/--
Polynomial evaluation commutes with finset.prod
-/
theorem eval_prod {ι : Type _} (s : Finset ι) (p : ι → Polynomial R) (x : R) :
  eval x (∏j in s, p j) = ∏j in s, eval x (p j) :=
  by 
    classical 
    apply Finset.induction_on s
    ·
      simp only [Finset.prod_empty, eval_one]
    ·
      intro j s hj hpj 
      have h0 : (∏i in insert j s, eval x (p i)) = eval x (p j)*∏i in s, eval x (p i)
      ·
        apply Finset.prod_insert hj 
      rw [h0, ←hpj, Finset.prod_insert hj, eval_mul]

end Eval

section Map

variable[CommSemiringₓ R][CommSemiringₓ S](f : R →+* S)

theorem map_multiset_prod (m : Multiset (Polynomial R)) : m.prod.map f = (m.map$ map f).Prod :=
  Eq.symm$ Multiset.prod_hom _ (map_ring_hom f).toMonoidHom

theorem map_prod {ι : Type _} (g : ι → Polynomial R) (s : Finset ι) : (∏i in s, g i).map f = ∏i in s, (g i).map f :=
  (map_ring_hom f).map_prod _ _

theorem support_map_subset (p : Polynomial R) : (map f p).Support ⊆ p.support :=
  by 
    intro x 
    simp only [mem_support_iff]
    contrapose! 
    rw [coeff_map]
    intro hx 
    rw [hx]
    exact RingHom.map_zero f

end Map

end CommSemiringₓ

section Ringₓ

variable[Ringₓ R]{p q r : Polynomial R}

theorem C_neg : C (-a) = -C a :=
  RingHom.map_neg C a

theorem C_sub : C (a - b) = C a - C b :=
  RingHom.map_sub C a b

@[simp]
theorem map_sub {S} [Ringₓ S] (f : R →+* S) : (p - q).map f = p.map f - q.map f :=
  (map_ring_hom f).map_sub p q

@[simp]
theorem map_neg {S} [Ringₓ S] (f : R →+* S) : (-p).map f = -p.map f :=
  (map_ring_hom f).map_neg p

@[simp]
theorem map_int_cast {S} [Ringₓ S] (f : R →+* S) (n : ℤ) : map f («expr↑ » n) = «expr↑ » n :=
  (map_ring_hom f).map_int_cast n

@[simp]
theorem eval_int_cast {n : ℤ} {x : R} : (n : Polynomial R).eval x = n :=
  by 
    simp only [←C_eq_int_cast, eval_C]

@[simp]
theorem eval₂_neg {S} [Ringₓ S] (f : R →+* S) {x : S} : (-p).eval₂ f x = -p.eval₂ f x :=
  by 
    rw [eq_neg_iff_add_eq_zero, ←eval₂_add, add_left_negₓ, eval₂_zero]

@[simp]
theorem eval₂_sub {S} [Ringₓ S] (f : R →+* S) {x : S} : (p - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x :=
  by 
    rw [sub_eq_add_neg, eval₂_add, eval₂_neg, sub_eq_add_neg]

@[simp]
theorem eval_neg (p : Polynomial R) (x : R) : (-p).eval x = -p.eval x :=
  eval₂_neg _

@[simp]
theorem eval_sub (p q : Polynomial R) (x : R) : (p - q).eval x = p.eval x - q.eval x :=
  eval₂_sub _

theorem root_X_sub_C : is_root (X - C a) b ↔ a = b :=
  by 
    rw [is_root.def, eval_sub, eval_X, eval_C, sub_eq_zero, eq_comm]

@[simp]
theorem neg_comp : (-p).comp q = -p.comp q :=
  eval₂_neg _

@[simp]
theorem sub_comp : (p - q).comp r = p.comp r - q.comp r :=
  eval₂_sub _

@[simp]
theorem cast_int_comp (i : ℤ) : comp (i : Polynomial R) p = i :=
  by 
    cases i <;> simp 

end Ringₓ

end Polynomial

