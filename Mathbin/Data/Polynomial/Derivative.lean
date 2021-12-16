import Mathbin.Algebra.IterateHom 
import Mathbin.Data.Polynomial.Eval

/-!
# The derivative map on polynomials

## Main definitions
 * `polynomial.derivative`: The formal derivative of polynomials, expressed as a linear map.

-/


noncomputable section 

open Finset

open_locale BigOperators Classical

namespace Polynomial

universe u v w y z

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

section Derivative

section Semiringₓ

variable [Semiringₓ R]

/-- `derivative p` is the formal derivative of the polynomial `p` -/
def derivative : Polynomial R →ₗ[R] Polynomial R :=
  { toFun := fun p => p.sum fun n a => C (a*n)*X ^ (n - 1),
    map_add' :=
      fun p q =>
        by 
          rw [sum_add_index] <;>
            simp only [add_mulₓ, forall_const, RingHom.map_add, eq_self_iff_true, zero_mul, RingHom.map_zero],
    map_smul' :=
      fun a p =>
        by 
          dsimp <;>
            rw [sum_smul_index] <;>
              simp only [mul_sum, ←C_mul', mul_assocₓ, coeff_C_mul, RingHom.map_mul, forall_const, zero_mul,
                RingHom.map_zero, Sum] }

theorem derivative_apply (p : Polynomial R) : derivative p = p.sum fun n a => C (a*n)*X ^ (n - 1) :=
  rfl

theorem coeff_derivative (p : Polynomial R) (n : ℕ) : coeff (derivative p) n = coeff p (n+1)*n+1 :=
  by 
    rw [derivative_apply]
    simp only [coeff_X_pow, coeff_sum, coeff_C_mul]
    rw [Sum, Finset.sum_eq_single (n+1)]
    simp only [Nat.add_succ_sub_one, add_zeroₓ, mul_oneₓ, if_true, eq_self_iff_true]
    normCast
    ·
      intro b 
      cases b
      ·
        intros 
        rw [Nat.cast_zero, mul_zero, zero_mul]
      ·
        intro _ H 
        rw [Nat.succ_sub_one b, if_neg (mt (congr_argₓ Nat.succ) H.symm), mul_zero]
    ·
      rw [if_pos (add_tsub_cancel_right n 1).symm, mul_oneₓ, Nat.cast_add, Nat.cast_one, mem_support_iff]
      intro h 
      pushNeg  at h 
      simp [h]

@[simp]
theorem derivative_zero : derivative (0 : Polynomial R) = 0 :=
  derivative.map_zero

@[simp]
theorem iterate_derivative_zero {k : ℕ} : (derivative^[k]) (0 : Polynomial R) = 0 :=
  by 
    induction' k with k ih
    ·
      simp 
    ·
      simp [ih]

@[simp]
theorem derivative_monomial (a : R) (n : ℕ) : derivative (monomial n a) = monomial (n - 1) (a*n) :=
  by 
    rw [derivative_apply, sum_monomial_index, C_mul_X_pow_eq_monomial]
    simp 

theorem derivative_C_mul_X_pow (a : R) (n : ℕ) : derivative (C a*X ^ n) = C (a*n)*X ^ (n - 1) :=
  by 
    rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, derivative_monomial]

@[simp]
theorem derivative_X_pow (n : ℕ) : derivative (X ^ n : Polynomial R) = (n : Polynomial R)*X ^ (n - 1) :=
  by 
    convert derivative_C_mul_X_pow (1 : R) n <;> simp 

@[simp]
theorem derivative_C {a : R} : derivative (C a) = 0 :=
  by 
    simp [derivative_apply]

@[simp]
theorem derivative_X : derivative (X : Polynomial R) = 1 :=
  (derivative_monomial _ _).trans$
    by 
      simp 

@[simp]
theorem derivative_one : derivative (1 : Polynomial R) = 0 :=
  derivative_C

@[simp]
theorem derivative_bit0 {a : Polynomial R} : derivative (bit0 a) = bit0 (derivative a) :=
  by 
    simp [bit0]

@[simp]
theorem derivative_bit1 {a : Polynomial R} : derivative (bit1 a) = bit0 (derivative a) :=
  by 
    simp [bit1]

@[simp]
theorem derivative_add {f g : Polynomial R} : derivative (f+g) = derivative f+derivative g :=
  derivative.map_add f g

@[simp]
theorem iterate_derivative_add {f g : Polynomial R} {k : ℕ} :
  (derivative^[k]) (f+g) = (derivative^[k]) f+(derivative^[k]) g :=
  derivative.toAddMonoidHom.iterate_map_add _ _ _

@[simp]
theorem derivative_neg {R : Type _} [Ringₓ R] (f : Polynomial R) : derivative (-f) = -derivative f :=
  LinearMap.map_neg derivative f

@[simp]
theorem iterate_derivative_neg {R : Type _} [Ringₓ R] {f : Polynomial R} {k : ℕ} :
  (derivative^[k]) (-f) = -(derivative^[k]) f :=
  (@derivative R _).toAddMonoidHom.iterate_map_neg _ _

@[simp]
theorem derivative_sub {R : Type _} [Ringₓ R] {f g : Polynomial R} : derivative (f - g) = derivative f - derivative g :=
  LinearMap.map_sub derivative f g

@[simp]
theorem iterate_derivative_sub {R : Type _} [Ringₓ R] {k : ℕ} {f g : Polynomial R} :
  (derivative^[k]) (f - g) = (derivative^[k]) f - (derivative^[k]) g :=
  by 
    induction' k with k ih generalizing f g
    ·
      simp [Nat.iterate]
    ·
      simp [Nat.iterate, ih]

@[simp]
theorem derivative_sum {s : Finset ι} {f : ι → Polynomial R} :
  derivative (∑ b in s, f b) = ∑ b in s, derivative (f b) :=
  derivative.map_sum

@[simp]
theorem derivative_smul (r : R) (p : Polynomial R) : derivative (r • p) = r • derivative p :=
  derivative.map_smul _ _

@[simp]
theorem iterate_derivative_smul (r : R) (p : Polynomial R) (k : ℕ) :
  (derivative^[k]) (r • p) = r • (derivative^[k]) p :=
  by 
    induction' k with k ih generalizing p
    ·
      simp 
    ·
      simp [ih]

/-- We can't use `derivative_mul` here because
we want to prove this statement also for noncommutative rings.-/
@[simp]
theorem derivative_C_mul (a : R) (p : Polynomial R) : derivative (C a*p) = C a*derivative p :=
  by 
    convert derivative_smul a p <;> apply C_mul'

@[simp]
theorem iterate_derivative_C_mul (a : R) (p : Polynomial R) (k : ℕ) :
  (derivative^[k]) (C a*p) = C a*(derivative^[k]) p :=
  by 
    convert iterate_derivative_smul a p k <;> apply C_mul'

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R]

theorem derivative_eval (p : Polynomial R) (x : R) : p.derivative.eval x = p.sum fun n a => (a*n)*x ^ (n - 1) :=
  by 
    simp only [derivative_apply, eval_sum, eval_pow, eval_C, eval_X, eval_nat_cast, eval_mul]

@[simp]
theorem derivative_mul {f g : Polynomial R} : derivative (f*g) = (derivative f*g)+f*derivative g :=
  calc derivative (f*g) = f.sum fun n a => g.sum fun m b => C ((a*b)*(n+m : ℕ))*X ^ ((n+m) - 1) :=
    by 
      rw [mul_eq_sum_sum]
      trans 
      exact derivative_sum 
      trans
      ·
        apply Finset.sum_congr rfl 
        intro x hx 
        exact derivative_sum 
      apply Finset.sum_congr rfl 
      intro n hn 
      apply Finset.sum_congr rfl 
      intro m hm 
      trans
      ·
        apply congr_argₓ 
        exact monomial_eq_C_mul_X 
      exact derivative_C_mul_X_pow _ _ 
    _ = f.sum fun n a => g.sum fun m b => ((C (a*n)*X ^ (n - 1))*C b*X ^ m)+(C a*X ^ n)*C (b*m)*X ^ (m - 1) :=
    sum_congr rfl$
      fun n hn =>
        sum_congr rfl$
          fun m hm =>
            by 
              simp only [Nat.cast_add, mul_addₓ, add_mulₓ, C_add, C_mul] <;>
                cases n <;>
                  simp only [Nat.succ_sub_succ, pow_zeroₓ] <;>
                    cases m <;>
                      simp only [Nat.cast_zero, C_0, Nat.succ_sub_succ, zero_mul, mul_zero, Nat.add_succ, tsub_zero,
                        pow_zeroₓ, pow_addₓ, one_mulₓ, pow_succₓ, mul_commₓ, mul_left_commₓ]
    _ = (derivative f*g)+f*derivative g :=
    by 
      conv  => rhs congr·rw [←sum_C_mul_X_eq g]·rw [←sum_C_mul_X_eq f]
      simp only [Sum, sum_add_distrib, Finset.mul_sum, Finset.sum_mul, derivative_apply]
    

theorem derivative_pow_succ (p : Polynomial R) (n : ℕ) : (p ^ n+1).derivative = ((n+1)*p ^ n)*p.derivative :=
  Nat.recOn n
      (by 
        rw [pow_oneₓ, Nat.cast_zero, zero_addₓ, one_mulₓ, pow_zeroₓ, one_mulₓ])$
    fun n ih =>
      by 
        rw [pow_succ'ₓ, derivative_mul, ih, mul_right_commₓ, ←add_mulₓ, add_mulₓ (n.succ : Polynomial R), one_mulₓ,
          pow_succ'ₓ, mul_assocₓ, n.cast_succ]

theorem derivative_pow (p : Polynomial R) (n : ℕ) : (p ^ n).derivative = (n*p ^ (n - 1))*p.derivative :=
  Nat.casesOn n
      (by 
        rw [pow_zeroₓ, derivative_one, Nat.cast_zero, zero_mul, zero_mul])$
    fun n =>
      by 
        rw [p.derivative_pow_succ n, n.succ_sub_one, n.cast_succ]

theorem derivative_comp (p q : Polynomial R) : (p.comp q).derivative = q.derivative*p.derivative.comp q :=
  by 
    apply Polynomial.induction_on' p
    ·
      intro p₁ p₂ h₁ h₂ 
      simp [h₁, h₂, mul_addₓ]
    ·
      intro n r 
      simp only [derivative_pow, derivative_mul, monomial_comp, derivative_monomial, derivative_C, zero_mul,
        C_eq_nat_cast, zero_addₓ, RingHom.map_mul]
      rw [mul_commₓ (derivative q)]
      simp only [mul_assocₓ]

@[simp]
theorem derivative_map [CommSemiringₓ S] (p : Polynomial R) (f : R →+* S) : (p.map f).derivative = p.derivative.map f :=
  Polynomial.induction_on p
    (fun r =>
      by 
        rw [map_C, derivative_C, derivative_C, map_zero])
    (fun p q ihp ihq =>
      by 
        rw [map_add, derivative_add, ihp, ihq, derivative_add, map_add])
    fun n r ih =>
      by 
        rw [map_mul, map_C, Polynomial.map_pow, map_X, derivative_mul, derivative_pow_succ, derivative_C, zero_mul,
          zero_addₓ, derivative_X, mul_oneₓ, derivative_mul, derivative_pow_succ, derivative_C, zero_mul, zero_addₓ,
          derivative_X, mul_oneₓ, map_mul, map_C, map_mul, Polynomial.map_pow, map_add, map_nat_cast, map_one, map_X]

@[simp]
theorem iterate_derivative_map [CommSemiringₓ S] (p : Polynomial R) (f : R →+* S) (k : ℕ) :
  (Polynomial.derivative^[k]) (p.map f) = ((Polynomial.derivative^[k]) p).map f :=
  by 
    induction' k with k ih generalizing p
    ·
      simp 
    ·
      simp [ih]

/-- Chain rule for formal derivative of polynomials. -/
theorem derivative_eval₂_C (p q : Polynomial R) : (p.eval₂ C q).derivative = p.derivative.eval₂ C q*q.derivative :=
  Polynomial.induction_on p
    (fun r =>
      by 
        rw [eval₂_C, derivative_C, eval₂_zero, zero_mul])
    (fun p₁ p₂ ih₁ ih₂ =>
      by 
        rw [eval₂_add, derivative_add, ih₁, ih₂, derivative_add, eval₂_add, add_mulₓ])
    fun n r ih =>
      by 
        rw [pow_succ'ₓ, ←mul_assocₓ, eval₂_mul, eval₂_X, derivative_mul, ih, @derivative_mul _ _ _ X, derivative_X,
          mul_oneₓ, eval₂_add, @eval₂_mul _ _ _ _ X, eval₂_X, add_mulₓ, mul_right_commₓ]

theorem derivative_prod {s : Multiset ι} {f : ι → Polynomial R} :
  (Multiset.map f s).Prod.derivative =
    (Multiset.map (fun i => (Multiset.map f (s.erase i)).Prod*(f i).derivative) s).Sum :=
  by 
    refine'
      Multiset.induction_on s
        (by 
          simp )
        fun i s h => _ 
    rw [Multiset.map_cons, Multiset.prod_cons, derivative_mul, Multiset.map_cons _ i s, Multiset.sum_cons,
      Multiset.erase_cons_head, mul_commₓ (f i).derivative]
    congr 
    rw [h, ←AddMonoidHom.coe_mul_left, (AddMonoidHom.mulLeft (f i)).map_multiset_sum _, AddMonoidHom.coe_mul_left]
    simp only [Function.comp_app, Multiset.map_map]
    congr 1
    refine' Multiset.map_congr fun j hj => _ 
    simp only [Function.comp_app]
    rw [←mul_assocₓ, ←Multiset.prod_cons, ←Multiset.map_cons]
    congr 1
    byCases' hij : i = j
    ·
      simp [hij, ←Multiset.prod_cons, ←Multiset.map_cons, Multiset.cons_erase hj]
    ·
      simp [hij]

theorem of_mem_support_derivative {p : Polynomial R} {n : ℕ} (h : n ∈ p.derivative.support) : (n+1) ∈ p.support :=
  mem_support_iff.2$
    fun h1 : p.coeff (n+1) = 0 =>
      mem_support_iff.1 h$
        show p.derivative.coeff n = 0 by 
          rw [coeff_derivative, h1, zero_mul]

theorem degree_derivative_lt {p : Polynomial R} (hp : p ≠ 0) : p.derivative.degree < p.degree :=
  (Finset.sup_lt_iff$ bot_lt_iff_ne_bot.2$ mt degree_eq_bot.1 hp).2$
    fun n hp => lt_of_lt_of_leₓ (WithBot.some_lt_some.2 n.lt_succ_self)$ Finset.le_sup$ of_mem_support_derivative hp

theorem nat_degree_derivative_lt {p : Polynomial R} (hp : p.derivative ≠ 0) : p.derivative.nat_degree < p.nat_degree :=
  have hp1 : p ≠ 0 :=
    fun h =>
      hp$
        by 
          rw [h, derivative_zero]
  WithBot.some_lt_some.1$
    by 
      rw [nat_degree, Option.get_or_else_of_ne_none$ mt degree_eq_bot.1 hp, nat_degree,
        Option.get_or_else_of_ne_none$ mt degree_eq_bot.1 hp1]
      exact degree_derivative_lt hp1

theorem degree_derivative_le {p : Polynomial R} : p.derivative.degree ≤ p.degree :=
  if H : p = 0 then
    le_of_eqₓ$
      by 
        rw [H, derivative_zero]
  else le_of_ltₓ$ degree_derivative_lt H

/-- The formal derivative of polynomials, as linear homomorphism. -/
def derivative_lhom (R : Type _) [CommRingₓ R] : Polynomial R →ₗ[R] Polynomial R :=
  { toFun := derivative, map_add' := fun p q => derivative_add, map_smul' := fun r p => derivative_smul r p }

@[simp]
theorem derivative_lhom_coe {R : Type _} [CommRingₓ R] :
  (Polynomial.derivativeLhom R : Polynomial R → Polynomial R) = Polynomial.derivative :=
  rfl

@[simp]
theorem derivative_cast_nat {n : ℕ} : derivative (n : Polynomial R) = 0 :=
  by 
    rw [←C.map_nat_cast n]
    exact derivative_C

@[simp]
theorem iterate_derivative_cast_nat_mul {n k : ℕ} {f : Polynomial R} : (derivative^[k]) (n*f) = n*(derivative^[k]) f :=
  by 
    induction' k with k ih generalizing f
    ·
      simp [Nat.iterate]
    ·
      simp [Nat.iterate, ih]

end CommSemiringₓ

section CommRingₓ

variable [CommRingₓ R]

theorem derivative_comp_one_sub_X (p : Polynomial R) : (p.comp (1 - X)).derivative = -p.derivative.comp (1 - X) :=
  by 
    simp [derivative_comp]

@[simp]
theorem iterate_derivative_comp_one_sub_X (p : Polynomial R) (k : ℕ) :
  (derivative^[k]) (p.comp (1 - X)) = (-1 ^ k)*((derivative^[k]) p).comp (1 - X) :=
  by 
    induction' k with k ih generalizing p
    ·
      simp 
    ·
      simp [ih p.derivative, iterate_derivative_neg, derivative_comp, pow_succₓ]

theorem eval_multiset_prod_X_sub_C_derivative {S : Multiset R} {r : R} (hr : r ∈ S) :
  eval r (Multiset.map (fun a => X - C a) S).Prod.derivative = (Multiset.map (fun a => r - a) (S.erase r)).Prod :=
  by 
    nthRw 0[←Multiset.cons_erase hr]
    simpa using (eval_ring_hom r).map_multiset_prod (Multiset.map (fun a => X - C a) (S.erase r))

end CommRingₓ

section IsDomain

variable [Ringₓ R] [IsDomain R]

theorem mem_support_derivative [CharZero R] (p : Polynomial R) (n : ℕ) :
  n ∈ (derivative p).Support ↔ (n+1) ∈ p.support :=
  suffices ¬(coeff p (n+1) = 0 ∨ ((n+1 : ℕ) : R) = 0) ↔ coeff p (n+1) ≠ 0 by 
    simpa only [mem_support_iff, coeff_derivative, Ne.def, mul_eq_zero]
  by 
    rw [Nat.cast_eq_zero]
    simp only [Nat.succ_ne_zero, or_falseₓ]

@[simp]
theorem degree_derivative_eq [CharZero R] (p : Polynomial R) (hp : 0 < nat_degree p) :
  degree (derivative p) = (nat_degree p - 1 : ℕ) :=
  by 
    have h0 : p ≠ 0
    ·
      contrapose! hp 
      simp [hp]
    apply le_antisymmₓ
    ·
      rw [derivative_apply]
      apply le_transₓ (degree_sum_le _ _) (sup_le fun n hn => _)
      apply le_transₓ (degree_C_mul_X_pow_le _ _) (WithBot.coe_le_coe.2 (tsub_le_tsub_right _ _))
      apply le_nat_degree_of_mem_supp _ hn
    ·
      refine' le_sup _ 
      rw [mem_support_derivative, tsub_add_cancel_of_le, mem_support_iff]
      ·
        show ¬leading_coeff p = 0
        rw [leading_coeff_eq_zero]
        intro h 
        rw [h, nat_degree_zero] at hp 
        exact lt_irreflₓ 0 (lt_of_le_of_ltₓ (zero_le _) hp)
      exact hp

theorem nat_degree_eq_zero_of_derivative_eq_zero [CharZero R] {f : Polynomial R} (h : f.derivative = 0) :
  f.nat_degree = 0 :=
  by 
    byCases' hf : f = 0
    ·
      exact (congr_argₓ Polynomial.natDegree hf).trans rfl
    ·
      rw [nat_degree_eq_zero_iff_degree_le_zero]
      byContra absurd 
      have f_nat_degree_pos : 0 < f.nat_degree
      ·
        rwa [not_leₓ, ←nat_degree_pos_iff_degree_pos] at absurd 
      let m := f.nat_degree - 1
      have hm : (m+1) = f.nat_degree := tsub_add_cancel_of_le f_nat_degree_pos 
      have h2 := coeff_derivative f m 
      rw [Polynomial.ext_iff] at h 
      rw [h m, coeff_zero, zero_eq_mul] at h2 
      cases h2
      ·
        rw [hm, ←leading_coeff, leading_coeff_eq_zero] at h2 
        exact hf h2
      ·
        normCast  at h2

end IsDomain

end Derivative

end Polynomial

