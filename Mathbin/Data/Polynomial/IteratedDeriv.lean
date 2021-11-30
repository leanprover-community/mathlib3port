import Mathbin.Data.Nat.Interval 
import Mathbin.Data.Polynomial.Derivative 
import Mathbin.Tactic.Linarith.Default

/-!
# Theory of iterated derivative
We define and prove some lemmas about iterated (formal) derivative for polynomials over a semiring.
-/


noncomputable theory

open Finset Nat Polynomial

open_locale BigOperators

namespace Polynomial

universe u

variable {R : Type u}

section Semiringₓ

variable [Semiringₓ R] (r : R) (f p q : Polynomial R) (n k : ℕ)

/-- `iterated_deriv f n` is the `n`-th formal derivative of the polynomial `f` -/
def iterated_deriv : Polynomial R :=
  (derivative^[n]) f

@[simp]
theorem iterated_deriv_zero_right : iterated_deriv f 0 = f :=
  rfl

theorem iterated_deriv_succ : iterated_deriv f (n+1) = (iterated_deriv f n).derivative :=
  by 
    rw [iterated_deriv, iterated_deriv, Function.iterate_succ']

@[simp]
theorem iterated_deriv_zero_left : iterated_deriv (0 : Polynomial R) n = 0 :=
  by 
    induction' n with n hn
    ·
      exact iterated_deriv_zero_right _
    ·
      rw [iterated_deriv_succ, hn, derivative_zero]

@[simp]
theorem iterated_deriv_add : iterated_deriv (p+q) n = iterated_deriv p n+iterated_deriv q n :=
  by 
    induction' n with n ih
    ·
      simp only [iterated_deriv_zero_right]
    ·
      simp only [iterated_deriv_succ, ih, derivative_add]

@[simp]
theorem iterated_deriv_smul : iterated_deriv (r • p) n = r • iterated_deriv p n :=
  by 
    induction' n with n ih
    ·
      simp only [iterated_deriv_zero_right]
    ·
      simp only [iterated_deriv_succ, ih, derivative_smul]

@[simp]
theorem iterated_deriv_X_zero : iterated_deriv (X : Polynomial R) 0 = X :=
  by 
    simp only [iterated_deriv_zero_right]

@[simp]
theorem iterated_deriv_X_one : iterated_deriv (X : Polynomial R) 1 = 1 :=
  by 
    simp only [iterated_deriv, derivative_X, Function.iterate_one]

@[simp]
theorem iterated_deriv_X (h : 1 < n) : iterated_deriv (X : Polynomial R) n = 0 :=
  by 
    induction' n with n ih
    ·
      exfalso 
      exact Nat.not_lt_zeroₓ 1 h
    ·
      simp only [iterated_deriv_succ]
      byCases' H : n = 1
      ·
        rw [H]
        simp only [iterated_deriv_X_one, derivative_one]
      ·
        replace h : 1 < n := Arrayₓ.push_back_idx h (Ne.symm H)
        rw [ih h]
        simp only [derivative_zero]

@[simp]
theorem iterated_deriv_C_zero : iterated_deriv (C r) 0 = C r :=
  by 
    simp only [iterated_deriv_zero_right]

@[simp]
theorem iterated_deriv_C (h : 0 < n) : iterated_deriv (C r) n = 0 :=
  by 
    induction' n with n ih
    ·
      exfalso 
      exact Nat.lt_asymmₓ h h
    ·
      byCases' H : n = 0
      ·
        rw [iterated_deriv_succ, H]
        simp only [iterated_deriv_C_zero, derivative_C]
      ·
        replace h : 0 < n := Nat.pos_of_ne_zeroₓ H 
        rw [iterated_deriv_succ, ih h]
        simp only [derivative_zero]

@[simp]
theorem iterated_deriv_one_zero : iterated_deriv (1 : Polynomial R) 0 = 1 :=
  by 
    simp only [iterated_deriv_zero_right]

-- error in Data.Polynomial.IteratedDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem iterated_deriv_one : «expr < »(0, n) → «expr = »(iterated_deriv (1 : polynomial R) n, 0) :=
λ h, begin
  have [ident eq1] [":", expr «expr = »((1 : polynomial R), C 1)] [":=", expr by simp [] [] ["only"] ["[", expr ring_hom.map_one, "]"] [] []],
  rw [expr eq1] [],
  exact [expr iterated_deriv_C _ _ h]
end

end Semiringₓ

section Ringₓ

variable [Ringₓ R] (p q : Polynomial R) (n : ℕ)

@[simp]
theorem iterated_deriv_neg : iterated_deriv (-p) n = -iterated_deriv p n :=
  by 
    induction' n with n ih
    ·
      simp only [iterated_deriv_zero_right]
    ·
      simp only [iterated_deriv_succ, ih, derivative_neg]

@[simp]
theorem iterated_deriv_sub : iterated_deriv (p - q) n = iterated_deriv p n - iterated_deriv q n :=
  by 
    rw [sub_eq_add_neg, iterated_deriv_add, iterated_deriv_neg, ←sub_eq_add_neg]

end Ringₓ

section CommSemiringₓ

variable [CommSemiringₓ R]

variable (f p q : Polynomial R) (n k : ℕ)

-- error in Data.Polynomial.IteratedDeriv: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem coeff_iterated_deriv_as_prod_Ico : ∀
m : exprℕ(), «expr = »((iterated_deriv f k).coeff m, «expr * »(«expr∏ in , »((i), Ico m.succ «expr + »(m, k.succ), i), f.coeff «expr + »(m, k))) :=
begin
  induction [expr k] [] ["with", ident k, ident ih] [],
  { simp [] [] ["only"] ["[", expr add_zero, ",", expr forall_const, ",", expr one_mul, ",", expr Ico_self, ",", expr eq_self_iff_true, ",", expr iterated_deriv_zero_right, ",", expr prod_empty, "]"] [] [] },
  { intro [ident m],
    rw ["[", expr iterated_deriv_succ, ",", expr coeff_derivative, ",", expr ih «expr + »(m, 1), ",", expr mul_right_comm, "]"] [],
    apply [expr congr_arg2],
    { have [ident set_eq] [":", expr «expr = »(Ico m.succ «expr + »(m, k.succ.succ), «expr ∪ »(Ico «expr + »(m, 1).succ «expr + »(«expr + »(m, 1), k.succ), {«expr + »(m, 1)}))] [],
      { rw ["[", expr union_comm, ",", "<-", expr insert_eq, ",", expr Ico_insert_succ_left, ",", expr add_succ, ",", expr add_succ, ",", expr add_succ _ k, ",", "<-", expr succ_eq_add_one, ",", expr succ_add, "]"] [],
        rw [expr succ_eq_add_one] [],
        linarith [] [] [] },
      rw ["[", expr set_eq, ",", expr prod_union, "]"] [],
      apply [expr congr_arg2],
      { refl },
      { simp [] [] ["only"] ["[", expr prod_singleton, "]"] [] [],
        norm_cast [] },
      { rw ["[", expr disjoint_singleton_right, ",", expr mem_Ico, "]"] [],
        exact [expr λ h, (nat.lt_succ_self _).not_le h.1] } },
    { exact [expr congr_arg _ (succ_add m k)] } }
end

theorem coeff_iterated_deriv_as_prod_range :
  ∀ m : ℕ, (iterated_deriv f k).coeff m = f.coeff (m+k)*∏i in range k, «expr↑ » ((m+k) - i) :=
  by 
    induction' k with k ih
    ·
      simp 
    intro m 
    calc (f.iterated_deriv k.succ).coeff m = (f.coeff (m+k.succ)*∏i in range k, «expr↑ » ((m+k.succ) - i))*m+1 :=
      by 
        rw [iterated_deriv_succ, coeff_derivative, ih m.succ, succ_add,
          add_succ]_ = (f.coeff (m+k.succ)*∏i in range k, «expr↑ » ((m+k.succ) - i))*«expr↑ » (m+1) :=
      by 
        pushCast _ = f.coeff (m+k.succ)*∏i in range k.succ, «expr↑ » ((m+k.succ) - i) :=
      by 
        rw [prod_range_succ, add_tsub_assoc_of_le k.le_succ, succ_sub le_rfl, tsub_self, mul_assocₓ]

theorem iterated_deriv_eq_zero_of_nat_degree_lt (h : f.nat_degree < n) : iterated_deriv f n = 0 :=
  by 
    ext m 
    rw [coeff_iterated_deriv_as_prod_range, coeff_zero, coeff_eq_zero_of_nat_degree_lt, zero_mul]
    linarith

theorem iterated_deriv_mul :
  iterated_deriv (p*q) n = ∑k in range n.succ, (C (n.choose k : R)*iterated_deriv p (n - k))*iterated_deriv q k :=
  by 
    induction' n with n IH
    ·
      simp 
    calc
      (p*q).iteratedDeriv n.succ =
        (∑k : ℕ in range n.succ, (C («expr↑ » (n.choose k))*p.iterated_deriv (n - k))*q.iterated_deriv k).derivative :=
      by 
        rw [iterated_deriv_succ,
          IH]_ =
        (∑k : ℕ in range n.succ,
            (C
                  («expr↑ »
                    (n.choose
                      k))*p.iterated_deriv
                  ((n -
                      k)+1))*q.iterated_deriv
                k)+∑k : ℕ in range n.succ,
            (C («expr↑ » (n.choose k))*p.iterated_deriv (n - k))*q.iterated_deriv (k+1) :=
      by 
        simpRw [derivative_sum, derivative_mul, derivative_C, zero_mul, zero_addₓ, iterated_deriv_succ,
          sum_add_distrib]_ =
        ((∑k : ℕ in range n.succ,
              (C
                    («expr↑ »
                      (n.choose
                        k.succ))*p.iterated_deriv
                    (n -
                      k))*q.iterated_deriv
                  (k+1))+(C
                  («expr↑ »
                    1)*p.iterated_deriv
                  n.succ)*q.iterated_deriv
                0)+∑k : ℕ in range n.succ,
            (C («expr↑ » (n.choose k))*p.iterated_deriv (n - k))*q.iterated_deriv (k+1) :=
      _
        _ =
        ((∑k : ℕ in range n.succ,
              (C
                    («expr↑ »
                      (n.choose
                        k))*p.iterated_deriv
                    (n -
                      k))*q.iterated_deriv
                  (k+1))+∑k : ℕ in range n.succ,
              (C
                    («expr↑ »
                      (n.choose
                        k.succ))*p.iterated_deriv
                    (n - k))*q.iterated_deriv (k+1))+(C («expr↑ » 1)*p.iterated_deriv n.succ)*q.iterated_deriv 0 :=
      by 
        ring
          _ =
        (∑i : ℕ in range n.succ,
            (C
                  («expr↑ »
                    ((n+1).choose
                      (i+1)))*p.iterated_deriv
                  ((n+1) - i+1))*q.iterated_deriv (i+1))+(C («expr↑ » 1)*p.iterated_deriv n.succ)*q.iterated_deriv 0 :=
      by 
        simpRw [choose_succ_succ, succ_sub_succ, cast_add, C.map_add, add_mulₓ,
          sum_add_distrib]_ =
        ∑k : ℕ in range n.succ.succ,
          (C («expr↑ » (n.succ.choose k))*p.iterated_deriv (n.succ - k))*q.iterated_deriv k :=
      by 
        rw [sum_range_succ' _ n.succ, choose_zero_right, tsub_zero]
    congr 
    refine' (sum_range_succ' _ _).trans (congr_arg2ₓ (·+·) _ _)
    ·
      rw [sum_range_succ, Nat.choose_succ_self, cast_zero, C.map_zero, zero_mul, zero_mul, add_zeroₓ]
      refine' sum_congr rfl fun k hk => _ 
      rw [mem_range] at hk 
      congr 
      rw [tsub_add_eq_add_tsub (Nat.succ_le_of_ltₓ hk), Nat.succ_sub_succ]
    ·
      rw [choose_zero_right, tsub_zero]

end CommSemiringₓ

end Polynomial

